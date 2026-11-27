"""Refreshes the Xcode release manifest, and the tags made from it.

  python refresh.py fetch [--apple-developer-downloads FILE]  # updates the snapshots in sources/
  python refresh.py manifest                                  # rebuilds the manifest from sources/
  python refresh.py tags [--push]                             # moves each version's tag to its release's latest data

Each source is kept in sources/<name>.json as a snapshot of what it last said,
in one shared format: "releases", each the part of a release the source knows,
in the format of releases/<build>.json, and "simulators", each a simulator
runtime, in the format of simulators.json. A snapshot is replaced only when
its source answers with something that looks right, so the manifest is always
built from the last good answer of every source, even when one is down.

The manifest is built from the snapshots alone:

- releases.json: every version, newest first, with its build, date and
  download URL.
- releases/<build>.json: one file per Xcode build, with the versions it was
  released as, its download, SDKs, the simulator runtime that matches each SDK,
  and the components it uses, such as the Metal Toolchain.
- simulators.json: every simulator runtime Apple offers, with what each one
  requires.

Where sources disagree, the one first in PRECEDENCE wins, field by field. A
download describes one file, so it comes whole from one source, and other
sources fill its gaps only when they name the same file. A source that does
not know builds, such as Apple's developer downloads, adds to the build that
has its versions. Simulators are matched to each release from its SDKs.

Each version is tagged "<version>+<build>", such as "27.2.0+27B52", with the
download URL as its message. Each build has its own line of commits holding
only release.json, its release's data, and its tags point at the newest one,
so "git show 27.2.0+27B52:release.json" shows the release and "git log
27.2.0+27B52" shows how it changed. Each version belongs to one build. A
version, once tagged, stays tagged, so versions that people pinned keep
working, unless the sources give it to another build: then the newer build
wins, and the old tag is deleted.
"""

import argparse
import datetime
import hashlib
import json
import os
import plistlib
import re
import subprocess
import sys
import time
import xml.etree.ElementTree as ElementTree
from collections import defaultdict
from email.utils import parsedate_to_datetime
from pathlib import Path

import requests

XCODE_RELEASES_URL = 'https://xcodereleases.com/data.json'
RELEASES_FEED_URL = 'https://developer.apple.com/news/releases/rss/releases.rss'
DOWNLOADABLES_INDEX_URL = 'https://devimages-cdn.apple.com/downloads/xcode/simulators/index2.dvtdownloadableindex'
RELEASE_NOTES_INDEX_URL = 'https://developer.apple.com/tutorials/data/documentation/xcode-release-notes.json'
OLD_RELEASE_NOTES_URL = 'https://developer.apple.com/library/archive/releasenotes/DeveloperTools/RN-Xcode/Chapters/Introduction.html'

# The sources, by precedence: where two give a field, the first one wins.
# - apple-developer-downloads: Apple's list of developer downloads, which
#   needs a signed-in Apple ID, as xcodes reads it with `--data-source apple`.
# - apple-releases-feed: Apple's developer releases feed.
# - apple-downloadables-index: Apple's downloadables index, which Xcode reads to
#   offer simulator runtimes and components.
# - apple-release-notes: Apple's index of Xcode release notes, one page for
#   each version from Xcode 10 on, rewritten with each of its betas.
# - xcodereleases: xcodereleases.com.
PRECEDENCE = ['apple-developer-downloads', 'apple-releases-feed', 'apple-downloadables-index', 'apple-release-notes',
              'xcodereleases']

# The feed covers only about the last six months, so its snapshot can shrink.
# The other sources only grow, so a snapshot that loses more than a tenth of
# its releases is taken for a broken answer.
ROLLING = {'apple-releases-feed'}

# Simulator platforms by their name in xcodereleases and `xcodebuild -downloadPlatform`,
# with the platform identifier and SDK name Apple's index uses for them.
PLATFORMS = {
    'iOS': ('com.apple.platform.iphoneos', 'iphoneos'),
    'tvOS': ('com.apple.platform.appletvos', 'appletvos'),
    'watchOS': ('com.apple.platform.watchos', 'watchos'),
    'visionOS': ('com.apple.platform.xros', 'xros'),
}
PLATFORM_NAMES = {identifier: name for name, (identifier, _) in PLATFORMS.items()}

# Components by their asset type in Apple's index, with their name in
# `xcodebuild -downloadComponent`.
COMPONENTS = {
    'metalToolchain': 'metalToolchain',
    'xcodeDeviceSupport': 'deviceSupport',
}

# The fields of releases/<build>.json, in order.
FIELDS = ['versions', 'build', 'date', 'sources', 'requires_macos', 'download', 'release_notes', 'compilers',
          'sdks', 'simulators', 'components']

# Releases before this are not tracked.
FIRST_VERSION = '8.0'

ROOT = Path(__file__).resolve().parent
SOURCES = ROOT / 'sources'
RELEASES = ROOT / 'releases'
SIMULATORS = ROOT / 'simulators.json'
INDEX = ROOT / 'releases.json'


def warn(message):
    print(message, file=sys.stderr)


def git(*arguments, env=None, input=None):
    return subprocess.run(
        ['git', *arguments], cwd=ROOT, check=True, capture_output=True, text=True, env=env, input=input
    ).stdout.strip()


def without_empty(values):
    return {key: value for key, value in values.items() if value not in (None, '', [], {})}


def version_key(version):
    return [int(part) if part.isdigit() else 0 for part in str(version).split('.')]


def semver_key(semver):
    """Orders versions such as "27.2.0-beta.2", "27.2.0-rc" and "27.2.0"."""
    number, _, pre_release = semver.partition('-')
    label, _, count = pre_release.partition('.')
    stage = {'beta': 0, 'gm-seed': 1, 'rc': 2}.get(label, 0) if pre_release else 3
    return version_key(number), stage, int(count or 1)


def semver_for(version):
    """Names a release the way its tag does, such as "27.3.0-beta.2", from an
    xcodereleases-style version."""
    number = version['number']
    dot_count = number.count('.')
    if dot_count == 2:
        semver = number
    elif dot_count == 1:
        semver = '%s.0' % number
    elif dot_count == 0:
        semver = '%s.0.0' % number
    else:
        return None

    pre_release_label = None
    pre_release_number = None
    release = version['release']
    if 'rc' in release:
        pre_release_label = 'rc'
        pre_release_number = release['rc']
    elif 'beta' in release:
        pre_release_label = 'beta'
        pre_release_number = release['beta']
    elif 'gmSeed' in release:
        pre_release_label = 'gm-seed'
        pre_release_number = release['gmSeed']
    if pre_release_label is not None:
        if pre_release_number is not None and pre_release_number > 1:
            semver = '%s-%s.%s' % (semver, pre_release_label, pre_release_number)
        else:
            semver = '%s-%s' % (semver, pre_release_label)
    return semver


def merged_versions(*lists):
    merged = []
    for versions in lists:
        for version in versions:
            if version not in merged:
                merged.append(version)
    return merged


def read_json(path):
    try:
        return json.loads(path.read_text())
    except FileNotFoundError:
        return None


def write_json(path, value):
    """Writes a file only when its content changes, so unchanged data makes no commit."""
    text = json.dumps(value, indent=2) + '\n'
    if path.exists() and path.read_text() == text:
        return False
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return True


# Sources: each turns what its source says into a snapshot.


def is_apple_silicon(download):
    return download.get('architectures') == ['arm64']


def describes(release):
    """Orders a build's entries in xcodereleases: the latest version, and
    for it, the Apple silicon download."""
    return semver_key(release['versions'][-1]), is_apple_silicon(release.get('download', {}))


def xcodereleases_snapshot(content):
    releases = {}
    started = False
    for xcode in reversed(json.loads(content)):
        # An Xcode offered both ways is listed as "Xcode" and "Xcode (Apple
        # Silicon)". "Xcode (Universal)" is Xcode 12 for macOS Universal Apps,
        # whose betas have their own builds but the same versions as Xcode 12's.
        if xcode['name'] not in ('Xcode', 'Xcode (Apple Silicon)'):
            continue
        if not started:
            if xcode['version']['number'] != FIRST_VERSION:
                continue
            started = True
        semver = semver_for(xcode['version'])
        if semver is None:
            continue
        version = xcode['version']
        links = xcode.get('links', {})
        date = xcode['date']
        release = without_empty({
            'versions': [semver],
            'build': version['build'],
            'date': '%04d-%02d-%02d' % (date['year'], date['month'], date['day']),
            'requires_macos': xcode.get('requires'),
            'download': without_empty({
                'url': links.get('download', {}).get('url'),
                'architectures': links.get('download', {}).get('architectures'),
            }),
            'release_notes': links.get('notes', {}).get('url'),
            'compilers': {
                name: entries[0]['number']
                for name, entries in sorted(xcode.get('compilers', {}).items())
                if entries and 'number' in entries[0]
            },
            'sdks': {
                platform: {'version': entries[0]['number'], 'build': entries[0]['build']}
                for platform, entries in sorted(xcode.get('sdks', {}).items())
                if entries and 'number' in entries[0] and 'build' in entries[0]
            },
        })
        # A release candidate that ships unchanged keeps its build, so one
        # build can have several versions, and an Xcode offered both for Apple
        # silicon and as Universal is listed once for each. The latest release
        # describes the build, with its Apple silicon download.
        earlier = releases.get(release['build'])
        if earlier is not None:
            versions = merged_versions(earlier['versions'], release['versions'])
            if describes(earlier) > describes(release):
                release = earlier
            release['versions'] = versions
        releases[release['build']] = release
    return {'releases': list(releases.values())}


FEED_TITLE = re.compile(
    r'^Xcode (?P<number>\d+(?:\.\d+){0,2})'
    r'(?: (?P<label>beta|RC|Release Candidate)(?: (?P<count>\d+))?)?'
    r' \((?P<build>[0-9A-Za-z]+)\)$'
)


def releases_feed_snapshot(content):
    releases = {}
    for item in ElementTree.fromstring(content).iter('item'):
        title = (item.findtext('title') or '').strip()
        if not title.startswith('Xcode '):
            continue
        match = FEED_TITLE.match(title)
        if match is None:
            warn('Skipping a feed item whose title is not understood: %s' % title)
            continue
        label = match['label']
        count = int(match['count'] or 1)
        if label is None:
            kind = {'release': True}
        elif label == 'beta':
            kind = {'beta': count}
        else:
            kind = {'rc': count}
        semver = semver_for({'number': match['number'], 'release': kind})
        date = parsedate_to_datetime(item.findtext('pubDate')).date().isoformat()
        release = releases.setdefault(match['build'], {'versions': [], 'build': match['build'], 'date': date})
        release['versions'] = merged_versions(release['versions'], [semver])
        release['date'] = max(release['date'], date)
    return {'releases': list(releases.values())}


def downloadables_index_snapshot(content):
    index = plistlib.loads(content)

    runtimes = {}
    for downloadable in index.get('downloadables', []):
        identifier = downloadable.get('platform')
        build = downloadable.get('simulatorVersion', {}).get('buildUpdate')
        if identifier not in PLATFORM_NAMES or build is None:
            continue
        runtime = runtimes.setdefault((PLATFORM_NAMES[identifier], build), without_empty({
            'platform': PLATFORM_NAMES[identifier],
            'version': downloadable['simulatorVersion'].get('version'),
            'build': build,
            'name': downloadable.get('name'),
            'beta': 'beta' in downloadable.get('name', '').lower(),
            'downloads': [],
        }))
        requirements = downloadable.get('hostRequirements', {})
        runtime.setdefault('downloads', []).append(without_empty({
            'architectures': downloadable.get('architectures'),
            'size': downloadable.get('fileSize'),
            'requires': without_empty({
                'min_xcode': requirements.get('minXcodeVersion'),
                'max_xcode': requirements.get('maxXcodeVersion'),
                'min_macos': requirements.get('minHostVersion'),
                'max_macos': requirements.get('maxHostVersion'),
                'excluded_architectures': requirements.get('excludedHostArchitectures'),
            }),
        }))

    # The SDKs each runtime is for. A runtime Apple maps an SDK to but does
    # not offer for download is kept with only its platform and build.
    for mapping in index.get('sdkToSimulatorMappings', []):
        sdk = mapping['sdkIdentifier']
        platform = next((name for name, (_, sdk_name) in PLATFORMS.items() if sdk.startswith(sdk_name)), None)
        if platform is None:
            continue
        build = mapping['simulatorBuildUpdate']
        runtime = runtimes.setdefault((platform, build), {'platform': platform, 'build': build})
        runtime.setdefault('sdks', []).append(without_empty({
            'version': sdk[len(PLATFORMS[platform][1]):],
            'build': mapping['sdkBuildUpdate'],
            'preferred': mapping.get('affinity') == 'preferred',
        }))

    # The components each Xcode build uses.
    assets = {(asset['assetType'], asset['assetBuildUpdate']): asset for asset in index.get('otherDownloadables', [])}
    mappings = defaultdict(list)
    for mapping in index.get('xcodeToOtherDownloadablesMappings', []):
        if 'xcodeBuildUpdate' in mapping:
            mappings[mapping['xcodeBuildUpdate']].append(mapping)
    releases = []
    for xcode_build, xcode_mappings in mappings.items():
        components = {}
        for asset_type, name in COMPONENTS.items():
            matches = [mapping for mapping in xcode_mappings if mapping['assetType'] == asset_type]
            if not matches:
                continue
            preferred = [mapping for mapping in matches if mapping.get('affinity') == 'preferred'] or matches
            build = preferred[-1]['assetBuildUpdate']
            asset = assets.get((asset_type, build), {})
            components[name] = without_empty({'build': build, 'size': asset.get('fileSizeBytes')})
        if components:
            releases.append({'build': xcode_build, 'components': components})

    return {'releases': releases, 'simulators': list(runtimes.values())}


# How xcodes names versions in Apple's list, such as "27.2.0-release.candidate.2".
XCODES_VERSION = re.compile(
    r'^(?P<number>\d+\.\d+\.\d+)(?:-(?P<label>beta|release\.candidate|gm-seed)(?:\.(?P<count>\d+))?)?$'
)
XCODES_LABELS = {'beta': 'beta', 'release.candidate': 'rc', 'gm-seed': 'gmSeed'}


def developer_downloads_snapshot(content):
    """Apple's list of developer downloads, from the file xcodes saves it to,
    available-xcodes.json. The list has no builds, and its dates are when a
    file last changed, so each release has only its versions and download."""
    releases = []
    for entry in json.loads(content):
        match = XCODES_VERSION.match(entry['xcodeID']['version'])
        if match is None or version_key(match['number']) < version_key(FIRST_VERSION):
            continue
        label = match['label']
        kind = {'release': True} if label is None else {XCODES_LABELS[label]: int(match['count'] or 1)}
        filename = entry.get('filename', '')
        if 'Apple_silicon' in filename:
            architectures = ['arm64']
        elif 'Universal' in filename:
            architectures = ['arm64', 'x86_64']
        else:
            architectures = None
        releases.append({
            'versions': [semver_for({'number': match['number'], 'release': kind})],
            'download': without_empty({
                'url': entry.get('url'),
                'architectures': architectures,
                'size': entry.get('fileSize'),
            }),
        })
    return {'releases': releases}


RELEASE_NOTES_TITLE = re.compile(r'^Xcode (?P<number>\d+(?:\.\d+){0,2})\b.* Release Notes$', re.IGNORECASE)


def release_notes_snapshot(content):
    """Apple's index of Xcode release notes: one page for each version, which
    covers its betas too."""
    pages = {}
    for reference in json.loads(content).get('references', {}).values():
        match = RELEASE_NOTES_TITLE.match(reference.get('title', ''))
        if match is None or not reference.get('url', '').startswith('/documentation/'):
            continue
        number = semver_for({'number': match['number'], 'release': {'release': True}})
        pages[number] = 'https://developer.apple.com' + reference['url']
    return {'release_notes': [{'version': version, 'url': url} for version, url in pages.items()]}


def sorted_snapshot(snapshot):
    """Orders a snapshot so that it changes only when its source does."""
    releases = []
    for release in snapshot.get('releases', []):
        if 'versions' in release:
            release = release | {'versions': sorted(release['versions'], key=semver_key)}
        releases.append(release)
    releases.sort(key=lambda release: (release.get('build', ''), [semver_key(v) for v in release.get('versions', [])]))
    simulators = sorted(snapshot.get('simulators', []), key=lambda runtime: (
        runtime['platform'], version_key(runtime.get('version', '')), runtime['build']
    ))
    release_notes = sorted(snapshot.get('release_notes', []), key=lambda page: version_key(page['version']))
    return without_empty({'releases': releases, 'simulators': simulators, 'release_notes': release_notes})


def entries(snapshot):
    """How much a snapshot lists: its releases, or its release notes pages."""
    return len(snapshot.get('releases', [])) + len(snapshot.get('release_notes', []))


def save_snapshot(name, snapshot):
    """Replaces a source's snapshot, unless the new one looks broken."""
    path = SOURCES / ('%s.json' % name)
    count = entries(snapshot)
    before = entries(read_json(path) or {})
    if count == 0 or (name not in ROLLING and count < before * 0.9):
        warn('Keeping the last snapshot of %s: it lists %d entries now, against %d before' % (name, count, before))
        return False
    return write_json(path, sorted_snapshot(snapshot))


def download(url):
    response = requests.get(url, timeout=60)
    response.raise_for_status()
    return response.content


def refresh_sources(developer_downloads):
    readers = [
        ('xcodereleases', lambda: xcodereleases_snapshot(download(XCODE_RELEASES_URL))),
        ('apple-releases-feed', lambda: releases_feed_snapshot(download(RELEASES_FEED_URL))),
        ('apple-downloadables-index', lambda: downloadables_index_snapshot(download(DOWNLOADABLES_INDEX_URL))),
        ('apple-release-notes', lambda: release_notes_snapshot(download(RELEASE_NOTES_INDEX_URL))),
    ]
    if developer_downloads is not None:
        readers.append(('apple-developer-downloads',
                        lambda: developer_downloads_snapshot(Path(developer_downloads).read_bytes())))
    changed = 0
    for name, read in readers:
        try:
            snapshot = read()
        except Exception as error:  # noqa: BLE001
            warn('Keeping the last snapshot of %s, which could not be read: %s' % (name, error))
            continue
        changed += save_snapshot(name, snapshot)
    print('Sources: %d of %d snapshots changed' % (changed, len(readers)))


# Manifest


def merge(build, records):
    """Merges what the sources say about one build, given as (source, release)
    pairs by precedence."""
    release = {
        'versions': sorted({version for _, record in records for version in record.get('versions', [])},
                           key=semver_key),
        'build': build,
        'sources': merged_versions([name for name, _ in records]),
    }
    for _, record in records:
        for field, value in record.items():
            release.setdefault(field, value)
    # A download describes one file, so it comes from one source: the first
    # with an Apple silicon download, or else the first with any. Other sources
    # fill its gaps only when they name the same file.
    downloads = [record['download'] for _, record in records if 'download' in record]
    downloads.sort(key=lambda download: not is_apple_silicon(download))
    if downloads:
        release['download'] = dict(downloads[0])
        for other in downloads[1:]:
            if other.get('url') == downloads[0].get('url'):
                for field, value in other.items():
                    release['download'].setdefault(field, value)
    return release


def matching_simulators(runtimes, sdks):
    """The simulator runtime Xcode uses for each SDK. xcodereleases sometimes
    lists a different SDK build than Xcode ships, so when Apple's index does
    not know the build, the runtime Apple prefers for that SDK version is
    used, and marked as matched by version."""
    simulators = {}
    for platform, sdk in sdks.items():
        if platform not in PLATFORMS:
            continue
        candidates = [(runtime, entry) for runtime in runtimes if runtime['platform'] == platform
                      for entry in runtime.get('sdks', []) if entry['build'] == sdk['build']]
        exact = bool(candidates)
        if not candidates:
            candidates = [(runtime, entry) for runtime in runtimes if runtime['platform'] == platform
                          for entry in runtime.get('sdks', []) if entry['version'] == sdk['version']]
        if not candidates:
            continue
        preferred = [candidate for candidate in candidates if candidate[1].get('preferred')] or candidates
        runtime, _ = max(preferred, key=lambda candidate: (
            version_key(candidate[0].get('version', '')), candidate[0]['build']
        ))
        simulator = {field: value for field, value in runtime.items() if field != 'sdks'}
        if not exact:
            simulator['matched_by_sdk_version'] = True
        simulators[platform] = simulator
    return simulators


def renamed(version):
    """A version under its current name: GM seeds were tagged "-seed" before
    they were "-gm-seed"."""
    return re.sub(r'(?<=\d)-seed(?=\.|$)', '-gm-seed', version)


def release_notes_link(notes, release):
    """Apple's current release notes page for a release's version, which
    Apple moves from time to time, or else the link a source gave. A link to
    a file only signed-in developers can download is left out."""
    number = release['versions'][-1].partition('-')[0]
    # A version Apple has no page for, such as 12.1.1, which only had a
    # release candidate, is covered by its minor version's page.
    minor = '.'.join(number.split('.')[:2]) + '.0'
    link = notes.get(number) or notes.get(minor) or release.get('release_notes')
    if link and link.startswith('https://download.developer.apple.com/'):
        link = None
    # Release notes from before Xcode 10 are all on one page in Apple's archive.
    if link is None and version_key(number) < [10]:
        link = OLD_RELEASE_NOTES_URL
    return link


def tagged_versions():
    """Versions already tagged, by build."""
    versions = defaultdict(list)
    for name in git('tag', '--list').splitlines():
        version, _, build = name.rpartition('+')
        if version:
            versions[build].append(renamed(version))
    return versions


def version_owners(releases):
    """The build each version belongs to. When two builds have a version, as
    when Apple re-released Xcode 13 beta 3 or a source renames a build, the
    newer build wins."""
    owner = {}
    for release in releases:
        for version in release['versions']:
            current = owner.get(version)
            if current is None or (release.get('date', ''), release['build']) > (current.get('date', ''), current['build']):
                owner[version] = release
    return {version: release['build'] for version, release in owner.items()}


def refresh_manifest():
    snapshots = {name: read_json(SOURCES / ('%s.json' % name)) or {} for name in PRECEDENCE}

    by_build = defaultdict(list)
    without_build = []
    for name in PRECEDENCE:
        for record in snapshots[name].get('releases', []):
            if 'versions' in record:
                record['versions'] = [renamed(version) for version in record['versions']]
            if 'build' in record:
                by_build[record['build']].append((name, record))
            else:
                without_build.append((name, record))

    # A release from a source without builds joins the build that has its
    # versions. When it has several, as when a release candidate ships
    # unchanged, the release's own download comes first.
    owner = version_owners(merge(build, records) for build, records in by_build.items())
    unknown = []
    for name, record in sorted(without_build, key=lambda item: max(map(semver_key, item[1]['versions'])),
                               reverse=True):
        builds = {owner[version] for version in record['versions'] if version in owner}
        if len(builds) == 1:
            by_build[builds.pop()].append((name, record))
        else:
            unknown.extend(record['versions'])
    if unknown:
        warn('Skipping releases whose build no source knows: %s' % ', '.join(sorted(unknown, key=semver_key)))

    releases = {}
    for build, records in by_build.items():
        records.sort(key=lambda item: PRECEDENCE.index(item[0]))
        release = merge(build, records)
        if release['versions']:
            releases[build] = release

    # Builds the sources no longer list keep their files, so their versions
    # stay tagged, and still compete for versions with the builds listed now.
    for path in RELEASES.glob('*.json'):
        if path.stem not in releases:
            release = read_json(path)
            releases[path.stem] = release | {'versions': [renamed(version) for version in release['versions']]}

    owner = version_owners(releases.values())
    runtimes = snapshots['apple-downloadables-index'].get('simulators', [])
    notes = {page['version']: page['url'] for page in snapshots['apple-release-notes'].get('release_notes', [])}

    tagged = tagged_versions()
    changed = 0
    for build, release in releases.items():
        path = RELEASES / ('%s.json' % build)
        existing = read_json(path) or {}
        # Versions tagged before keep their tags, so pins keep working, unless
        # another build has that version now, as when a source renames a build.
        release['versions'] = sorted((
            version
            for version in merged_versions(map(renamed, existing.get('versions', [])), tagged.get(build, []),
                                           release['versions'])
            if owner.get(version, build) == build
        ), key=semver_key)
        if not release['versions']:
            # A build whose every version went to a newer build.
            if path.exists():
                path.unlink()
                changed += 1
            continue
        release['simulators'] = matching_simulators(runtimes, release.get('sdks', {}))
        release['release_notes'] = release_notes_link(notes, release)
        release = {field: release[field] for field in FIELDS if field in release}
        changed += write_json(path, without_empty(release))
    changed += write_json(SIMULATORS, [runtime for runtime in runtimes if 'downloads' in runtime])
    changed += write_json(INDEX, release_index())
    print('Manifest: %d of %d files changed' % (changed, len(releases) + 2))


def release_index():
    """Every version, newest first, with its build, date and download URL."""
    entries = []
    for path in RELEASES.glob('*.json'):
        release = json.loads(path.read_text())
        for version in release['versions']:
            entries.append(without_empty({
                'version': version,
                'build': release['build'],
                'date': release['date'],
                'url': release.get('download', {}).get('url'),
            }))
    entries.sort(key=lambda entry: (entry['date'], semver_key(entry['version']), entry['build']), reverse=True)
    return entries


# Tags


def tag_name(version, build):
    return '%s+%s' % (version, build)


def version_title(version, build):
    """Names a version the way Apple does, such as "Xcode 27.3 beta 2 (27C5035i)"."""
    number, _, pre_release = version.partition('-')
    number = re.sub(r'(\.0){1,2}$', '', number)
    label = pre_release.replace('.', ' ').replace('rc', 'RC').replace('gm-seed', 'GM seed')
    return 'Xcode %s%s (%s)' % (number, ' ' + label if label else '', build)


def release_title(release):
    """Names a build for its release, rather than the release candidate it
    shipped unchanged from."""
    stable = [version for version in release['versions'] if '-' not in version]
    return version_title((stable or release['versions'])[-1], release['build'])


def committed_releases():
    """Yields each committed release with its file's blob, skipping files not
    committed yet."""
    for path in sorted(RELEASES.glob('*.json')):
        relative = str(path.relative_to(ROOT))
        blob = subprocess.run(['git', 'rev-parse', '--verify', '--quiet', 'HEAD:' + relative],
                              cwd=ROOT, capture_output=True, text=True).stdout.strip()
        if not blob:
            warn('Skipping %s, which is not committed' % path.name)
            continue
        yield json.loads(git('cat-file', 'blob', blob)), blob


def release_blob(commit):
    """The blob of a tag's release.json, or None for a tag from before tags
    held one."""
    return subprocess.run(['git', 'rev-parse', '--verify', '--quiet', commit + ':release.json'],
                          cwd=ROOT, capture_output=True, text=True).stdout.strip() or None


def refresh_tags(push):
    """Keeps each version's tag on the tip of its build's line of commits.

    Each build has its own line of commits, which hold only release.json:
    the build's file from releases/. When the file changes, a commit is added
    to the line and the build's tags move to it, so a tag's history is its
    release's history. Tags of versions that another build has now are
    deleted.
    """
    # The commit each tag points at.
    existing = {}
    for line in git('for-each-ref', 'refs/tags', '--format=%(refname:short) %(objectname) %(*objectname)').splitlines():
        name, target, *peeled = line.split()
        existing[name] = peeled[0] if peeled else target
    releases = list(committed_releases())

    if not releases:
        warn('Changing no tags: releases/ has no committed releases')
        return

    # A tag whose version its build no longer has: another build has it now,
    # or the version was renamed.
    versions = {release['build']: set(release['versions']) for release, _ in releases}
    deleted = []
    for name in sorted(existing):
        version, _, build = name.rpartition('+')
        if version not in versions.get(build, ()):
            git('tag', '--delete', name)
            deleted.append(name)

    changed = []
    for release, blob in releases:
        names = [tag_name(version, release['build']) for version in release['versions']]
        # The build's line ends at whichever of its tags is already on it.
        tip = next((existing[name] for name in names if name in existing and release_blob(existing[name])), None)
        if tip is None or release_blob(tip) != blob:
            tree = git('mktree', input='100644 blob %s\trelease.json\n' % blob)
            title = release_title(release)
            parent = ['-p', tip] if tip else []
            tip = git('commit-tree', tree, *parent, '-m', title if tip is None else 'Update ' + title)
        date = '%sT00:00:00' % release['date']
        env = dict(os.environ) | {'GIT_COMMITTER_DATE': date}
        message = release.get('download', {}).get('url', '')
        for name in names:
            if existing.get(name) != tip:
                git('tag', '--force', '--message', message, name, tip, env=env)
                changed.append(name)

    print('Tags: %d moved or created, %d deleted' % (len(changed), len(deleted)))
    if push:
        for names, prefix in ((changed, '+'), (deleted, ':')):
            for start in range(0, len(names), 100):
                git('push', 'origin', *[prefix + 'refs/tags/' + name for name in names[start:start + 100]])


# Releases


# GitHub limits how fast content is created, to about 500 requests an hour,
# so each run changes at most this many releases, a request a second, and
# leaves the rest for the next run.
RELEASE_CHANGES_PER_RUN = 100


class GitHub:
    """The parts of GitHub's API that releases need."""

    def __init__(self, repository, token):
        self.repository = repository
        self.session = requests.Session()
        self.session.headers.update({'Accept': 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28'})
        if token:
            self.session.headers['Authorization'] = 'Bearer %s' % token

    def request(self, method, url, **kwargs):
        if not url.startswith('https://'):
            url = 'https://api.github.com/repos/%s/%s' % (self.repository, url)
        for _ in range(5):
            response = self.session.request(method, url, timeout=60, **kwargs)
            limited = response.status_code in (403, 429) and (
                'retry-after' in response.headers or response.headers.get('x-ratelimit-remaining') == '0'
            )
            if not limited:
                break
            wait = int(response.headers.get('retry-after') or int(response.headers['x-ratelimit-reset']) - time.time())
            warn('GitHub asks to wait %d seconds' % wait)
            time.sleep(min(max(wait, 1), 600))
        response.raise_for_status()
        if method != 'GET':
            time.sleep(1)
        return response.json() if response.content else None

    def releases(self):
        releases = []
        page = 1
        while True:
            batch = self.request('GET', 'releases', params={'per_page': 100, 'page': page})
            releases.extend(batch)
            if len(batch) < 100:
                return releases
            page += 1


def release_notes(release):
    """A release's description on GitHub."""
    links = []
    if release.get('download', {}).get('url'):
        links.append('[Download](%s)' % release['download']['url'])
    if release.get('release_notes'):
        links.append('[Release notes](%s)' % release['release_notes'])
    # GitHub shows when a release was published here, not when Apple released it.
    first = ['Released %s.' % datetime.date.fromisoformat(release['date']).strftime('%B %-d, %Y')]
    if release.get('requires_macos'):
        first.append('Requires macOS %s or later.' % release['requires_macos'])
    paragraphs = [' '.join(first)]
    if links:
        paragraphs.append(' \u00b7 '.join(links))
    return '\n\n'.join(paragraphs)


def repository_name():
    if os.environ.get('GITHUB_REPOSITORY'):
        return os.environ['GITHUB_REPOSITORY']
    url = git('remote', 'get-url', 'origin')
    return re.sub(r'\.git$', '', re.split(r'github\.com[:/]', url)[-1])


def refresh_releases(dry_run):
    """Keeps a GitHub release for each tag, named for its version, with its
    release.json attached, and marks the newest stable Xcode as the latest."""
    github = GitHub(repository_name(), os.environ.get('GITHUB_TOKEN'))
    tags = set(git('tag', '--list').splitlines())
    releases = list(committed_releases())
    owner = version_owners(release for release, _ in releases)

    # Each tag's release, oldest first, so they are created in order.
    wanted = {}
    for release, blob in releases:
        for version in release['versions']:
            name = tag_name(version, release['build'])
            if name in tags and owner.get(version) == release['build']:
                wanted[name] = (version, release, blob)
    order = sorted(wanted, key=lambda name: (wanted[name][1]['date'], semver_key(wanted[name][0])))
    stable = [name for name in order if '-' not in wanted[name][0]]
    latest = stable[-1] if stable else None
    # The latest release goes first, so it's marked before any other exists:
    # until one is marked, GitHub calls the newest one made the latest.
    if latest is not None:
        order.remove(latest)
        order.insert(0, latest)

    existing = {release['tag_name']: release for release in github.releases()}
    created, updated, deleted = [], [], []

    for name in sorted(set(existing) - set(wanted)):
        deleted.append(name)
        if not dry_run:
            github.request('DELETE', 'releases/%d' % existing[name]['id'])

    left = 0
    for name in order:
        version, release, blob = wanted[name]
        content = subprocess.run(['git', 'cat-file', 'blob', blob], cwd=ROOT, check=True, capture_output=True).stdout
        digest = 'sha256:' + hashlib.sha256(content).hexdigest()
        fields = {
            'name': version_title(version, release['build']),
            'body': release_notes(release),
            'prerelease': '-' in version,
        }
        current = existing.get(name)
        assets = [asset for asset in (current or {}).get('assets', []) if asset['name'] == 'release.json']
        stale_fields = current is not None and any(current.get(key) != value for key, value in fields.items())
        stale_asset = current is None or [asset.get('digest') for asset in assets] != [digest]
        if not (current is None or stale_fields or stale_asset):
            continue
        if len(created) + len(updated) >= RELEASE_CHANGES_PER_RUN:
            left += 1
            continue
        (created if current is None else updated).append(name)
        if dry_run:
            continue
        make_latest = 'true' if name == latest else 'false'
        if current is None:
            current = github.request('POST', 'releases', json=dict(fields, tag_name=name, make_latest=make_latest))
        elif stale_fields:
            github.request('PATCH', 'releases/%d' % current['id'], json=dict(fields, make_latest=make_latest))
        if stale_asset:
            for asset in assets:
                github.request('DELETE', 'releases/assets/%d' % asset['id'])
            github.request('POST', current['upload_url'].split('{')[0], params={'name': 'release.json'},
                           data=content, headers={'Content-Type': 'application/json'})

    # A release marked latest only when created or edited, so the latest one
    # is checked on every run.
    if latest is not None and latest in existing and not dry_run:
        try:
            current_latest = github.request('GET', 'releases/latest')['tag_name']
        except requests.HTTPError:
            current_latest = None
        if current_latest != latest:
            github.request('PATCH', 'releases/%d' % existing[latest]['id'], json={'make_latest': 'true'})

    print('Releases: %d created, %d updated, %d deleted%s%s' % (
        len(created), len(updated), len(deleted),
        ', %d left for the next run' % left if left else '',
        ' (dry run)' if dry_run else '',
    ))


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    commands = parser.add_subparsers(dest='command', required=True)
    fetch = commands.add_parser('fetch', help='update the snapshots in sources/ from the sources that answer')
    fetch.add_argument('--apple-developer-downloads', metavar='FILE',
                       help="Apple's developer downloads, as xcodes saves them to available-xcodes.json")
    commands.add_parser('manifest', help='rebuild releases.json, releases/ and simulators.json from sources/')
    tags = commands.add_parser('tags', help="move each version's tag to its release's latest data")
    tags.add_argument('--push', action='store_true', help='push the tags that changed or were deleted to origin')
    releases = commands.add_parser('releases', help="keep a GitHub release for each tag, with its release.json")
    releases.add_argument('--dry-run', action='store_true', help='print what would change, and change nothing')
    arguments = parser.parse_args()

    if arguments.command == 'fetch':
        refresh_sources(arguments.apple_developer_downloads)
    elif arguments.command == 'manifest':
        refresh_manifest()
    elif arguments.command == 'tags':
        refresh_tags(arguments.push)
    else:
        refresh_releases(arguments.dry_run)

if __name__ == '__main__':
    main()
