from datetime import datetime
import subprocess
import os
import requests

if __name__ == '__main__':
    xcodes_response = requests.get('https://xcodereleases.com/data.json')
    xcodes = xcodes_response.json()
    xcodes.reverse()

    start = False

    for xcode in xcodes:
        if xcode['name'] != 'Xcode':
            continue

        version = xcode['version']
        number = version['number']

        if not start:
            if number == '8.0':
                start = True
            else:
                continue

        date_components = xcode['date']
        year = date_components['year']
        month = date_components['month']
        day = date_components['day']

        date = datetime(year, month, day)
        isodate = date.isoformat()

        build = version['build']

        dot_count = number.count('.')
        if dot_count == 2:
            semver = number
        elif dot_count == 1:
            semver = '%s.0' % number
        elif dot_count == 0:
            semver = '%s.0.0' % number
        else:
            continue

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
            pre_release_label = 'seed'
            pre_release_number = release['gmSeed']
        if pre_release_label is not None:
            if pre_release_number is not None and pre_release_number > 1:
                semver = '%s-%s.%s' % (semver, pre_release_label, pre_release_number)
            else:
                semver = '%s-%s' % (semver, pre_release_label)

        subprocess.run(
            ['git', 'tag', '--force', semver, '-m', build],
            check=True,
            env=dict(os.environ) | {
                "GIT_AUTHOR_DATE": isodate,
                "GIT_COMMITTER_DATE": isodate
            }
        )
