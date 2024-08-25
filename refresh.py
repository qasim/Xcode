import requests

if __name__ == '__main__':
    r = requests.get('https://xcodereleases.com/data.json')
    print(r.json())
