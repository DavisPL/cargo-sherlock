from tqdm import tqdm
import json
import requests
from packaging import version
import regex as re
import time
import subprocess
import sys

def parse_dict_string(dict_string):
    # Helper function to convert strings to dictionaries
    def string_to_dict(s):
        try:
            # Convert string representation of dictionary to an actual dictionary
            return json.loads(s.replace("'", '"'))
        except json.JSONDecodeError:
            return s

    # Regular expression to match key-value pairs
    kv_pattern = re.compile(r"(\w+):\s*(.+)")

    result_dict = {}
    for line in dict_string.split('\n'):
        match = kv_pattern.match(line.strip())
        if match:
            key, value = match.groups()
            # Check if value is a nested dictionary or list
            if value.startswith('{') or value.startswith('['):
                result_dict[key] = string_to_dict(value)
            else:
                result_dict[key] = value

    return result_dict

def get_versions(dep_name):
    url = f"https://crates.io/api/v1/crates/{dep_name}/versions"
    headers = {"User-Agent": "reqwest"}
    response = requests.get(url, headers=headers)
    body = response.text
    data = json.loads(body)
    # print(data)
    if "errors" in data:
        return "error"
    versions = [v["num"] for v in data["versions"]] 
    # print("I have", versions)
    # Removing the versions with alphabetical characters like 3.0.0-beta.2. They cause problems later while automating
    versions = [version for version in versions if not any(char.isalpha() for char in version)]
    versions.sort()
    # print(versions)
    return versions

def find_previous_version(given_version, versions_list):
    # Convert all versions to a list of packaging.version.Version objects
    versions_objects = [version.parse(v) for v in versions_list]

    # Sort the versions
    versions_objects.sort()

    # Find the index of the given version
    try:
        index_of_given = versions_objects.index(version.parse(given_version))
        # Find the version one less than the given version, if it exists
        previous_version = versions_objects[index_of_given - 1] if index_of_given > 0 else None
    except ValueError:
        # Given version is not in the list
        previous_version = None

    return str(previous_version) if previous_version else None

def read_dicts_from_txt(text_file, separator="\n---\n"):
    with open(text_file, "r") as file:
        content = file.read()
        # Split the content by the separator, and ignore the first empty item if it exists
        dict_strings = [s for s in content.split(separator) if s]
        
    return dict_strings

def download_crate(crate_name, version):
    # Construct the output file name
    output_file = f"processing/{crate_name}-{version}.tar.gz"

    # Construct the URL for downloading
    url = f"https://crates.io/api/v1/crates/{crate_name}/{version}/download"

    # Send a GET request to the URL
    response = requests.get(url, allow_redirects=True)

    # Check if the request was successful
    if response.status_code == 200:
        # Write the content to the output file
        with open(output_file, 'wb') as file:
            file.write(response.content)

codex = read_dicts_from_txt("helpers/data.txt")
# print(codex[0])
pattern = r'(>=|>)?(\d+\.\d+(\.\d+)?)'
for data in tqdm(codex):
    data = parse_dict_string(data)
    temp = data["package"]
    package = temp["name"].split("(")[0]
    temp = data["patched"]
    versions = list()
    target_version = str()
    if temp == "no patched versions":
        versions = get_versions(package)
        target_version = versions[-1]
    else:
        (_,ver,_) = re.findall(pattern, temp)[0]
        versions = get_versions(package)
        if versions == "error":
            continue
        target_version = find_previous_version(ver, versions)
    print("Checking for" , package, target_version)
    if target_version == None:
        subprocess.run([sys.executable, 'sherlock.py', 'trust', package, '-o', f'rustsec/{package}_{target_version}.json'])
    else:
        subprocess.run([sys.executable, 'sherlock.py', 'trust', package, target_version, '-o', f'rustsec/{package}_{target_version}.json'])
    break
    time.sleep(0.1)
