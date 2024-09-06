import pandas as pd 
import requests
import json
import regex as re
from packaging import version
import os
import tarfile
import subprocess
import csv
import time
from tqdm import tqdm

def read_dicts_from_txt(text_file, separator="\n---\n"):
    with open(text_file, "r") as file:
        content = file.read()
        # Split the content by the separator, and ignore the first empty item if it exists
        dict_strings = [s for s in content.split(separator) if s]
        
    return dict_strings

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

def download_crate(crate_name, version):
    # Construct the output file name
    output_file = f"{crate_name}-{version}.tar.gz"

    # Construct the URL for downloading
    url = f"https://crates.io/api/v1/crates/{crate_name}/{version}/download"

    # Send a GET request to the URL
    response = requests.get(url, allow_redirects=True)

    # Check if the request was successful
    if response.status_code == 200:
        # Write the content to the output file
        with open(output_file, 'wb') as file:
            file.write(response.content)
    else:
        raise Exception(f"Failed to download the crate. Status code: {response.status_code}")

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

def is_version_in_range(version_str, range_str):
    """
    Check if a version is within a specified range.

    :param version_str: The version string to check.
    :param range_str: The range string, formatted as '<max_version, >=min_version'.
    :return: Boolean indicating if the version is within the range.
    """
    min_version, max_version = range_str.split(', ')
    min_version = min_version[2:]  # Remove '>='
    max_version = max_version[1:]  # Remove '<'

    return version.parse(min_version) <= version.parse(version_str) < version.parse(max_version)

def find_latest_version_in_range(all_versions, range_str):
    """
    Find the latest version from a list of versions that falls within a specified range.

    :param all_versions: List of all version strings.
    :param range_str: The range string, formatted as '<max_version, >=min_version'.
    :return: The latest version within the range, or None if none found.
    """
    valid_versions = [v for v in all_versions if is_version_in_range(v, range_str)]
    if valid_versions:
        return max(valid_versions, key=version.parse)
    else:
        return None

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
    # else:
    #     raise Exception(f"Failed to download the crate. Status code: {response.status_code}")

def extract_and_delete():
    current_dir = os.getcwd()
    os.chdir("processing")
    # Extract all .tar.gz files in the current directory
    print("Extracting crates...")
    for file in tqdm(os.listdir('.')):
        if file.endswith('.tar.gz'):
            try:
                with tarfile.open(file, 'r:gz') as tar:
                    tar.extractall()
                # print(f"Extracted {file}")
            except Exception as e:
                print(f"Failed to extract {file}: {e}")

    # Delete all .zip files in the current directory
    print("Deleting crates zipped files...")
    for file in tqdm(os.listdir('.')):
        if file.endswith('.tar.gz'):
            try:
                os.remove(file)
                # print(f"Deleted {file}")
            except Exception as e:
                print(f"Failed to delete {file}: {e}")  
    os.chdir(current_dir)

def run_shell_command(command):
    try:
        # Run the command and capture the output
        process = subprocess.run(command, shell=True, check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return process.stdout, process.stderr, process.returncode
    except subprocess.CalledProcessError as e:
        # Handle errors in the command execution
        return e.stdout, e.stderr, e.returncode

def run_cargo_scan_and_save_output():
    original_dir = os.getcwd()
    # print(f"Original directory: {original_dir}")
    os.chdir("processing")
    directories = [d for d in os.listdir('.') if os.path.isdir(d) and d != 'cargo-scan']
    # print(f"Directories: {directories[0]}")
    # exit()

    try:
        os.chdir('../cargo-scan')
        output_data = []
        directories = directories[:10]

        print("Getting Side Effects for Rust Sec crates...")
        for directory in tqdm(directories):
            try:
                command = f'cargo run --bin scan ../processing/{directory}'
                # print(f"Running command: {command}")
                # exit()
                process = subprocess.run(command, shell=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

                # Write output to a CSV file named after the directory
                csv_filename = f'../processing/rustsec/{directory}.csv'
                if not os.path.exists('../processing/rustsec'):
                    os.mkdir(f'../processing/rustsec')
                try:
                    with open(csv_filename, 'w', newline='') as csvfile:
                        writer = csv.writer(csvfile)
                        # writer.writerow(['Directory', 'Output', 'Error'])
                        writer.writerow([process.stdout, process.stderr])
                except Exception as e:
                    print(f"Failed to write to CSV file: {e}")
            except:
                print(f"An error occurred while processing {directory}")
                continue

    except Exception as e:
        print(f"An error occurred: {e}")
    finally:
        # Return to the original directory
        os.chdir(original_dir)

codex = read_dicts_from_txt("helpers/data.txt")
# print(codex[0])
pattern = r'(>=|>)?(\d+\.\d+(\.\d+)?)'
print("Downloading RustSec crates...")
for data in tqdm(codex):
    # print(dict)
    # data = dict(data)
    # print(data)
    # print(type(data))
    data = parse_dict_string(data)
    # print(data)
    temp = data["package"]
    package = temp["name"].split("(")[0]
    # print(package)
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
    download_crate(package,target_version)
    time.sleep(0.1)

extract_and_delete()
run_cargo_scan_and_save_output()
