import json
import requests
import regex as re
from packaging import version
import csv
import pandas as pd
import subprocess
import toml
import os 
from packaging import version
from pydriller import Repository
import tarfile
import shutil
import random
from tqdm import tqdm
import copy
import sys
from packaging.version import parse

def get_github_repo_stats(username: str, repository: str, token_file: str = 'token.txt') -> dict | None:
    if not os.path.exists(token_file):
            print(f"Error: Token file '{token_file}' not found. Please generate a GitHub token and save it to a file named 'token.txt'.")
            return None
        
    try:
        with open(token_file, 'r') as file:
            token = file.read().strip()
    except Exception as e:
        print(f"Error reading token file: {e}")
        return None

    url = f"https://api.github.com/repos/{username}/{repository}"

  
    response = requests.get(url, headers={"Authorization": f"token {token}"})

    if response.status_code == 200:
        data = response.json()
        # print(data)
        stars = data['stargazers_count']
        forks = data['forks_count']
        watchers = data['subscribers_count']
        return {
            "stars": stars,
            "forks": forks,
            "watchers": watchers
        }
    else:
        print(f"Failed to retrieve data: {response.status_code}")
        return None

def get_stars_and_forks(crate_name: str) -> dict | None:
    # Get the repository URL for the crate
    url = f"https://crates.io/api/v1/crates/{crate_name}"
    response = requests.get(url)
    data = response.json()
    repository_url = data['crate']['repository']
    if repository_url == None:
        return None
    if '.git' in repository_url:
        repository_url = repository_url.rstrip('.git')

    regex = r"https:\/\/github\.com\/([^\/]+)\/([^\/]+)";
    match = re.match(regex, repository_url)


    if match:
        username = match.group(1)
        repo_name = match.group(2)
        return get_github_repo_stats(username, repo_name)
    else:
        # print("No match found for repository URL")
        return None

def read_dicts_from_txt(text_file, separator="\n---\n"):
    """
    Reads a text file containing multiple dictionary entries separated by a delimiter.
    """
    with open(text_file, "r") as file:
        content = file.read()
        dict_strings = [s for s in content.split(separator) if s]
    return dict_strings

def parse_dict_string(dict_string):
    """
    Converts a string representation of a dictionary (with keys and values on separate lines)
    into an actual Python dictionary.
    """
    def string_to_dict(s):
        try:
            return json.loads(s.replace("'", '"'))
        except json.JSONDecodeError:
            return s
    
    kv_pattern = re.compile(r"(\w+):\s*(.+)")
    result_dict = {}
    
    for line in dict_string.split('\n'):
        match = kv_pattern.match(line.strip())
        if match:
            key, value = match.groups()
            if value.startswith('{') or value.startswith('['):
                result_dict[key] = string_to_dict(value)
            else:
                result_dict[key] = value
    return result_dict


def normalize_version(version):
    return parse(version)

# def get_versions(dep_name: str):
#     url = f"https://crates.io/api/v1/crates/{dep_name}/versions"
#     headers = {"User-Agent": "reqwest"}
#     response = requests.get(url, headers=headers)
#     data = response.json()
#     if "errors" in data:
#         return "error"
    
#     versions = [v["num"] for v in data["versions"]]
#     versions.sort(key=normalize_version)
#     return versions

def get_versions(dep_name: str):
    url = f"https://crates.io/api/v1/crates/{dep_name}/versions"
    headers = {"User-Agent": "reqwest"}
    response = requests.get(url, headers=headers)
    body = response.text
    data = json.loads(body)
    if "errors" in data:
        return "error"
    versions = [v["num"] for v in data["versions"]]
    # Removing versions with alphabetical characters like '3.0.0-beta.2'
    versions = [v for v in versions if not any(char.isalpha() for char in v)]
    # Sort versions using packaging's Version class
    versions.sort(key=version.parse)
    return versions


def find_previous_version(given_version, versions_list):
    versions_objects = [version.parse(v) for v in versions_list]

    versions_objects.sort()

    try:
        index_of_given = versions_objects.index(version.parse(given_version))
        # Find the version one less than the given version, if it exists
        previous_version = versions_objects[index_of_given - 1] if index_of_given > 0 else None
    except ValueError:
        # Given version is not in the list
        previous_version = None

    return str(previous_version) if previous_version else None

# def inRustSec(crate_name, version):
#     codex = read_dicts_from_txt("data.txt")
#     # print(cod÷ex)
#     pattern = r'(>=|>)?(\d+\.\d+(\.\d+)?)'
#     for data in codex:
#         data = parse_dict_string(data)
#         temp = data["package"]
#         package = temp["name"].split("(")[0]
#         if package == crate_name:
#         # print(package)
#             temp = data["patched"]
#             if temp == "no patched version": # this means that the crate is still vulnerable
#                 return "Critical"
#             else:
#                 ver = re.findall(pattern, temp)
#                 # print(data)
#                 flag, label = bulls_eye(ver, version)
#                 if label == "Critical" and flag:
#                     print("This crate has been flagged by RustSec.")
#                     return "Critical"
#                 if label == "Critical" and not flag:
#                     # print("This is present in RUST SEC but has been patched. However, you are using a vulnerable version.")
#                     print("A past version of this crate appears in RustSec. Please check the patched version.")
#                     return "Critical"
#                 if label == None and flag:
#                     # print("This crate has been reported by RustSec but you are using a patched version.")
#                     print("A past version of this crate appears in RustSec. Please check the patched version.")
#                     return "Low"
#     return "Safe"

def is_vulnerable(crate_version, patched_info):
    """
    Determines if a given crate_version is vulnerable based on a generic patched_info string.
    
    Two cases are supported:
      1. If patched_info starts with '^', it is treated as a compound expression.
         In that case we extract all version thresholds from the string and, for each,
         if the threshold's major version matches the crate_version's major version, we
         compare crate_version against that threshold.
      2. Otherwise, patched_info is assumed to be a simple expression (e.g. ">=3.7.2"),
         and the version is vulnerable if it is less than the threshold.
         
    If patched_info is "no patched version", it always returns True.
    """
    if patched_info == "no patched versions":
        return True

    parsed_version = version.parse(crate_version)
    
    if patched_info.startswith('^'):
        thresholds = re.findall(r'(\d+\.\d+\.\d+)', patched_info)
        for threshold_str in thresholds:
            threshold_version = version.parse(threshold_str)
            if threshold_version.major == parsed_version.major:
                return parsed_version < threshold_version
        return False
    else:
        match = re.match(r'>=\s*(\d+\.\d+\.\d+)', patched_info)
        if match:
            threshold_str = match.group(1)
            threshold_version = version.parse(threshold_str)
            return parsed_version < threshold_version
        else:
            return False

def inRustSec(crate_name, crate_version):
    """
    Checks if the given crate appears on RustSec and returns:
      - in_rustsec: True if the crate is found and at least one advisory marks the version as vulnerable.
      - in_patched_rustsec: True if the crate is found and every advisory indicates the version is patched.
      - label: Overall label, using the advisory's "classification" (or "Critical" if not provided)
               for vulnerable advisories; if all advisories mark as patched, returns "Patched". 
               If no advisory is found, returns "Safe".
      - advisory_type: The advisory "type" (collected from each record's "type" field).
    """
    codex = read_dicts_from_txt("data.txt")
    vulnerable_labels = []  # For vulnerable advisories' labels.
    patched_count = 0       # Count of advisories that indicate patched.
    advisories_found = False
    types_list = []         # To collect type values from each advisory.
    
    for data in codex:
        record = parse_dict_string(data)
        package = record.get("package", {}).get("name", "").split("(")[0]
        if package == crate_name:
            advisories_found = True
            
            # Gather the advisory "type" from the record if available.
            rec_type = record.get("type", None)
            if rec_type is not None:
                types_list.append(rec_type)
            
            patched_info = record.get("patched", "")
            classification = record.get("classification", None)
            if patched_info == "no patched version" or is_vulnerable(crate_version, patched_info):
                vuln_label = classification if classification is not None else "Critical"
                vulnerable_labels.append(vuln_label)
            else:
                patched_count += 1

    if types_list:
        unique_types = list(set(types_list))
        advisory_type = unique_types[0] if len(unique_types) == 1 else unique_types
    else:
        advisory_type = None

    # If no advisories were found, return defaults.
    if not advisories_found:
        return False, False, "Safe", advisory_type

    # Determine overall label and vulnerability status.
    if vulnerable_labels:
        unique_labels = list(set(vulnerable_labels))
        overall_label = unique_labels[0] if len(unique_labels) == 1 else unique_labels
        return True, False, overall_label, advisory_type
    else:
        return False, True, "Patched", advisory_type


def bulls_eye(ver, version):
    '''
        this ver is actually a list of tuples of size 3, where the first element is the operator, second is the version and third is not relevant looks something like this 
        [('>=', '0.23.5', '.5'), ('>=', '0.22.4', '.4'), ('', '0.23.0', '.0'), ('>=', '0.21.11', '.11'), ('', '0.22.0', '.0')]
        the above list says:
        - Patched for version 0.23.5 and above
        - Patched for version 0.22.4 and above
        - No issues in versions less than 0.23.0
        - Patched for version 0.21.11 and above
        - No issues in versions less than 0.22.0

        This means anything above 0.23.5 is safe. 
        Anything above 0.22.4 but less than 0.23.0 is safe.
        Anything above 0.21.11 but less than 0.22.0 is safe.

        Now, if my version is in unsafe range, I should return Critical. 
        If the version has been patched return patched.
    '''
    # print("I am comparing", version  , "with" , ver)
    for i in range(0,len(ver)):
        # print("I am", i, ver[i])
        (op,v,_) = ver[i]
        if i+1 < len(ver):
            # print("next is", i+1 , ver[i+1])
            (op2,v2,_) = ver[i+1]
            # print(op2 , v2)
            if op2 == '':
                # print("494")
                if version < v2 and version >= v: # this means that the version is in the range of v and v2
                    return True,None
                else: #not in the range of v and v2
                    return False,"Critical"
            # if op2=='>=': #I have not seen this case yet so leaving it for now.
            #     print("The unexpected happened")
            #     print("i was comparing", version , ver)
            #     return None # returning None so code crashes if this happens
        if op == '>=':
            if version >= v:
                return True,None
            else:
                return False,"Critical"
        if op == '': #means < 
            if version >= ver: #means patched range
                # print("I am here")
                return True,None
            else:
                return False,"Critical"   
    return True,"Critical"

def get_cargo_vet():
    url = "https://raw.githubusercontent.com/mozilla/cargo-vet/main/registry.toml"
    try:
        response = requests.get(url)
        response.raise_for_status()  # Raises an HTTPError for bad responses
    except requests.RequestException as e:
        print(f"Failed to fetch data: {e}")
        return None
    
    # Parse the TOML content
    data = toml.loads(response.text)
    # print(data.keys())
    codex = data['registry']  # There is only one key currently, so hard coded, might need to update later. 
    result = {}
    for org,_ in codex.items():
        try:
            urls = codex[org]
            for url,_ in urls.items():
                result[org] = urls[url]
        except:
            pass
    return result

def get_organization_file(url,file):
    try:
        response = requests.get(url)
        response.raise_for_status()  
        with open(f"../audits/{file}.toml", "w") as file:
            file.write(response.text)
    except requests.RequestException as e:
        print(f"Failed to download and save file: {e}")

def getVersion(version):
    '''
    this can get input in two forms 
    1) 1.0.57 -> 1.0.61
    2) 1.0.68
    in first case return [1.0.57,1.0.61]
    in second case return [1.0.68]
    '''
    if '->' in version:
        temp = version.split("->")
        return temp
    else:
        return [version]

def clean_toml(toml_path):
    '''
    Load the toml file, and remove all keys with crtieria , i.e [criteria.crypto-safe]
    Can't do delete as it is a dictionary, so I will have to save the file again.
    '''

    with open(toml_path, 'r') as file:
        toml_data = toml.load(file)
        for key in list(toml_data.keys()):
            if 'criteria' in key:
                del toml_data[key]
    with open(toml_path, 'w') as file:
        toml.dump(toml_data, file)
  
def parse_toml_with_type_and_crate(toml_path):
    data = {}
    entry = {}
    current_type = None
    current_crate = None
    multi_line_key = None
    buffer = []

    clean_toml(toml_path)
    
    with open(toml_path, 'r') as file:
        for line in file:
            line = line.rstrip()
            if line.startswith('[[') and line.endswith(']]'):
                # Save the previous entry if it exists
                if entry:
                    if current_crate not in data[current_type]:
                        data[current_type][current_crate] = []
                    data[current_type][current_crate].append(entry)
                
                # Extract the type and crate name from the section name
                section_parts = line[2:-2].split('.')
                current_type = section_parts[0]  # e.g., "audits"
                current_crate = section_parts[1]  # e.g., "anyhow"
                
                # Initialize dictionaries if not already present
                if current_type not in data:
                    data[current_type] = {}
                if current_crate not in data[current_type]:
                    data[current_type][current_crate] = []
                
                # Reset for the new entry
                entry = {}
                multi_line_key = None
                buffer = []
            elif '=' in line:
                if multi_line_key:
                    # Append the last multi-line entry
                    entry[multi_line_key] = '\n'.join(buffer).strip()
                    multi_line_key = None
                    buffer = []
                
                key, value = line.split('=', 1)
                key = key.strip()
                value = value.strip()
                
                if value.startswith('"""'):
                    multi_line_key = key
                    # Check if it also ends on the same line
                    if value.endswith('"""') and value.count('"""') > 1:
                        entry[key] = value[3:-3].strip()
                        multi_line_key = None
                    else:
                        buffer.append(value[3:])
                else:
                    entry[key] = value.strip('"')
            elif multi_line_key:
                if line.endswith('"""'):
                    buffer.append(line[:-3])
                    entry[multi_line_key] = '\n'.join(buffer).strip()
                    multi_line_key = None
                    buffer = []
                else:
                    buffer.append(line)

        # Append the last entry if any
        if entry and current_crate and current_type:
            if current_crate not in data[current_type]:
                data[current_type][current_crate] = []
            data[current_type][current_crate].append(entry)

    return data

def is_audited(crate_name, version=None):
    '''
    Get the name of the organization who audited that thing in specific. 
    if google cater for ub-risk criteria as well and points based on that?
    '''
    cargo_vet = get_cargo_vet()
    # print(cargo_vet)
    for org,url in cargo_vet.items():
        get_organization_file(url,org)
    
    organiations = cargo_vet.keys()
    vessel = []
    points = 0
    for org in organiations:
        codex = parse_toml_with_type_and_crate(f"../audits/{org}.toml")
        for type,data in codex.items():
            temp = {}
            for name,info in data.items():
                if name == crate_name: 
                    if type == 'trusted':
                        for audit in info:
                            temp["organization"] = org
                            temp["type"] = type
                            temp["criteria"] = audit["criteria"]
                            temp["points"] = 3
                            if temp != {}:
                                vessel.append(temp)
                                temp = {}
                                points = 0
                    else:
                        for audit in info:
                            if 'delta' in audit:
                                versions = getVersion(audit["delta"])
                                if version in versions:
                                    if 'safe-to' in audit['criteria']: 
                                    # covers the following cases:
                                    # 1) safe-to-deploy
                                    # 2) safe-to-run
                                    # 3) rule-of-two-safe-to-deploy
                                        points+=3
                                    if 'ub-risk-2' in audit['criteria']: # average good crate , trivial risk of UB
                                        points-=2
                                    if 'ub-risk-3' in audit['criteria']: # do not hold typical standards , significant risk of UB
                                        points -=4
                                    if 'ub-risk-4' in audit['criteria']: # extremle unsoundness, should be avoided
                                        points -=5
                                else:
                                    # print(f"The crate has been audited by {org} for version {versions}.")
                                    points = None
                                temp["organization"] = org
                                temp["type"] = type
                                temp["criteria"] = audit["criteria"]
                                temp["delta"] = audit["delta"]
                                temp["points"] = points
                                # temp.append(points)
                                if 'notes' in audit:
                                    # temp.append(audit["notes"])
                                    temp["notes"] = audit["notes"]
                                if temp != {}:
                                    del temp["points"] # I do not want to add points to the final output
                                    vessel.append(temp)
                                    temp = {}
                                    points = 0
                            else: #when will this happen? - when it is audited for the first time.
                                # print(audit , org)
                                if "version" not in audit.keys(): #this happens when mozilla audits a crate they have devloped but there are some commits by other ppl as well, so they just audit the commits and not a specific version.
                                    points = 3
                                elif version == audit["version"]:
                                    # print("This specific version is audited by", org)
                                    if 'safe-to' in audit['criteria']: 
                                    # covers the following cases:
                                    # 1) safe-to-deploy
                                    # 2) safe-to-run
                                    # 3) rule-of-two-safe-to-deploy
                                        points+=3
                                    if 'ub-risk-2' in audit['criteria']: # average good crate , trivial risk of UB
                                        points-=2
                                    if 'ub-risk-3' in audit['criteria']: # do not hold typical standards , significant risk of UB
                                        points -=4
                                    if 'ub-risk-4' in audit['criteria']: # extremle unsoundness, should be avoided
                                        points -=5
                                else:
                                    # print(f"The crate has been audited by {org} for version {audit['version']}.")
                                    points = None
                                temp["organization"] = org
                                temp["type"] = type
                                temp["criteria"] = audit["criteria"]
                                temp["points"] = points
                                if 'version' in audit.keys():
                                    temp["version"] = audit["version"]
                                if 'notes' in audit:
                                    # temp.append(audit["notes"])
                                    temp["notes"] = audit["notes"]
                                if temp != {}:
                                    # print("adding temp to vessel")
                                    del temp["points"] # I do not want to add points to the final output
                                    vessel.append(temp)
                                    temp = {}
                                    points = 0
                                    # print("vessel is", vessel)
                            
        # break
    if vessel == []:
        print("This crate has not been audited by any organization.")
        return False,{}
    return True, vessel

def get_author(crate_name: str):
    '''
    query the crates.io page and get the author name
    '''
    url = f"https://crates.io/api/v1/crates/{crate_name}/owners"
    response = requests.get(url)

    data = response.json()  # Parse JSON response
    owners = []
    if response.status_code == 200:
        # Extract author names from versions data
        codex = data['users']
        '''
        {'avatar': 'https://avatars.githubusercontent.com/u/64996?v=4', 'id': 1, 'kind': 'user', 'login': 'alexcrichton', 'name': 'Alex Crichton', 'url': 'https://github.com/alexcrichton'}
        this is what each contributor looks like. 
        '''
        for contributor in codex:
            temp = [] # collecting kind, name , name , url
            temp.append(contributor['kind'])
            temp.append(contributor['name'])
            temp.append(contributor['login'])
            temp.append(contributor['url'])
            owners.append(temp)
        return owners
    else:
        return "Failed to retrieve crate data: HTTP Status Code {}".format(response.status_code)

def get_downloads(crate_name: str):    
    '''
    Query the crates.io API to get total download counts for a crate.
    '''
    url = f"https://crates.io/api/v1/crates/{crate_name}"
    response = requests.get(url)
    if response.status_code == 200:
        data = response.json()
        total_downloads = data['crate']['downloads']
        return total_downloads

def remove_after_value(list_of_lists, value):
    # Find the index where the value is found
    index_to_cut = None
    for i, sublist in enumerate(list_of_lists):
        if value in sublist:
            index_to_cut = i
            break
    
    if index_to_cut is not None:
        return list_of_lists[:index_to_cut-1]
    else:
        return list_of_lists 
    
def remove_before_value(list_of_lists, value):
    # Find the index where the value is found
    index_to_cut = None
    for i, sublist in enumerate(list_of_lists):
        if value in sublist:
            index_to_cut = i
            break
    
    if index_to_cut is not None:
        # Keep the list that contains the value and all subsequent lists
        return list_of_lists[index_to_cut:]
    else:
        # If the value is not found, return the entire list
        return list_of_lists

def formatter(codex):
    formatted_data = []
    for sequence in codex:
        split_list = re.split(r'(?<!\\),', str(sequence))
        split_list = [item.replace('\\,', ',') for item in split_list]
        split_list = [x.strip() for x in split_list]
        formatted_data.append(split_list)
    return formatted_data

def clean_row(row):
    '''
    Input : ["['crate", 'fn_decl', 'callee', 'effect', 'dir', 'file', 'line', "col']"]
    output : ['crate", 'fn_decl', 'callee', 'effect', 'dir', 'file', 'line', "col']
    '''
    row_str = ','.join(row)
    row_str = row_str.lstrip("['").rstrip("']")
    cleaned_row = re.split(r'(?<!\\),', row_str)
    cleaned_row = [item.strip().strip("'\"") for item in cleaned_row]
    return cleaned_row

def get_potential_functions(file_path):
    # print(file_path)c
    length = 0
    try:
        with open(file_path) as csv_file:
            reader = list(csv.reader(csv_file))
            target = ['crate, fn_decl, callee, effect, dir, file, line, col']
            start_index = reader.index(target)
            lines = reader[start_index:-3] # removing the first two and last three lines, the last three lines contains the summary and first line is finished 'dev' profile etc 
        formatted_lines = formatter(lines)
        formatted_lines = [clean_row(row) for row in formatted_lines]
        df = pd.DataFrame(formatted_lines[1:] , columns=formatted_lines[0])
        # here I am getting the count for just the unsafe calls, it is possible to get the count of each type of side effect as well if interested. 
        unsafe = df[df["effect"].str.contains("unsafe", case=False, na=False)]["effect"].count()
        unsafe += df[df["effect"].str.contains("PtrDeref", case=False, na=False)]["effect"].count() # Unsafe calls with a pointer dereference are labeled as PtrDeref

        with open("effect_counts.json", "r") as file:
                loaded_effect_counts = json.load(file)
                rustsec_effects = loaded_effect_counts.keys()
                concerned_df = df[df['effect'].isin(rustsec_effects)]
                desired_order = ['dir', 'file', 'line', 'col', 'fn_decl', 'callee', 'effect']
                df_reordered = concerned_df[desired_order]
                df_reordered.to_csv(f"../experiments/dangerous_functions.csv")
                return len(df), len(concerned_df) , int(unsafe)
    except FileNotFoundError:
        print(f"File not found: {file_path}")
        return None,None,None
    except Exception as e:
        print(f"An error occurred: {e}")
        return None,None,None

def download_crate(crate_name: str, version: str):
    # Construct the output file name
    output_file = f"../processing/{crate_name}-{version}.tar.gz"

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
    current_directory = os.getcwd()
    os.chdir("../processing")
    # Extract all .tar.gz files in the current directory
    for file in os.listdir('.'):
        if file.endswith('.tar.gz'):
            try:
                with tarfile.open(file, 'r:gz') as tar:
                    tar.extractall()
                # print(f"Extracted {file}")
            except Exception as e:
                print(f"Failed to extract {file}: {e}")

    # Delete all .zip files in the current directory
    for file in os.listdir('.'):
        if file.endswith('.tar.gz'):
            try:
                os.remove(file)
                # print(f"Deleted {file}")
            except Exception as e:
                print(f"Failed to delete {file}: {e}")  
    os.chdir(current_directory)

def rudra(crate_name, version):
    '''
    This function will run rudra on the crate and give the output.
    Run ./Users/hassnain/Desktop/Research/code-sherlock/Rudra/docker-helper/docker-cargo-rudra /crate_name-version
    '''
    # download_crate(crate_name, version)
    # extract_and_delete()
    path = f"/Users/hassnain/Desktop/SQ24/289C/project/Rudra/docker-helper/docker-cargo-rudra {crate_name}-{version}"
    result = subprocess.run(path, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    return result.stdout

def version_audit(audit_info, target):
    '''
    This function will check if the same version has been audited or not. 
    '''
    future = True
    target = version.parse(target)
    for audit in audit_info:
        if 'version' in audit:
            temp = version.parse(audit["version"])
            if temp == target:
                return True,future
            elif temp < target:
                future = False
        if 'delta' in audit:
            start,end = getVersion(audit["delta"])
            # print(start,end)
            start = version.parse(start)
            end = version.parse(end)
            if target == start or target == end:
                return True,future
            if target < start:
                future = True 
            if target > end:
                future = False
    return False,future

def get_labels(audit_info):
    '''
    audit info looks something like this:
    (True, [['google', 'audits', 'safe-to-run', 3, '0.8.3'], ['google', 'audits', '[ "safe-to-run", "does-not-implement-crypto",]', 3, '0.8.5', 'Reviewed in https://crrev.com/c/5171063\\n\\nPreviously reviewed during security review and the audit is grandparented in.\\n']])
    '''
    # print(audit_info)
    pointsFlag = False
    orgs = {}
    for audit in audit_info:
        # print(audit)
        if audit["points"] == -2:
            print("This crate has been flagged by Google for extreme unsoundness. Do not use it.")
            # return "Critical"
            orgs[audit["organization"]] = "Critical"
        if audit["points"] == -1:
            print("This crate has been flagged by Google for significant risk of UB. Use with caution.")
            # return "High"
            orgs[audit["organization"]] = "High"
        if audit["points"] == 0:
            print("This crate has been flagged by Google for trivial risk of UB. Use with caution.")
            # return "Medium"
            orgs[audit["organization"]] = "Medium"
        if audit["points"] == 1:
            print("This crate, unsafe code has been certified sound by google.")
            # return "Low"
            orgs[audit["organization"]] = "Low"
        if audit["points"] == 2:
            print("This crate has no unsafe code.")
            orgs[audit["organization"]] = "Very Low"
        if audit["points"] == 3:            
            print("This crate has been flagged by Google as safe to run.")
            # return "Safe"
            orgs[audit["organization"]] = "Safe"
    return orgs

def get_last_audited_version(audit_info):
    '''
    This function will return the last audited version.
    '''
    last = "0.0.0"
    last = version.parse(last)
    for audit in audit_info:
        if 'version' in audit:
            temp = version.parse(audit["version"])
            if last < temp:
                last = temp
        if 'delta' in audit:
            start,end = getVersion(audit["delta"])
            end = version.parse(end)
            if last < end:
                last = end
    return last

def get_repo_url(crate_name):
    '''
    This function will clone the repo of the crate 
    '''
    url = f"https://crates.io/api/v1/crates/{crate_name}"
    response = requests.get(url)

    data = response.json()  # Parse JSON response
    return data['crate']['repository']
    
def repo_analysis(crate_name , target, last_audited_release):
    url = get_repo_url(crate_name)
    target = "Release " + str(target)
    last_audited_release = "Release " + str(last_audited_release)
    hash_target = None
    hash_last_audited_release = None
    for commit in Repository(url).traverse_commits():
        if commit.msg == target:
            hash_target = commit.hash
        if commit.msg == last_audited_release:
            hash_last_audited_release = commit.hash
        if hash_target and hash_last_audited_release:
            break
    for commit in Repository(url , from_commit=hash_last_audited_release , to_commit=hash_target).traverse_commits():
        print(commit.msg)
        for mod in commit.modified_files:
            print(mod.filename)
            print(mod.change_type)
            # print(mod.diff_parsed)
            print("_______")
        print("****************************")
        # print(commit)

def run_cargo_and_save(crate_name, crate_version):
    if not os.path.exists("../experiments"):
        os.mkdir("../experiments") 

    original_directory = os.getcwd()
    # crate_name = crate_name.replace('-', '_') # idk why this was here, but this was casuing the cargo-scan to crash, because this modified the crate-name that was supplied to cargo-scan and than cargo-scan would not be able to find the directory and cause a crash. This lead to that 2 columns passed, expeced 8 columns error. Commenting this fixed this. This might cause issues later. But the issue is yet to be encounterd. 
    crate_path = os.path.join(original_directory, "../processing", f"{crate_name}-{crate_version}")
    output_file_path = os.path.join(original_directory, "../experiments", f"{crate_name}-{crate_version}.csv")

    cargo_scan_directory = os.path.join(original_directory, "../cargo-scan")
    os.chdir(cargo_scan_directory)
    command = f'cargo run --bin scan {crate_path}'
    # Combine stderr into stdout to capture all output
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

    os.chdir(original_directory)

    # Write the output to the CSV file
    with open(output_file_path, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        # Split the output into lines to write each line separately
        writer.writerows([[line] for line in result.stdout.splitlines()])
    
    return output_file_path

def get_dependencies(crate_name, version):
    # Fetch dependencies from crates.io API
    url = f"https://crates.io/api/v1/crates/{crate_name}/{version}/dependencies"
    response = requests.get(url)
    if response.status_code == 200:
        return response.json()['dependencies']
    else:
        print(f"Failed to fetch dependencies for {crate_name} version {version}")
        return []

def run_miri_and_save(crate_name, crate_version):
    # Define paths
    base_dir = os.path.abspath(os.path.join(os.getcwd(), ".."))
    experiments_dir = os.path.join(base_dir, "experiments")
    crate_dir = os.path.join(base_dir, "processing", f"{crate_name}-{crate_version}")
    output_file_path = os.path.join(experiments_dir, f"{crate_name}-{crate_version}_miri_output.csv")

    # Ensure the experiments directory exists
    os.makedirs(experiments_dir, exist_ok=True)

    # Change to the crate directory
    original_directory = os.getcwd()
    os.chdir(crate_dir)

    try:
        # Command to run Miri tests
        command = 'cargo +nightly miri test'

        # Run the command with a 10 minute timeout (600 seconds)
        result = subprocess.run(
            command,
            shell=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=600  # Timeout set to 600 seconds (10 minutes)
        )

        # Write the output to the CSV file
        with open(output_file_path, 'w', newline='') as csvfile:
            writer = csv.writer(csvfile)
            writer.writerows([[line] for line in result.stdout.splitlines()])
    except subprocess.TimeoutExpired:
        print("Miri test did not complete within 10 minutes. Timing out.")
        return None
    except Exception as e:
        print(f"An error occurred helper/logger::run_miri_and_save: {e}")
        return None
    finally:
        # Change back to the original directory
        os.chdir(original_directory)

    return output_file_path


# def parse_miri_summary(output_file_path):
#     """
#     Parses the Miri output file to extract the last test result summary.
    
#     The expected format in the file is similar to:
#       test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.43s
    
#     Returns:
#         A dictionary with keys:
#             'status', 'passed', 'failed', 'ignored', 'measured', 'filtered_out', 'time_seconds'
#         or None if no summary line could be found or parsed.
#     """
#     if not os.path.exists(output_file_path):
#         print(f"File not found: {output_file_path} Miri")
#         return None

#     summary_line = None
#     with open(output_file_path, 'r') as f:
#         for line in f:
#             if "test result:" in line:
#                 summary_line = line.strip().strip('"')

#     if summary_line is None:
#         print("No test summary line found in the file for Miri")
#         return {"status": "crash"}

#     # Define a regex pattern to extract the summary values.
#     pattern = (
#         r"test result:\s+(\w+)\.\s+"      # status, e.g. "ok"
#         r"(\d+)\s+passed;\s+"             # number of tests passed
#         r"(\d+)\s+failed;\s+"             # number of tests failed
#         r"(\d+)\s+ignored;\s+"            # number of tests ignored
#         r"(\d+)\s+measured;\s+"           # number of tests measured
#         r"(\d+)\s+filtered out;\s+"       # number of tests filtered out
#         r"finished in\s+([\d\.]+)s"        # total time in seconds
#     )
#     match = re.search(pattern, summary_line)
#     if match:
#         result = {
#             "status": match.group(1),
#             "passed": int(match.group(2)),
#             "failed": int(match.group(3)),
#             "ignored": int(match.group(4)),
#             "measured": int(match.group(5)),
#             "filtered_out": int(match.group(6)),
#             "time_seconds": float(match.group(7))
#         }
#         return result
#     else:
#         print("Failed to parse the summary line for Miri:")
#         print(summary_line)
#         return None

def parse_miri_summary(output_file_path):
    """
    Parses the Miri output file to extract both the test summary and any error messages.
    
    Expected output includes:
      - A test summary line like:
            test result: ok. 9 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 6.96s
      - Error messages (lines starting with "error:") that may follow.
    
    If any error messages are found, this function returns a dictionary with:
         - "status": "crash"
         - "failed": number of error messages found (overriding the summary failed count)
         - "errors": list of error message lines
         - Plus any parsed summary fields (passed, ignored, measured, filtered_out, time_seconds)
    
    If no errors are found, it returns the parsed summary.
    """
    if output_file_path is None:
        return {
                "status": "timeout",
                "passed": 0,
                "failed": 0,
                "ignored": 0,
                "measured": 0,
                "filtered_out": 0,
                "time_seconds": 0.0
            }

    if not os.path.exists(output_file_path):
        print(f"File not found: {output_file_path} (Miri output)")
        return None

    summary_line = None
    error_lines = []

    with open(output_file_path, 'r') as f:
        for line in f:
            clean_line = line.strip().strip('"')
            if "test result:" in clean_line:
                summary_line = clean_line
            if "error:" in clean_line:
                error_lines.append(clean_line)

    # Regex to parse the test summary line.
    summary_pattern = (
        r"test result:\s+(\w+)\.\s+"      # status (e.g., ok)
        r"(\d+)\s+passed;\s+"             # passed count
        r"(\d+)\s+failed;\s+"             # failed count
        r"(\d+)\s+ignored;\s+"            # ignored count
        r"(\d+)\s+measured;\s+"           # measured count
        r"(\d+)\s+filtered out;\s+"       # filtered out count
        r"finished in\s+([\d\.]+)s"        # time in seconds
    )

    summary = {}
    if summary_line:
        match = re.search(summary_pattern, summary_line)
        if match:
            summary = {
                "status": match.group(1),
                "passed": int(match.group(2)),
                "failed": int(match.group(3)),
                "ignored": int(match.group(4)),
                "measured": int(match.group(5)),
                "filtered_out": int(match.group(6)),
                "time_seconds": float(match.group(7))
            }
        else:
            summary = {
                "status": "unknown",
                "passed": 0,
                "failed": 0,
                "ignored": 0,
                "measured": 0,
                "filtered_out": 0,
                "time_seconds": 0.0
            }
    else:
        summary = {
            "status": "unknown",
            "passed": 0,
            "failed": 0,
            "ignored": 0,
            "measured": 0,
            "filtered_out": 0,
            "time_seconds": 0.0
        }

    # If the summary status is not "ok" and error messages exist, override the summary.
    if summary.get("status") != "ok" and error_lines:
        total_failed = 0
        # Pattern to try extracting a number from an error line (optional).
        size_pattern = r"error:\s*(\d+)"
        for err in error_lines:
            size_match = re.search(size_pattern, err)
            if size_match:
                total_failed += int(size_match.group(1))
            else:
                total_failed += 1  # Fallback if no number is found.
        summary["status"] = "crash"
        summary["failed"] = total_failed
        summary["errors"] = error_lines

    return summary


def logger(crate_name: str, version: str, job_id: str):
    '''
    This function will log the results of solidifier in a file.
    '''

    current_directory = os.getcwd()

    os.chdir("helpers")

    data = []

    if not os.path.exists(f"../logs/{job_id}"):
        os.mkdir(f"../logs/{job_id}")

    rustsec_current, rustsec_patched, rustsec_label, rustsec_tag = inRustSec(crate_name, version)
    with open(f"../logs/{job_id}/{crate_name}-{version}.csv", "w", newline='') as file:
        writer = csv.writer(file)
        writer.writerow(["************************************"])
        writer.writerow(["event", "timestamp", "current", "patched", "label" , "tag"])
        writer.writerow(["RustSec", "-", rustsec_current, rustsec_patched, rustsec_label, rustsec_tag])
        data.append({ "event": "RustSec", "timestamp": "-", "current": rustsec_current, "patched": rustsec_patched, "label": rustsec_label, "tag": rustsec_tag})
        # data.append([{ "event": "RustSec", "timestamp": "-", "label": label}])
        writer.writerow(["************************************"])


        _, audit_info = is_audited(crate_name, version)

        writer.writerow(["event", "timestamp", "organization", "type", "criteria", "delta", "version", "notes"])

        entry: dict
        for entry in audit_info:
            writer.writerow([
                entry.get('type', ''),
                "-",
                entry.get('organization', ''),
                entry.get('criteria', ''),
                entry.get('delta', ''),
                entry.get('version', ''),
                entry.get('notes', '').replace('\n', ' '),
                entry.get('points', '')
            ])
            data.append({ "event": entry.get('type', ''), "timestamp": "-", "organization": entry.get('organization', ''), "type": entry.get('criteria', ''), "delta": entry.get('delta', ''), "version": entry.get('version', ''), "notes": entry.get('notes', '').replace('\n', ' ')})
            # data.append(entry)

        writer.writerow(["************************************"])

        author = get_author(crate_name)
        writer.writerow(["event", "timestamp", "name" , "username" , "url"])
        for entry in author:
            writer.writerow([
                "Author",
                "-",
                entry[1],
                entry[2],
                entry[3]
            ])
            data.append({ "event": "Author", "timestamp": "-", "name": entry[1], "username": entry[2], "url": entry[3]})
        writer.writerow(["************************************"])

        # information =  get_stars_and_forks("anyhow")
        information = get_stars_and_forks(crate_name)
        writer.writerow(["event", "timestamp", "stars", "forks" , "watchers"])
        if information != None:
            # print(information)
            writer.writerow(["github_stats" , "-" ,information["stars"], information["forks"], information["watchers"]])
            data.append({ "event": "github_stats", "timestamp": "-", "stars": information["stars"], "forks": information["forks"], "watchers": information["watchers"]})
        else:
            writer.writerow(["github_stats", "-", 0 , 0 ,0 ])
            data.append({ "event": "github_stats", "timestamp": "-", "stars": 0, "forks": 0, "watchers": 0})
        writer.writerow(["************************************"])

        downloads = get_downloads(crate_name)
        writer.writerow(["event", "timestamp", "downloads"])
        writer.writerow([
            "Downloads",
            "-",
            downloads
        ])
        data.append({ "event": "Downloads", "timestamp": "-", "downloads": downloads})
        writer.writerow(["************************************"])
        
        download_crate(crate_name, version)
        extract_and_delete()
        file_name = run_cargo_and_save(crate_name, version)
        total,flagged,unsafe= get_potential_functions(file_name)
        writer.writerow(["event", "timestamp", "total", "flagged"])
        writer.writerow([
            "Side Effects",
            "-",
            total,
            flagged,
            unsafe
        ])
        data.append({ "event": "Side Effects", "timestamp": "-", "total": total, "flagged": flagged , "unsafe": unsafe})
        writer.writerow(["************************************"])
        dependency_tree = build_dependency_tree(crate_name, version)
        writer.writerow(["event", "timestamp", "dependency_tree"])
        writer.writerow([
            "dependency_tree",
            "-",
            dependency_tree
        ])
        data.append({ "event": "dependency_tree", "timestamp": "-", "dependency_tree": dependency_tree})
        writer.writerow(["************************************"])
        writer.writerow(["Rudra", "timestamp",])
        rud = rudra(crate_name , version)
        writer.writerow([
            rud
        ])
        data.append({ "event": "Rudra", "timestamp": "-", "output": rud})
        miri_file = run_miri_and_save(crate_name, version)
        miri = parse_miri_summary(miri_file)
        writer.writerow(["event", "timestamp", "status", "passed", "failed", "ignored", "measured", "filtered_out", "time_seconds"])
        writer.writerow(["Miri","-",miri["status"], miri["passed"], miri["failed"], miri["ignored"], miri["measured"], miri["filtered_out"], miri["time_seconds"]
        ])
        data.append({ "event": "Miri", "timestamp": "-", "status": miri["status"], "passed": miri["passed"], "failed": miri["failed"], "ignored": miri["ignored"], "measured": miri["measured"], "filtered_out": miri["filtered_out"], "time_seconds": miri["time_seconds"]})
        os.chdir(current_directory)
        shutil.rmtree(f"processing/{crate_name}-{version}")

        return data

        '''
        Code below this is for future use.

        '''

        # flag,future = version_audit(audit_info[1], version)
        # # print(same_version_flag)
        # if flag: #means this version has been audited
        #     label = get_labels(audit_info[1])
        #     # print(label)
        # else: #some other version has been audited
        #     '''
        #     this could be future or past
        #     '''
        #     if future:
        #         print("This crate has been audited for a future version.")
        #         last_audit = get_last_audited_version(audit_info[1])
        #         print(f"The last audited version is {last_audit}.")
        #     else:
        #         print("This crate has been audited for a past version.")
        #         last_audit = get_last_audited_version(audit_info[1])
        #         print(f"The last audited version is {last_audit}.")
        #         '''
        #         Now get the repo of the crate and see if the authors have changed or not.
        #         '''
                # repo_analysis(crate_name, version , last_audit)

def rust_sec_logs():
    codex = read_dicts_from_txt("data.txt")
    # print(codex[0])
    pattern = r'(>=|>)?(\d+\.\d+(\.\d+)?)'
    for data in codex:
        # print(dict)
        # data = dict(data)
        # print(data)
        # print(type(data))
        try:  
            data = parse_dict_string(data)
            # print(data)
            temp = data["package"]
            package = temp["name"].split("(")[0]
            # print(package)
            temp = data["patched"]
            versions = list()
            target_version = str()
            if temp == "no patched versions":
                # print("just pick the latest one")
                versions = get_versions(package)
                # print(versions)
                target_version = versions[-1]
                # print(target_version)
                # break
            # print(temp)
            else:
                (_,ver,_) = re.findall(pattern, temp)[0]
                # print(ver)
                versions = get_versions(package)
                if versions == "error":
                    continue
                # print(versions)
                target_version = find_previous_version(ver, versions)
                # print(target_version)

            print(package, target_version)
            logger(package, target_version , "RustSec")
            # exit()
            # download_crate(package,target_version)

            # time.sleep(0.1)
        except Exception as e:
            print(f"An error occurred: {e}")
            with open(f"logs/RustSec/{package}-{target_version}.csv", "w", newline='') as file:
                writer = csv.writer(file)
                writer.writerow(["An error occurred: ", e])
                writer.writerow(["************************************"])
            continue

def get_crate_names(page, per_page):
    url = f'https://crates.io/api/v1/crates?page={page}&per_page={per_page}'
    response = requests.get(url)
    return response.json()['crates']

def get_random_crates(count: int):
    # Get all crate names from a random page
    all_crate_names = []
    per_page = 20
    visited = []

    while len(all_crate_names) < count:
        while(1):
            random_page = random.randint(200, 3000)
            if random_page in visited:
                continue
            visited.append(random_page)
            break
        crates = get_crate_names(random_page, per_page)
        if not crates:
            continue
        all_crate_names.extend([crate['id'] for crate in crates])

    # Randomly select 1000 crate names
    random_crates = random.sample(all_crate_names, count)

    # Function to get the latest version of a crate
    def get_latest_version(crate_name):
        url = f'https://crates.io/api/v1/crates/{crate_name}'
        response = requests.get(url)
        crate_info = response.json()['crate']
        return crate_info['newest_version']

    # Get the latest version of each selected crate
    random_crates_info = [{'name': crate_name, 'latest_version': get_latest_version(crate_name)} for crate_name in random_crates]

    # Write the results to a CSV file
    with open('random_crates.csv', mode='w', newline='') as file:
        writer = csv.DictWriter(file, fieldnames=['name', 'latest_version'])
        writer.writeheader()
        for crate_info in random_crates_info:
            writer.writerow(crate_info)
    
    return 'random_crates.csv'

def random_logs(count):
    print("Starting the random logs...")
    # Get the latest version of a random set of 1000 crates
    # file_path = get_random_crates(count)
    print("Random crates have been selected.")
    # Read the crate names and latest versions from the CSV file
    random_crates = pd.read_csv("random_crates.csv")

    # Log the results for each crate
    print("Logging the results for each crate...")
    for _, row in tqdm(random_crates.iterrows()):
        try:
            crate_name = row['name']
            version = row['latest_version']
            print(f"Logging the results for {crate_name} {version}")
            logger(crate_name, version , "Random500")
            # exit()
        except Exception as e:
            print(f"An error occurred: {e}")
            with open(f"logs/RustSec/{crate_name}-{version}.csv", "w", newline='') as file:
                writer = csv.writer(file)
                writer.writerow(["An error occurred: ", e])
                writer.writerow(["************************************"])
            continue
      
dependency_cache = {}

def get_latest_version(crate_name):
    versions = get_versions(crate_name)
    if versions:
        return versions[-1]  
    else:
        print(f"Could not fetch the latest version for crate {crate_name}.")
        print("This should not happen, please raise an issue on GitHub.")
        sys.exit(1)

def verify_version(crate_name, version):
    """
    Verify if the given version of the crate exists on crates.io.
    """
    versions = get_versions(crate_name)
    if version not in versions:
        print(f"Invalid Version : {version} of crate {crate_name} does not exist.")
        print(f"Available versions are: {versions}")
        print("Please check the version and try again.")
        return False
    return True

def get_dependencies(crate_name, version):
    try:
        url = f'https://crates.io/api/v1/crates/{crate_name}/{version}/dependencies'
        response = requests.get(url)
        return response.json()['dependencies']
    except:
        print(f"Failed to fetch dependencies for {crate_name} version {version}")
        return []

def build_dependency_tree(crate_name, version):
    global dependency_cache
    
    # Check if the dependency tree for this crate is already cached
    if (crate_name,version) in dependency_cache:
        return copy.deepcopy(dependency_cache[(crate_name,version)])
    
    tree = {}
    dependencies = get_dependencies(crate_name, version)
    
    for dep in dependencies:
        # print("working" , dep)
        if dep["kind"] != "normal":  # Only include normal dependencies
            continue
        if dep["optional"]:  # Skip optional dependencies
            continue
        sub_dep_name = dep["crate_id"]
        sub_dep_version = get_latest_version(sub_dep_name)
        
        # Recursively build the dependency tree for this sub-dependency
        tree[(sub_dep_name, sub_dep_version)] = build_dependency_tree(sub_dep_name, sub_dep_version)
    
    # Cache the computed dependency tree for the current crate
    dependency_cache[(crate_name,version)] = copy.deepcopy(tree)
    
    return tree


# logger("tokio", "1.39.3" , "test")
# get_potential_functions("/Users/hassnain/Desktop/RHS/supply-chain-trust/helpers/../experiments/tokio-1.39.3.csv")