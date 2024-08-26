import time
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

def get_github_repo_stats(username, repository, token_file='token.txt'):
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

    # print(url)

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

def get_stars_and_forks(crate_name):
    # Get the repository URL for the crate
    url = f"https://crates.io/api/v1/crates/{crate_name}"
    response = requests.get(url)
    data = response.json()
    repository_url = data['crate']['repository']
    # print("line 58" , repository_url)

    if repository_url == None:
        return None

    regex = r"https:\/\/github\.com\/([^\/]+)\/([^\/]+)";
    match = re.match(regex, repository_url)


    if match:
        username = match.group(1)
        repo_name = match.group(2)
        # print(f"Username: {username}")
        # print(f"Repository Name: {repo_name}")
        return get_github_repo_stats(username, repo_name)
    else:
        # print("No match found for repository URL")
        return None

def read_dicts_from_txt(text_file, separator="\n---\n"):
    with open(text_file, "r") as file:
        content = file.read()
        # Split the content by the separator, and ignore the first empty item if it exists
        dict_strings = [s for s in content.split(separator) if s]
        
    return dict_strings

def parse_dict_string(dict_string):
    # Helper function to convert strings to dictionaries
    def string_to_dict(s):
        try:
            # Convert string representation of dictionary to an actual dictionary
            return json.loads(s.replace("'", '"'))
        except json.JSONDecodeError:
            return s
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

def inRustSec(crate_name, version):
    codex = read_dicts_from_txt("data.txt")
    # print(cod÷ex)
    pattern = r'(>=|>)?(\d+\.\d+(\.\d+)?)'
    for data in codex:
        data = parse_dict_string(data)
        temp = data["package"]
        package = temp["name"].split("(")[0]
        if package == crate_name:
        # print(package)
            temp = data["patched"]
            if temp == "no patched version": # this means that the crate is still vulnerable
                return "Critical"
            else:
                ver = re.findall(pattern, temp)
                # print(data)
                flag, label = bulls_eye(ver, version)
                if label == "Critical" and flag:
                    print("This crate has been flagged by RustSec.")
                    return "Critical"
                if label == "Critical" and not flag:
                    print("This is present in RUST SEC but has been patched. However, you are using a vulnerable version. The patched versions are", ver)
                    return "Critical"
                if label == None and flag:
                    print("This crate has been reported by RustSec but you are using a patched version.")
                    return "Low"
    return "Safe"

def bulls_eye(ver , version):
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
    print("I am comparing", version  , "with" , ver)
    for i in range(0,len(ver)):
        print("I am", i, ver[i])
        (op,v,_) = ver[i]
        if i+1 < len(ver):
            print("next is", i+1 , ver[i+1])
            (op2,v2,_) = ver[i+1]
            print(op2 , v2)
            if op2 == '':
                print("494")
                if version < v2 and version >= v: # this means that the version is in the range of v and v2
                    # print(version , v , v2)÷
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
        with open(f"{file}.toml", "w") as file:
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
    if google cater for ub-risk criteria as well and p[oints based on that?]
    '''
    cargo_vet = get_cargo_vet()
    # print(cargo_vet)
    for org,url in cargo_vet.items():
        get_organization_file(url,org)
    
    organiations = cargo_vet.keys()
    vessel = []
    points = 0
    for org in organiations:
        # org = "google"
        codex = parse_toml_with_type_and_crate(f"{org}.toml")
    # print(codex.keys())
        for type,data in codex.items():
            # print(type)
            temp = {}
            for name,info in data.items():
                if name == crate_name: 
                    if type == 'trusted':
                        for audit in info:
                            temp["organization"] = org
                            temp["type"] = type
                            temp["criteria"] = audit["criteria"]
                            # points+=3
                            temp["points"] = 3
                            # print(f"This crate is written by an author trusted by {org}.")
                            if temp != {}:
                                vessel.append(temp)
                                temp = {}
                                points = 0
                    else:
                        for audit in info:
                            # print(audit)
                            # print(audit)
                            if 'delta' in audit:
                                versions = getVersion(audit["delta"])
                                # print("version : " , versions)
                                if version in versions:
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
                                if version == audit["version"]:
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
                                # temp.append(org)
                                # temp.append(type)
                                # temp.append(audit["criteria"])
                                temp["points"] = points
                                temp["version"] = audit["version"]
                                # temp.append(points)
                                # temp.append(audit["version"])
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

def get_author(crate_name):
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

def get_downloads(crate_name):    
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
    genome = []
    for sequence in codex:
        temp = sequence.split(",")
        temp = [x.strip() for x in temp]
        genome.append(temp)
    return genome

def get_potential_functions(file_path):
    length = 0
    # print("I will read " , full_path)
    try:
        with open(file_path) as csv_file:
            reader = (csv.reader(csv_file))
            for row in reader:
                lines = row[0].split("\n")
                # print(lines)
                lines = remove_before_value(lines, 'crate')
                lines = remove_after_value(lines , 'num_effects')
                lines = formatter(lines)
                df = pd.DataFrame(lines[1:] , columns=lines[0])
                with open("effect_counts.json", "r") as file:
                    loaded_effect_counts = json.load(file)
                    rustsec_effects = loaded_effect_counts.keys()
                    # print("my length is", len(df))
                    length = len(df)
                    # print("df is", df)
                    concerned_df = df[df['effect'].isin(rustsec_effects)]
                    # print("concerned_df is", concerned_df)
                    desired_order = ['dir', 'file', 'line', 'col', 'fn_decl', 'callee', 'effect']
                    # Reorder the DataFrame
                    df_reordered = concerned_df[desired_order]
                    df_reordered.to_csv("dangerous_functions.csv")
                    return len(df), len(concerned_df)
    except FileNotFoundError:
        print(f"File not found: {file_path}")
        return None,None
    except Exception as e:
        print(f"An error occurred: {e}")
        return None,None

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
    # else:
    #     raise Exception(f"Failed to download the crate. Status code: {response.status_code}")

def extract_and_delete():
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
    # print(audit_info)
    last = "0.0.0"
    last = version.parse(last)
    for audit in audit_info:
        if 'version' in audit:
            temp = version.parse(audit["version"])
            if last < temp:
                # print(last, temp)
                last = temp
        if 'delta' in audit:
            start,end = getVersion(audit["delta"])
            end = version.parse(end)
            # print(last , end)
            if last < end:
                # print("in")
                last = end
        # print(last)
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
    print("I am looking for", target)
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

def run_cargo_and_save(crate_name, crate_path):
    original_directory = os.getcwd()
    crate_name = crate_name.replace('-', '_')
    output_file_path = os.path.join(original_directory, f"{crate_name}.csv")

    cargo_scan_directory = os.path.join(original_directory, "cargo-scan")
    os.chdir(cargo_scan_directory)

    command = f'cargo run --bin scan ../{crate_path}'
    # Combine stderr into stdout to capture all output
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

    os.chdir(original_directory)

    with open(output_file_path, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        # writer.writerow(['Directory', 'Output', 'Error'])
        writer.writerow([result.stdout, result.stderr])
    
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
def logger(crate_name, version , job_id):
    '''
    This function will log the results of solidifier in a file.
    '''
    if not os.path.exists(f"logs/{job_id}"):
        os.mkdir(f"logs/{job_id}")

    label = inRustSec(crate_name, version)
    with open(f"logs/{job_id}/{crate_name}-{version}.csv", "w", newline='') as file:
        writer = csv.writer(file)
        writer.writerow(["************************************"])
        writer.writerow(["event", "timestamp", "label"])
        writer.writerow(["RustSec","-", label])
        writer.writerow(["************************************"])


        _,audit_info = is_audited(crate_name, version)

        writer.writerow(["event", "timestamp", "organization", "type", "criteria", "delta", "version", "notes"])

        for entry in audit_info:
                writer.writerow([
                    entry.get('type', ''),
                    "-",
                    label,
                    entry.get('organization', ''),
                    entry.get('criteria', ''),
                    entry.get('delta', ''),
                    entry.get('version', ''),
                    entry.get('notes', '').replace('\n', ' '),
                    entry.get('points', '')
                ])
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
        writer.writerow(["************************************"])

        # information =  get_stars_and_forks("anyhow")
        information = get_stars_and_forks(crate_name)
        writer.writerow(["event", "timestamp", "stars", "forks" , "watchers"])
        if information!=None:
            # print(information)
            writer.writerow(["github_stats" , "-" ,information["stars"], information["forks"], information["watchers"]])
        else:
            writer.writerow(["github_stats", "-", 0 , 0 ,0 ])
        writer.writerow(["************************************"])

        downloads = get_downloads(crate_name)
        writer.writerow(["event", "timestamp", "downloads"])
        writer.writerow([
            "Downloads",
            "-",
            downloads
        ])
        writer.writerow(["************************************"])
        
        download_crate(crate_name, version)
        extract_and_delete()
        file_name = run_cargo_and_save(crate_name, f"{crate_name}-{version}")
        # file_name = f"cargo-scan/{crate_name}-{version}.csv"
        total,flagged = get_potential_functions(file_name)
        writer.writerow(["event", "timestamp", "total", "flagged"])
        writer.writerow([
            "Side Effects",
            "-",
            total,
            flagged
        ])
        # dependencies = get_dependencies_from_toml(f"{crate_name}-{version}")
        # if dependencies:
        #     root_package = list(dependencies.keys())[0]  # Assuming the first package is the root
        #     print("Dependency tree:")
        #     print_dependency_tree(dependencies, root_package)
        # exit()
        writer.writerow(["************************************"])
        writer.writerow(["Rudra", "timestamp",])
        rud = rudra(crate_name , version)
        writer.writerow([
            rud
        ])
        writer.writerow(["************************************"])
        shutil.rmtree(f"{crate_name}-{version}")
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

def get_random_crates(count):
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
      
# random_logs(500)
# logger("anyhow" , "1.0.82" , "exp")
# 
# dependencies = get_dependencies("anyhow", "1.0.82")
# layer1 = []
# for dep in dependencies:
#     print(dep["crate_id"] , dep["req"])
#     layer1.append((dep["crate_id"] , dep["req"]))

# crate_path = "syn-2.0.75"  # Change this to the path of your crate

dependency_cache = {}

def get_latest_version(crate_name):
    url = f'https://crates.io/api/v1/crates/{crate_name}'
    response = requests.get(url)
    crate_info = response.json()['crate']
    return crate_info['newest_version']

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
    # print("Fetching dependencies for", crate_name, version)
    if (crate_name,version) in dependency_cache:
        # print("Using cached dependency tree for", crate_name, version)
        return copy.deepcopy(dependency_cache[(crate_name,version)])
    
    tree = {}
    dependencies = get_dependencies(crate_name, version)
    
    for dep in dependencies:
        if dep["kind"] != "normal":  # Only include normal dependencies
            continue
        if dep["optional"]:  # Skip optional dependencies
            continue
        
        sub_dep_name = dep["crate_id"]
        sub_dep_version = get_latest_version(sub_dep_name)
        # print(f"Fetching dependencies for {sub_dep_name} ({sub_dep_version})")
        
        # Recursively build the dependency tree for this sub-dependency
        tree[sub_dep_name] = build_dependency_tree(sub_dep_name, sub_dep_version)
    
    # Cache the computed dependency tree for the current crate
    dependency_cache[(crate_name,version)] = copy.deepcopy(tree)
    
    return tree

# dependency_cache = {}

# dependency_tree = build_dependency_tree("backtrace", "0.3.54")

# import pprint
# pp = pprint.PrettyPrinter(indent=4)
# pp.pprint(dependency_tree)

# for i in dependency_tree:
#     print(i)