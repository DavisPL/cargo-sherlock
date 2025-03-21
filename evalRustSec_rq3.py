import os
import re
import json
import subprocess
import concurrent.futures
import requests
from packaging import version
from typing import Union

# --- Existing helper functions ---

def read_dicts_from_txt(text_file, separator="\n---\n") -> list[str]:
    """
    Reads a text file containing multiple dictionary entries separated by a delimiter.
    """
    with open(text_file, "r") as file:
        content = file.read()
    dict_strings = [s for s in content.split(separator) if s.strip()]
    return dict_strings

def parse_dict_string(dict_string: str) -> dict:
    """
    Converts a string representation of a dictionary (with keys and values on separate lines)
    into an actual Python dictionary.
    """
    def string_to_dict(s: str) -> Union[dict, str]:
        try:
            return json.loads(s.replace("'", '"'))
        except json.JSONDecodeError:
            return s

    kv_pattern = re.compile(r"(\w+):\s*(.+)")
    result_dict = {}
    
    for line in dict_string.split('\n'):
        line = line.strip()
        if not line:
            continue
        match = kv_pattern.match(line)
        if match:
            key, value = match.groups()
            if value.startswith('{') or value.startswith('['):
                result_dict[key] = string_to_dict(value)
            else:
                result_dict[key] = value
    return result_dict

def is_vulnerable(crate_version: str, patched_info: str) -> bool:
    """
    Determines if a given crate_version is vulnerable based on a generic patched_info string.
    
    Two cases are supported:
      1. If patched_info starts with '^', it is treated as a compound expression.
         In that case we extract all version thresholds from the string and, for each,
         if the threshold's major version matches the crate_version's major version, we
         compare crate_version against that threshold.
      2. Otherwise, patched_info is assumed to be a simple expression (e.g. ">=3.7.2"),
         and the version is vulnerable if it is less than the threshold.
         
    If patched_info is "no patched versions", it always returns True.
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

# --- Provided helper function to query crates.io ---

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

# --- New helper functions for candidate selection ---

def get_candidate_version_from_available(crate_name: str, threshold_str: str) -> Union[str, None]:
    """
    Query crates.io for available versions of the crate and return the highest version
    that is strictly less than the given threshold_str.
    """
    available_versions = get_versions(crate_name)
    if available_versions == "error" or not available_versions:
        print(f"Error fetching versions for {crate_name}")
        return None
    threshold_version = version.parse(threshold_str)
    candidate_versions = [version.parse(v) for v in available_versions if version.parse(v) < threshold_version]
    if not candidate_versions:
        return None
    best_candidate = max(candidate_versions)
    return str(best_candidate)

def get_vulnerable_candidate_version(crate_name: str) -> Union[str, None]:
    """
    For the given crate_name, iterate over all advisories from rustsec (data.txt)
    and collect candidate vulnerable versions computed from the patched_info field.
    
    For patched_info that provides a threshold version, query crates.io for available versions,
    then pick the highest available version that is strictly less than the threshold.
    If patched_info is "no patched versions", the provided advisory version is used.
    
    If no candidate version can be determined from patched info, fall back to the latest version
    available on crates.io.
    
    Finally, return the highest candidate version (i.e. the latest vulnerable version)
    as a string, or None if no candidate is found.
    """
    dict_strings = read_dicts_from_txt("helpers/data.txt")
    candidate_versions = []
    
    for data in dict_strings:
        record = parse_dict_string(data)
        package = record.get("package", {}).get("name", "").split("(")[0]
        if package != crate_name:
            continue
        
        patched_info = record.get("patched", "")
        if patched_info:
            if patched_info == "no patched versions":
                candidate = record.get("version")
                if candidate:
                    candidate_versions.append(candidate)
            else:
                match = re.search(r'(\d+\.\d+\.\d+)', patched_info)
                if match:
                    threshold_str = match.group(1)
                    candidate = get_candidate_version_from_available(crate_name, threshold_str)
                    if candidate:
                        candidate_versions.append(candidate)
    
    # Fallback: if no candidate version was derived from patched info, use the latest version.
    if not candidate_versions:
        available_versions = get_versions(crate_name)
        if available_versions != "error" and available_versions:
            candidate_versions.append(available_versions[-1])
    
    try:
        parsed_candidates = [version.parse(v) for v in candidate_versions if v is not None]
        max_candidate = max(parsed_candidates)
        return str(max_candidate)
    except Exception as e:
        print(f"Error computing max candidate for {crate_name}: {e}")
        return None

# --- Main loop: run the tool on vulnerable versions of rustsec crates using one loop ---

def run_sherlock_on_vulnerable_rustsec_crates():
    """
    Iterate over the advisory records in data.txt. For each unique crate encountered,
    determine a candidate vulnerable version based on advisories (or fallback to the latest version).
    Then run the tool (sherlock.py) on that crate and version, storing the output in
    evaluation/rq3/rustsec with filename <crate_name>-<version>.
    
    This version uses a single loop to process unique crates concurrently using a thread pool with 5 threads.
    """
    dict_strings = read_dicts_from_txt("helpers/data.txt")
    output_dir = os.path.join("evaluation", "rq3", "rustsec")
    os.makedirs(output_dir, exist_ok=True)
    
    processed = set()
    
    def process_crate(crate_name):
        candidate_version = get_vulnerable_candidate_version(crate_name)
        if candidate_version is None:
            print(f"Skipping {crate_name}: no candidate vulnerable version found.")
            return
        output_file = os.path.join(output_dir, f"{crate_name}-{candidate_version}")
        command = f"python3 sherlock.py trust {crate_name} {candidate_version} -o {output_file}"
        print(f"Running: {command}")
        result = subprocess.run(command, shell=True)
        if result.returncode != 0:
            print(f"Command for {crate_name} failed with return code {result.returncode}")
    
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
        for data in dict_strings:
            record = parse_dict_string(data)
            crate = record.get("package", {}).get("name", "").split("(")[0]
            if crate and crate not in processed:
                processed.add(crate)
                executor.submit(process_crate, crate)

if __name__ == "__main__":
    run_sherlock_on_vulnerable_rustsec_crates()
