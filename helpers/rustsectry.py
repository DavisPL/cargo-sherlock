import re
import json
from packaging import version

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
      - in_pathed_rustsec: True if the crate is found and every advisory indicates the version is patched.
      - label: Overall label, using the advisory's "classification" (or "Critical" if not provided)
               for vulnerable advisories; if all advisories mark as patched, returns "Patched". 
               If no advisory is found, returns "Safe".
    """
    codex = read_dicts_from_txt("data.txt")
    vulnerable_labels = []  # To collect labels from vulnerable advisories.
    patched_count = 0       # Number of advisories that consider the version patched.
    total = 0               # Total advisories for this crate.
    
    for data in codex:
        record = parse_dict_string(data)
        package = record.get("package", {}).get("name", "").split("(")[0]
        if package == crate_name:
            total += 1
            patched_info = record.get("patched", "")
            classification = record.get("classification", None)
            if patched_info == "no patched version" or is_vulnerable(crate_version, patched_info):
                vuln_label = classification if classification is not None else "Critical"
                vulnerable_labels.append(vuln_label)
            else:
                patched_count += 1
    
    if total == 0:
        return False, False, "Safe"
    
    if vulnerable_labels:
        unique_labels = list(set(vulnerable_labels))
        overall_label = unique_labels[0] if len(unique_labels) == 1 else unique_labels
        return True, False, overall_label
    else:
        return False, True, "Patched"

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

def worst_label(labels: list[str] | str) -> str:
    """
    Determines the highest severity label from a list of labels.
    """
    if isinstance(labels, str):
        return labels
    severity_order = {
        "Safe": 0,
        "Patched": 1,
        "Uncategorized": 2,
        "LOW": 3,
        "MEDIUM": 4,
        "HIGH": 5,
        "CRITICAL": 6
    }
    worst = "Safe"
    for label in labels:
        if severity_order[label] > severity_order[worst]:
            worst = label
    return worst

if __name__ == '__main__':
    # For example, for the "protobuf" crate:
    #   - One advisory might specify patched: ">=3.7.2" (simple expression)
    #   - Another might use a compound expression like "^1.7.5>=2.6.0"
    # If you pass a version "3.7.1", then the generic logic will mark it as vulnerable
    # if any matching advisory indicates so.
    in_rusrsec, in_pathcec_riustsec, label = inRustSec("abomonation", "0.7.3")
    print("in_rustsec:", in_rusrsec)
    print("in_patched_rustsec:", in_pathcec_riustsec)
    print("label:", label)
