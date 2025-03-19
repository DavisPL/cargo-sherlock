# This file contains the functions to get metadata for a given crate or user.
import sys
import ast
import helpers.logger as logger
from typing import NamedTuple, DefaultDict
import csv
from pprint import pprint
import json 
import collections
from collections import defaultdict
from packaging.version import Version, InvalidVersion

User = str
class CrateVersion(NamedTuple):
    """
    Class representing a crate and its version.
    """
    name: str
    version: str
    def __str__(self) -> str:
        return f"{self.name}-{self.version}"

def pretty_print_summary(summary):
    pp = pprint.PrettyPrinter(indent=2)
    pp.pprint(summary)

def get_crate_metadata(crate: CrateVersion) -> dict:
    """
    Returns the metadata for a given crate.
    """
    cache_path = "logs/cache/" + crate.name + "-" + crate.version + ".json"
    try:
        with open(cache_path, "r") as file_backup:
            print("Loading Results for " + crate.name + "-" + crate.version + " from cache...")
            audit_summary: dict = json.load(file_backup)
            audit_summary['dependencies'] = [CrateVersion(dep[0], dep[1]) for dep in audit_summary['dependencies']]
        return audit_summary
    except FileNotFoundError:
        print("Cache file not found, running cargo sherlock on " + crate.name + "-" + crate.version + "...")

    # runs cargo sherlock
    crate_info = logger.logger(crate.name, crate.version, "exp")
    audit_summary = create_audit_summary(crate_info,crate)

    if isinstance(audit_summary, collections.defaultdict):
        audit_summary = dict(audit_summary)

    # save the audit summary to a cache file
    with open(cache_path, "w") as file_backup:
        json.dump(audit_summary, file_backup, indent=2)
    
    return audit_summary
    
def get_user_metadata(user: User) -> dict:
    """
    Returns the metadata for a given user.
    """
    # TODO (future work): Find a way to implement this function
    if user == "dtolnay":
        return {
            "stars": 100,
            "forks": 10
        }
    elif user == "alexcrichton":
        return {
            "stars": 125,
            "forks": 3
        }
    else:
        return {
            "stars": 0,
            "forks": 0
        }
    
def parse_single_file(file: str) -> list:
    csv.field_size_limit(sys.maxsize)
    with open(file, 'r') as f:
        contents = f.read()
        sections = contents.split('************************************')
        result = []
        for section in sections:
            # Remove any leading/trailing whitespace
            section = section.strip()
            if not section:
                continue
            lines = section.splitlines()
            reader = csv.DictReader(lines)
            data = list(reader)
            result.append(data)
    return result

# def create_audit_summary(crate_info: list[list[dict]]):
#     # Initialize the audit summary dictionary using DefaultDict
#     audit_summary = DefaultDict(list)
#     # Iterate over the parsed data to update the dictionary
#     section: list[dict]
#     for section in crate_info:
#         if not section:
#             continue
#         item: dict
#         for item in section:
#             if item.get('event') == 'RustSec':
#                 audit_summary['in_rust_sec'] = item.get('label') != 'Safe'
            
#             elif item.get('event') == 'Author':
#                 audit_summary['developers'].append(item.get('username'))

#             elif item.get('event') == 'github_stats':
#                 audit_summary['stars'] = int(item.get('stars', 0) or 0)
#                 audit_summary['forks'] = int(item.get('forks', 0) or 0)
            
#             elif item.get('event') == 'Downloads':
#                 audit_summary['downloads'] = int(item.get('downloads', 0) or 0)
            
#             elif item.get('event') == 'Side Effects':
#                 audit_summary['num_side_effects'] = int(item.get('total', 0) or 0)

#             elif 'Rudra' in item:
#                 audit_summary['failed_rudra'] = True

#             elif item.get('event') == 'audits':
#                 audit_summary['audits'].append({
#                     'organization': item.get('organization', ''),
#                     'criteria': item.get('criteria', ''),
#                     'delta': item.get('delta', ''),
#                     'notes': item.get('notes', '')
#                 })

#             elif item.get('event') == 'dependency_tree':
#                 if 'dependency_tree' in item:
#                     tree = ast.literal_eval(item.get('dependency_tree'))
#                     flat_tree = {f"{key[0]}-{key[1]}": value for key, value in tree.items()}
#                     dependencies = []
#                     for key, _ in flat_tree.items():
#                         name = "-".join(key.split("-")[:-1])
#                         version = key.split("-")[-1]
#                         cv = CrateVersion(name, version)
#                         dependencies.append(cv)
#                     audit_summary['dependencies'] = dependencies

#     # Set passed_audit to True if there are any audits
#     if audit_summary['audits']:
#         audit_summary['passed_audit'] = True
    
#     return audit_summary

from collections import defaultdict
import ast


def parse_dependency_tree(tree_data):
    dependencies = []
    seen_dependencies = set()  # To keep track of unique dependencies

    def recursive_parse(tree):
        for (crate_name, version), sub_tree in tree.items():
            crate_version = CrateVersion(name=crate_name, version=version)
            # Add to dependencies if not already seen
            if crate_version not in seen_dependencies:
                dependencies.append(crate_version)
                seen_dependencies.add(crate_version)
            # Recursively parse the sub-tree if it's not empty
            if sub_tree:
                recursive_parse(sub_tree)

    # Check if tree_data is already a dictionary or a string
    if isinstance(tree_data, dict):
        recursive_parse(tree_data)
    else:
        # If tree_data is a string, parse it as a dictionary first
        tree_data = eval(tree_data)  # This assumes the string can be safely evaluated
        recursive_parse(tree_data)
    
    return dependencies

def evaluate_audits(audits, current_version):
    """
    Given a list of audit entries and the current version (a string),
    return a tuple (passed_audit, past_audit):
      - passed_audit is True if an audit entry exactly certifies the current version.
      - past_audit is True if any audit entry applies to a version lower than current_version.
    Future (i.e. higher) audit entries are ignored.
    """
    passed_audit = False
    past_audit = False
    curr_ver = Version(current_version)
   
    for audit in audits:
        # Check full audit entries with a "version" field.
        if audit.get('version'):
            try:
                audited_ver = Version(audit['version'])
            except InvalidVersion:
                continue
            if audited_ver == curr_ver:
                passed_audit = True
            elif audited_ver < curr_ver:
                past_audit = True
        # Check delta audit entries, expected in the format "X -> Y"
        elif audit.get('delta'):
            parts = audit['delta'].split("->")
            if len(parts) == 2:
                new_ver_str = parts[1].strip()
                try:
                    new_ver = Version(new_ver_str)
                except InvalidVersion:
                    continue
                if new_ver == curr_ver:
                    passed_audit = True
                elif new_ver < curr_ver:
                    past_audit = True
    return passed_audit, past_audit

def create_audit_summary(crate_info , crate:CrateVersion):
    audit_summary = defaultdict(list)
    audit_summary.update({
        'rustsec_label': None,
        'in_rustsec_patched': False,
        'in_rustsec_current': False,
        'in_rust_sec' : False, #remove this once we add support for new ones
        'developers': [],
        'stars': 0,
        'forks': 0,
        'downloads': 0,
        'num_side_effects': 0,
        'failed_rudra': False,
        'audits': [],
        'dependencies': [],
        'passed_audit': False, 
        'num_unsafe_calls': 0,
        'miri': False,
        'past_audit': False
    })
    for section in crate_info:
        if isinstance(section, list):
            for item in section:
                if item.get('event') == 'Miri':
                    status = item.get('status', 'unknown').lower()
                    if status == "ok":
                        failed = 0
                        audit_summary['miri'] = False
                    else:
                        failed = int(item.get('failed', 0))
                        audit_summary['miri'] = True
                    audit_summary['miri_details'] = {
                        'status': status,
                        'passed': int(item.get('passed', 0)),
                        'failed': failed,
                        'ignored': int(item.get('ignored', 0)),
                        'measured': int(item.get('measured', 0)),
                        'filtered_out': int(item.get('filtered_out', 0)),
                        'time_seconds': float(item.get('time_seconds', 0))
                    }
                elif item.get('event') == 'RustSec':
                    # print(item)
                    # sys.exit(1)
                    audit_summary['in_rustsec_current'] = item.get('current') 
                    audit_summary['in_rustsec_patched'] = item.get('patched')
                    audit_summary['rustsec_label'] = item.get('label')
                            # rustsec_current, rustsec_patched, rustsec_label
                elif item.get('event') == 'Author':
                    audit_summary['developers'].append(item.get('username'))

                elif item.get('event') == 'github_stats':
                    audit_summary['stars'] = int(item.get('stars', 0) or 0)
                    audit_summary['forks'] = int(item.get('forks', 0) or 0)
                
                elif item.get('event') == 'Downloads':
                    audit_summary['downloads'] = int(item.get('downloads', 0) or 0)
                
                elif item.get('event') == 'Side Effects':
                    audit_summary['num_side_effects'] = int(item.get('total', 0) or 0)
                    audit_summary['num_unsafe_calls'] = int(item.get('unsafe', 0) or 0)

                elif 'Rudra' in item:
                    audit_summary['failed_rudra'] = True

                elif item.get('event') == 'audits':
                    # Append audit details to the audits list
                    audit_summary['audits'].append({
                        'organization': item.get('organization', ''),
                        'criteria': item.get('type', ''),  # Correcting the field to match expected criteria
                        'delta': item.get('delta', ''),
                        'version': item.get('version', ''),
                        'notes': item.get('notes', '')
                    })

                elif item.get('event') == 'dependency_tree':
                    tree_data = item.get('dependency_tree')
                    audit_summary['dependencies'] = parse_dependency_tree(tree_data)
        
        elif isinstance(section, dict):
            if section.get('event') == 'Miri':
                status = section.get('status', 'unknown').lower()
                if status == "ok":
                    failed = 0
                    audit_summary['miri'] = False
                else:
                    failed = int(section.get('failed', 0))
                    audit_summary['miri'] = True
                audit_summary['miri_details'] = {
                    'status': status,
                    'passed': int(section.get('passed', 0)),
                    'failed': failed,
                    'ignored': int(section.get('ignored', 0)),
                    'measured': int(section.get('measured', 0)),
                    'filtered_out': int(section.get('filtered_out', 0)),
                    'time_seconds': float(section.get('time_seconds', 0))
                }
            elif section.get('event') == 'RustSec':
                # `print("sec" , section)
                # sys.exit(1)
                audit_summary['in_rustsec_current'] = section.get('current') 
                audit_summary['in_rustsec_patched'] = section.get('patched')
                audit_summary['rustsec_label'] = section.get('label')

            elif section.get('event') == 'Author':
                audit_summary['developers'].append(section.get('username'))

            elif section.get('event') == 'github_stats':
                audit_summary['stars'] = int(section.get('stars', 0) or 0)
                audit_summary['forks'] = int(section.get('forks', 0) or 0)

            elif section.get('event') == 'Downloads':
                audit_summary['downloads'] = int(section.get('downloads', 0) or 0)

            elif section.get('event') == 'Side Effects':
                audit_summary['num_side_effects'] = int(section.get('total', 0) or 0)
                audit_summary['num_unsafe_calls'] = int(section.get('unsafe', 0) or 0)

            elif 'Rudra' in section:
                audit_summary['failed_rudra'] = True

            elif section.get('event') == 'audits':
                # want to check if the current version is audited
                audit_summary['audits'].append({
                    'organization': section.get('organization', ''),
                    'criteria': section.get('type', ''),  # Correcting the field to match expected criteria
                    'delta': section.get('delta', ''),
                    'version': section.get('version', ''),
                    'notes': section.get('notes', '')
                })

            elif section.get('event') == 'dependency_tree':
                tree_data = section.get('dependency_tree')
                audit_summary['dependencies'] = parse_dependency_tree(tree_data)

    # # Set passed_audit to True if there are any audits
    # if audit_summary['audits']:
    #     audit_summary['passed_audit'] = True
    passed, past = evaluate_audits(audit_summary['audits'], crate.version) #todo change this to current_audit and past_audit
    audit_summary['passed_audit'] = passed
    audit_summary['past_audit'] = past

    return audit_summary