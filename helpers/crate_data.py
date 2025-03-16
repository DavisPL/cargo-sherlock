# This file contains the functions to get metadata for a given crate or user.
import sys
import ast
import helpers.logger as logger
from typing import NamedTuple, DefaultDict
import csv

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
    import pprint
    pp = pprint.PrettyPrinter(indent=2)
    pp.pprint(summary)

def get_crate_metadata(crate: CrateVersion) -> dict:
    """
    Returns the metadata for a given crate.
    """
    # Runs cargo sherlock
    crate_info = logger.logger(crate.name, crate.version, "exp")
    # crate_info = parse_single_file(f"logs/exp/{crate.name}-{crate.version}.csv")
    # pretty_print_summary(crate_info)
    audit_summary = create_audit_summary(crate_info)
    # # pretty_print_summary(audit_summary)
    return audit_summary
    # return crate_info

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

def create_audit_summary(crate_info):
    # Initialize the audit summary dictionary using DefaultDict
    audit_summary = defaultdict(list)
    audit_summary.update({
        'in_rust_sec': False,
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
        'miri': False
    })

    # print("In create_audit_summary")
    # print(crate_info)
    # print("_" * 50)
    for section in crate_info:
        if isinstance(section, list):
            for item in section:
                if item.get('event') == 'Miri':
                    status = item.get('status', 'unknown').lower()
                    if status == "crash":
                        # If the summary indicates a crash, do not mark as failed (i.e. keep miri as False)
                        audit_summary['miri'] = False
                        audit_summary['miri_details'] = {
                            'status': "crash",
                            'passed': 0,
                            'failed': 0,
                            'ignored': 0,
                            'measured': 0,
                            'filtered_out': 0,
                            'time_seconds': 0.0
                        }
                    else:
                        print("lol here")
                        sys.exit(1)
                        try:
                            failed = int(item.get('failed', 0))
                        except (ValueError, TypeError):
                            failed = 0
                        # Set miri to True if any test failed or the status is not "ok"
                        audit_summary['miri'] = (failed > 0 or status != 'ok')
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
                    audit_summary['in_rust_sec'] = item.get('label') != 'Safe'
                
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
                if status == "crash":
                    # If the summary indicates a crash, do not mark as failed (i.e. keep miri as False)
                    audit_summary['miri'] = False
                    audit_summary['miri_details'] = {
                        'status': "crash",
                        'passed': 0,
                        'failed': 0,
                        'ignored': 0,
                        'measured': 0,
                        'filtered_out': 0,
                        'time_seconds': 0.0
                    }
                else:
                    print(section)
                    print("kaboom here")
                    sys.exit(1)
                    try:
                        failed = int(section.get('failed', 0))
                    except (ValueError, TypeError):
                        failed = 0
                    # Set miri to True if any test failed or the status is not "ok"
                    audit_summary['miri'] = (failed > 0 or status != 'ok')
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
                audit_summary['in_rust_sec'] = section.get('label') != 'Safe'

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

    # Set passed_audit to True if there are any audits
    if audit_summary['audits']:
        audit_summary['passed_audit'] = True

    return audit_summary