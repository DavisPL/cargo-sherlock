# This file contains the functions to get metadata for a given crate or user.
import sys
import ast
import logger
from typing import NamedTuple, DefaultDict
import csv

MAX_WEIGHT = 1500

User = str
class CrateVersion(NamedTuple):
    name: str
    version: str
    def __str__(self) -> str:
        return f"{self.name}-{self.version}"

def get_crate_metadata(crate: CrateVersion) -> dict:
    """
    Returns the metadata for a given crate.
    """
    # Runs cargo sherlock
    logger.logger(crate.name, crate.version, "exp")
    crate_info = parse_single_file(f"logs/exp/{crate.name}-{crate.version}.csv")
    audit_summary = create_audit_summary(crate_info)

    import pprint
    pp = pprint.PrettyPrinter(indent=2)
    pp.pprint(audit_summary)

    return audit_summary

def get_user_metadata(user: str) -> dict:
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

def create_audit_summary(crate_info: list[list[dict]]):
    # Initialize the audit summary dictionary using DefaultDict
    audit_summary = DefaultDict(list)
    # Iterate over the parsed data to update the dictionary
    section: list[dict]
    for section in crate_info:
        if not section:
            continue
        item: dict
        for item in section:
            if item.get('event') == 'RustSec':
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

            elif 'Rudra' in item:
                audit_summary['failed_rudra'] = True

            elif item.get('event') == 'audits':
                audit_summary['audits'].append({
                    'organization': item.get('organization', ''),
                    'criteria': item.get('criteria', ''),
                    'delta': item.get('delta', ''),
                    'notes': item.get('notes', '')
                })

            elif item.get('event') == 'dependency_tree':
                if 'dependency_tree' in item:
                    tree = ast.literal_eval(item.get('dependency_tree'))
                    flat_tree = {f"{key[0]}-{key[1]}": value for key, value in tree.items()}
                    dependencies = []
                    for key, _ in flat_tree.items():
                        name = "-".join(key.split("-")[:-1])
                        version = key.split("-")[-1]
                        cv = CrateVersion(name, version)
                        dependencies.append(cv)
                    audit_summary['dependencies'] = dependencies

    # Set passed_audit to True if there are any audits
    if audit_summary['audits']:
        audit_summary['passed_audit'] = True
    
    return audit_summary