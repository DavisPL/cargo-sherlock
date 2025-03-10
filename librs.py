'''
This file is for getting crates with a trust score less than 50 from a given folder
'''

import os
import glob
import csv

def process_file(filepath):
    filename = os.path.basename(filepath)
    if filename.endswith('.json'):
        base = filename[:-5]  # Remove .json extension
    else:
        return None, None, None, None

    # Split on the last underscore to get the crate name and version.
    if '_' in base:
        crate_name, version = base.rsplit('_', 1)
    else:
        crate_name = base
        version = ''

    trust_score = None
    assumptions = []
    in_assumptions = False

    with open(filepath, 'r') as f:
        for line in f:
            stripped = line.strip()
            if stripped.startswith("Trust Score for"):
                # Expected format: "Trust Score for A-Mazed-0.1.0: 34"
                try:
                    trust_score = int(stripped.split(":")[-1].strip())
                except ValueError:
                    trust_score = None
            elif stripped.startswith("Assumptions Made:"):
                in_assumptions = True
            elif in_assumptions:
                # Capture non-empty lines as assumptions.
                if stripped:
                    assumptions.append(stripped)

    # Join all assumption lines into a single string separated by " | "
    assumptions_text = " | ".join(assumptions) if assumptions else ""
    return crate_name, version, trust_score, assumptions_text

def main():
    results = []
    # Get all JSON files in the current directory.
    json_files = glob.glob("data/rustsecVsrandom/random/*.json")
    for filepath in json_files:
        crate_name, version, score, assumptions = process_file(filepath)
        if score is not None and score < 50:
            results.append({
                'crate_name': crate_name,
                'version': version,
                'trust_score': score,
                'assumptions': assumptions
            })

    csv_filename = 'low_trust_crates.csv'
    with open(csv_filename, 'w', newline='') as csvfile:
        fieldnames = ['crate_name', 'version', 'trust_score', 'assumptions']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        for row in results:
            writer.writerow(row)

    print(f"CSV file '{csv_filename}' created with {len(results)} entries.")

if __name__ == "__main__":
    main()
