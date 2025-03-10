'''
This file is for checking if a crate exists on lib.rs and updating the CSV file with the results.
'''


import csv
import requests
from time import sleep

def check_lib_rs(crate_name):
    """
    Constructs the URL for the crate on lib.rs and checks if it exists.
    Returns "yes" if the page exists (HTTP 200) and "no" otherwise.
    """
    url = f"https://lib.rs/crate/{crate_name}"
    try:
        response = requests.get(url, timeout=10)
        if response.status_code == 200:
            return "yes"
        else:
            return "no"
    except requests.RequestException:
        return "no"

def update_csv(input_csv, output_csv):
    updated_rows = []
    with open(input_csv, newline='', encoding="utf-8") as csvfile:
        reader = csv.DictReader(csvfile)
        # If the CSV already has a "librs" column, it will be updated.
        for row in reader:
            crate_name = row['crate_name']
            # Check if the crate exists on lib.rs
            row['librs'] = check_lib_rs(crate_name)
            updated_rows.append(row)
            sleep(1)
    
    with open(output_csv, 'w', newline='', encoding="utf-8") as csvfile:
        fieldnames = reader.fieldnames
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(updated_rows)

if __name__ == "__main__":
    input_csv = "low_trust_crates.csv"       # Input CSV file with the original data
    output_csv = "low_trust_crates_updated.csv"  # Output CSV with updated 'librs' column
    update_csv(input_csv, output_csv)
    print("CSV file updated with lib.rs check results.")
