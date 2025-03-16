import os
import csv
import requests
import subprocess

CSV_FILE = "top100_crates.csv"
TARGET_DIR = "./typo_crates"
CRATE_PREFIX = "supply-chain-trust-crate-"

def load_top_crates_from_csv():
    crates = []
    with open(CSV_FILE, "r") as file:
        reader = csv.DictReader(file)
        for row in reader:
            crates.append(row["id"])
    return crates

def get_repo_url(crate_name):
    url = f"https://crates.io/api/v1/crates/{crate_name}"
    response = requests.get(url)
    if response.status_code == 200:
        return response.json()['crate'].get('repository')
    return None

def clone_crate(crate_name, new_name):
    repo_url = get_repo_url(crate_name)
    if not repo_url:
        print(f"No repository URL found for {crate_name}. Skipping.")
        return

    target_path = os.path.join(TARGET_DIR, new_name)
    if os.path.exists(target_path):
        print(f"Directory {target_path} already exists. Skipping.")
        return

    os.makedirs(TARGET_DIR, exist_ok=True)
    try:
        print(f"Cloning {crate_name} into {target_path}...")
        subprocess.run(["git", "clone", repo_url, target_path], check=True)
        print(f"Cloned {crate_name} as {new_name}.")
    except subprocess.CalledProcessError:
        print(f"Failed to clone {crate_name}. Please inspect manually.")

def main():
    if not os.path.exists(CSV_FILE):
        print(f"CSV file {CSV_FILE} not found. Please create it with the top crates data.")
        return

    crates = load_top_crates_from_csv()
    for i, crate_name in enumerate(crates):
        new_name = f"{CRATE_PREFIX}{str(i + 1).zfill(6)}"
        clone_crate(crate_name, new_name)

if __name__ == "__main__":
    main()
