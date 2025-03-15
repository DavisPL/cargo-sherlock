import os
import requests
import subprocess
import sys
from tqdm import tqdm

# Function to fetch the top 100 most downloaded crates
def fetch_top_crates(limit=100):
    url = f"https://crates.io/api/v1/crates?page=1&per_page={limit}&sort=downloads"
    response = requests.get(url)
    if response.status_code == 200:
        crates = response.json()['crates']
        return [(crate['id'], crate['newest_version']) for crate in crates]
    else:
        print(f"Failed to fetch top crates. Status code: {response.status_code}")
        return []

# Function to download a crate's source code
def download_crate(crate_name, version, output_dir="cloned_crates"):
    url = f"https://crates.io/api/v1/crates/{crate_name}/{version}/download"
    output_file = os.path.join(output_dir, f"{crate_name}-{version}.tar.gz")

    response = requests.get(url, allow_redirects=True)
    if response.status_code == 200:
        os.makedirs(output_dir, exist_ok=True)
        with open(output_file, 'wb') as file:
            file.write(response.content)
        print(f"Downloaded {crate_name} version {version} successfully.")
        
        extracted_dir = os.path.join(output_dir, f"{crate_name}-{version}")
        os.makedirs(extracted_dir, exist_ok=True)
        subprocess.run(["tar", "-xzf", output_file, "-C", extracted_dir, "--strip-components=1"])
        return extracted_dir
    else:
        print(f"Failed to download {crate_name} version {version}. Status code: {response.status_code}")
        return None

# Main function to process the top crates
def main():
    top_crates = fetch_top_crates()

    for crate_name, latest_version in tqdm(top_crates):
        output_path = f"evaluation/top100/{crate_name}_{latest_version}.json"
        if os.path.exists(output_path):
            print(f"Output for {crate_name} version {latest_version} already exists. Skipping.")
            continue

        # Step 1: Download the crate
        crate_dir = download_crate(crate_name, latest_version)
        if not crate_dir:
            print(f"Skipping {crate_name} due to download failure.")
            continue
        
        # Step 2: Run sherlock.py on the downloaded crate and save results in evaluation directory
        try:
            subprocess.run([sys.executable, 'sherlock.py', 'trust', crate_name, latest_version, '-o', output_path])
            print(f"Ran sherlock on {crate_name} version {latest_version} and saved output to {output_path}.")
        except Exception as e:
            print(f"Failed to run sherlock on {crate_name} version {latest_version}: {e}")

if __name__ == "__main__":
    main()
