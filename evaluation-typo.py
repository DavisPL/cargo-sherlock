import os
import requests
import subprocess
import sys
from tqdm import tqdm
import re

def get_latest_version(crate_name):
    url = f"https://crates.io/api/v1/crates/{crate_name}"
    response = requests.get(url)
    if response.status_code == 200:
        crate_info = response.json()['crate']
        return crate_info['newest_version']
    else:
        print(f"Crate {crate_name} not found on crates.io.")
        return None

def download_crate(crate_name, version, output_dir="cloned_crates"):
    url = f"https://crates.io/api/v1/crates/{crate_name}/{version}/download"
    output_file = os.path.join(output_dir, f"{crate_name}-{version}.tar.gz")

    response = requests.get(url, allow_redirects=True)
    if response.status_code == 200:
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

def main():
    # Generate crate names from supply-chain-trust-example-crate-000000 to -000028
    for i in tqdm(range(1, 100)):
        crate_name = f"supply-chain-trust-example-crate-{i:06d}"
        latest_version = get_latest_version(crate_name)
        
        if latest_version:
            output_path = f"evaluation/typo/{crate_name}_{latest_version}.json"
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
        else:
            print(f"Skipping {crate_name} as it has no available version on crates.io")

if __name__ == "__main__":
    main()
