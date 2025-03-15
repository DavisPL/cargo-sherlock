import os
import requests
import subprocess
import sys
import csv
from tqdm import tqdm
from datetime import datetime
import pandas as pd

def download_crate(crate_name, version, output_dir="cloned_crates_random"):
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

def main():
    random_crates = pd.read_csv("random_crates.csv")

    csv_file = "evaluation/timing_results_random.csv"
    os.makedirs(os.path.dirname(csv_file), exist_ok=True)

    # Open the file in append mode and add the header only if the file is empty
    with open(csv_file, mode='a', newline='') as file:
        writer = csv.writer(file)
        if file.tell() == 0:  # Only write header if file is empty
            writer.writerow(["crate_name", "version", "time_taken"])

        for i in tqdm(range(len(random_crates))):
            try:
                crate_name = random_crates['name'][i]
                latest_version = random_crates['latest_version'][i]
                output_path = f"evaluation/{crate_name}_{latest_version}.json"

                if os.path.exists(output_path):
                    print(f"Output for {crate_name} version {latest_version} already exists. Skipping.")
                    continue

                crate_dir = download_crate(crate_name, latest_version)
                if not crate_dir:
                    print(f"Skipping {crate_name} due to download failure.")
                    continue

                start_time = datetime.now()
                try:
                    subprocess.run([sys.executable, 'sherlock.py', 'trust', crate_name, latest_version, '-o', output_path],
                                   timeout=600)
                    end_time = datetime.now()
                    duration = (end_time - start_time).total_seconds()
                    print(f"Ran sherlock on {crate_name} version {latest_version} and saved output to {output_path}.")
                    writer.writerow([crate_name, latest_version, duration])  # Write result immediately
                except subprocess.TimeoutExpired:
                    print(f"Timed out running sherlock on {crate_name} version {latest_version}.")
                    writer.writerow([crate_name, latest_version, "Timed out"])
                except Exception as e:
                    print(f"Failed to run sherlock on {crate_name} version {latest_version}: {e}")
                    writer.writerow([crate_name, latest_version, "Failed"])

            except Exception as e:
                print(f"Failed to fetch crate name and version: {e}")
                continue


if __name__ == "__main__":
    main()
