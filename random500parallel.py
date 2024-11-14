import os
import requests
import subprocess
import sys
import csv
from tqdm import tqdm
from datetime import datetime
import pandas as pd
from concurrent.futures import ProcessPoolExecutor, as_completed

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

def process_crate(crate_name, latest_version):
    output_path = f"evaluation_para/{crate_name}_{latest_version}.json"
    result = [crate_name, latest_version, ""]

    if os.path.exists(output_path):
        print(f"Output for {crate_name} version {latest_version} already exists. Skipping.")
        return result + ["Skipped"]

    crate_dir = download_crate(crate_name, latest_version)
    if not crate_dir:
        print(f"Skipping {crate_name} due to download failure.")
        return result + ["Download failed"]

    start_time = datetime.now()
    try:
        subprocess.run([sys.executable, 'sherlock.py', 'trust', crate_name, latest_version, '-o', output_path], timeout=180)
        duration = (datetime.now() - start_time).total_seconds()
        print(f"Ran sherlock on {crate_name} version {latest_version} and saved output to {output_path}.")
        return result + [duration]
    except subprocess.TimeoutExpired:
        print(f"Timed out running sherlock on {crate_name} version {latest_version}.")
        return result + ["Timed out"]
    except Exception as e:
        print(f"Failed to run sherlock on {crate_name} version {latest_version}: {e}")
        return result + ["Failed"]

def main():
    random_crates = pd.read_csv("random_crates.csv")
    results = []

    with ProcessPoolExecutor(max_workers=5) as executor:
        futures = [
            executor.submit(process_crate, row['name'], row['latest_version']) 
            for _, row in random_crates.iterrows()
        ]

        for future in tqdm(as_completed(futures), total=len(futures)):
            results.append(future.result())

    csv_file = "evaluation_para/timing_results_random.csv"
    os.makedirs(os.path.dirname(csv_file), exist_ok=True)
    with open(csv_file, mode='w', newline='') as file:
        writer = csv.writer(file)
        writer.writerow(["crate_name", "version", "time_taken"])
        writer.writerows(results)

if __name__ == "__main__":
    main()
