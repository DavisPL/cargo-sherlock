import os
import csv
import math
import random
import subprocess
import requests
import re
import concurrent.futures
import time

CSV_FILE = "random1000_crates.csv"
version_regex = re.compile(r"^(v)?\d+\.\d+\.\d+$")

def sample_crates():
    """
    Query the crates.io API to randomly sample 1000 unique crates.
    Only crates whose latest version is numeric (valid semver) are kept.
    Saves the sampled crates (name and version) into a CSV file.
    """
    if os.path.exists(CSV_FILE):
        print(f"{CSV_FILE} already exists. Skipping API queries.")
        return CSV_FILE

    # First, determine the total number of crates available.
    url = "https://crates.io/api/v1/crates?page=1&per_page=1"
    response = requests.get(url)
    response.raise_for_status()
    data = response.json()
    total_crates = data["meta"]["total"]
    per_page = 20
    max_page = math.ceil(total_crates / per_page)
    print(f"Total crates: {total_crates}, max_page: {max_page}")

    crates_set = {}
    # Keep querying until we have 1000 unique crates that have a numeric version.
    while len(crates_set) < 1000:
        page = random.randint(1, max_page)
        url = f"https://crates.io/api/v1/crates?page={page}&per_page={per_page}"
        try:
            response = requests.get(url)
            response.raise_for_status()
        except Exception as e:
            print(f"Error querying page {page}: {e}")
            continue

        data = response.json()
        for crate in data.get("crates", []):
            name = crate.get("name")
            version = crate.get("max_version")
            # Only keep crates with a version matching our numeric semver regex.
            if name and version and version_regex.match(version):
                crates_set[name] = version
            if len(crates_set) >= 1000:
                break
        print(f"Collected {len(crates_set)} unique crates so far...")

    # Write the sampled crates to CSV.
    with open(CSV_FILE, "w", newline="") as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(["name", "version"])
        for name, version in crates_set.items():
            writer.writerow([name, version])
    print(f"Saved {len(crates_set)} crates to {CSV_FILE}")
    return CSV_FILE

def run_sherlock_on_crates(csv_file):
    """
    Reads the CSV file of crates and runs the sherlock.py tool on each crate only if the
    output file already exists. The command execution is given a 10 minute timeout.
    The elapsed time for each command is measured and logged in a CSV file.
    
    Output files are saved under evaluation/rq3 with filenames in the format: <crate_name>-<version>
    The log file 'execution_log.csv' will have columns: crate_name, version, time_taken.
    """
    output_dir = os.path.join("evaluation", "rq3")
    os.makedirs(output_dir, exist_ok=True)

    with open(csv_file, newline="") as f:
        reader = list(csv.DictReader(f))
    
    results = []  # Will store tuples: (crate_name, version, time_taken in seconds)

    def process_row(row):
        crate_name = row["name"]
        version = row["version"]
        output_file = os.path.join(output_dir, f"{crate_name}-{version}")
        # Only run the command if the output file already exists.
        if not os.path.exists(output_file):
            print(f"Output file {output_file} does not exist. Skipping {crate_name}-{version}.")
            return None

        command = f"python3 sherlock.py trust {crate_name} {version} -o {output_file} --no-horn"
        print(f"Running: {command}")
        start_time = time.perf_counter()
        try:
            subprocess.run(command, shell=True, check=True, timeout=600)
            print(f"Command for {crate_name} completed successfully.")
        except subprocess.TimeoutExpired:
            print(f"Command for {crate_name} timed out after 10 minutes.")
        except Exception as e:
            print(f"Error processing {crate_name}: {e}")
        end_time = time.perf_counter()
        time_taken = end_time - start_time
        return (crate_name, version, time_taken)

    # Use a thread pool to run commands concurrently.
    with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
        futures = [executor.submit(process_row, row) for row in reader]
        for future in concurrent.futures.as_completed(futures):
            try:
                res = future.result()
                if res is not None:
                    results.append(res)
            except Exception as e:
                print(f"Thread encountered an exception: {e}")

    # Write the log file with execution times.
    log_file = "execution_timeHorn.csv"
    with open(log_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["crate_name", "version", "time_taken"])
        for row in results:
            writer.writerow(row)
    print(f"Logged execution times for {len(results)} commands in {log_file}.")

if __name__ == "__main__":
    csv_file = sample_crates()
    run_sherlock_on_crates(csv_file)
