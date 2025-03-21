import os
import requests
import subprocess
import toml
import shutil
import csv
import time  # used for rate limiting

# Updated crate prefix to match your existing naming convention.
CRATE_PREFIX = "supply-chain-trust-example-crate-"
TARGET_DIR = "./cloned_crates"
CRATES_IO_TOKEN = os.getenv("CRATES_IO_TOKEN")
CSV_FILE = "top100_crates.csv"
LOG_FILE = "update_log.txt"

CRATES_API_URL = "https://crates.io/api/v1/crates?page=1&per_page=100&sort=downloads"

def fetch_and_save_top_crates():
    response = requests.get(CRATES_API_URL)
    if response.status_code == 200:
        crates = response.json().get("crates", [])
        with open(CSV_FILE, mode="w", newline="") as file:
            writer = csv.writer(file)
            writer.writerow(["id", "name"])
            for crate in crates:
                writer.writerow([crate["id"], crate["name"]])
        return [crate["id"] for crate in crates]
    else:
        print("Failed to fetch top crates.")
        return []

def load_top_crates_from_csv():
    crates = []
    with open(CSV_FILE, mode="r") as file:
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

# Checks if a crate with the given name exists on crates.io.
def check_crate_exists(crate_name):
    url = f"https://crates.io/api/v1/crates/{crate_name}"
    response = requests.get(url)
    return response.status_code == 200

# Clone, modify, and publish (or update) the crate.
def clone_modify_publish(original_crate, new_name):
    repo_url = get_repo_url(original_crate)
    if not repo_url:
        print(f"No repository URL found for {original_crate}. Skipping.")
        return

    clone_dir = os.path.join(TARGET_DIR, new_name)
    os.makedirs(TARGET_DIR, exist_ok=True)

    try:
        subprocess.run(["git", "clone", repo_url, clone_dir], check=True)
    except subprocess.CalledProcessError:
        print(f"Failed to clone {original_crate}. Skipping.")
        return

    # Modify Cargo.toml.
    cargo_toml_path = os.path.join(clone_dir, "Cargo.toml")
    if not os.path.exists(cargo_toml_path):
        print(f"{cargo_toml_path} not found. Skipping {original_crate}.")
        return

    with open(cargo_toml_path, "r") as f:
        cargo_data = toml.load(f)

    # Update crate name and authors.
    cargo_data["package"]["name"] = new_name
    cargo_data["package"]["authors"] = ["Hassnain"]
    cargo_data["package"].pop("repository", None)
    cargo_data["package"].pop("homepage", None)

    # If the crate already exists on crates.io, assume you want to update it.
    # Bump the patch version (if version follows x.y.z) for an update.
    if check_crate_exists(new_name):
        current_version = cargo_data["package"].get("version", "0.1.0")
        version_parts = current_version.split(".")
        if len(version_parts) == 3 and version_parts[2].isdigit():
            version_parts[2] = str(int(version_parts[2]) + 1)
            new_version = ".".join(version_parts)
        else:
            new_version = "0.1.0"
        cargo_data["package"]["version"] = new_version

    with open(cargo_toml_path, "w") as f:
        toml.dump(cargo_data, f)

    # Optionally, update the crate name inside src/lib.rs.
    lib_rs_path = os.path.join(clone_dir, "src", "lib.rs")
    if os.path.exists(lib_rs_path):
        with open(lib_rs_path, "r") as f:
            lib_rs_content = f.read()

        underscore_name = new_name.replace("-", "_")
        if f'#![crate_name = "{original_crate}"]' in lib_rs_content:
            lib_rs_content = lib_rs_content.replace(
                f'#![crate_name = "{original_crate}"]',
                f'#![crate_name = "{underscore_name}"]'
            )
            with open(lib_rs_path, "w") as f:
                f.write(lib_rs_content)

    try:
        subprocess.run(
            ["cargo", "publish", "--token", CRATES_IO_TOKEN, "--allow-dirty"],
            cwd=clone_dir,
            check=True,
        )
        print(f"Published/Updated {new_name} successfully.")
    except subprocess.CalledProcessError:
        print(f"Failed to publish/update {new_name}.")
        raise  # Re-raise to be caught in main()
    finally:
        # Clean up the cloned repository.
        shutil.rmtree(clone_dir, ignore_errors=True)

def load_processed_crates():
    processed = set()
    if os.path.exists(LOG_FILE):
        with open(LOG_FILE, "r") as log_file:
            for line in log_file:
                # Expecting lines like:
                # "Processed 14/100: crate_name updated to supply-chain-trust-example-crate-000014"
                # or "Fail 14/100: crate_name failed with error: <error details>"
                if line.startswith("Processed") or line.startswith("Fail"):
                    parts = line.split()
                    # The original crate name is the third token (index 2)
                    if len(parts) > 2:
                        processed.add(parts[2])
    return processed

def main():
    # Read the CSV (or fetch the top crates if CSV not present).
    if os.path.exists(CSV_FILE):
        crates = load_top_crates_from_csv()
    else:
        crates = fetch_and_save_top_crates()

    total = len(crates)
    processed = load_processed_crates()

    # Open a log file to record progress.
    with open(LOG_FILE, "a") as log_file:
        for i, crate_name in enumerate(crates):
            # Build new name using the updated prefix and zero-padded index.
            new_name = f"{CRATE_PREFIX}{str(i + 1).zfill(6)}"
            if crate_name in processed:
                print(f"Skipping already processed crate: {crate_name}")
                continue

            print(f"Processing {i+1}/{total}: {crate_name} -> {new_name}")
            try:
                clone_modify_publish(crate_name, new_name)
                log_line = f"Processed {i+1}/{total}: {crate_name} updated to {new_name}\n"
                log_file.write(log_line)
                print(log_line.strip())
            except Exception as e:
                log_line = f"Fail {i+1}/{total}: {crate_name} failed with error: {e}\n"
                log_file.write(log_line)
                print(log_line.strip())
            # Wait 60 seconds before processing the next crate.
            print("Waiting 60 seconds before next attempt...")
            time.sleep(60)

if __name__ == "__main__":
    main()
