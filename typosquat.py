import os
import requests
import subprocess
import toml
import shutil
import csv
import time  # added for rate limiting

CRATES_API_URL = "https://crates.io/api/v1/crates?page=1&per_page=100&sort=downloads"
CRATE_PREFIX = "supply-chain-trust-crate-"
TARGET_DIR = "./cloned_crates"
CRATES_IO_TOKEN = os.getenv("CRATES_IO_TOKEN")
CSV_FILE = "top100_crates.csv"

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

# Function to check if a crate already exists on crates.io
def check_crate_exists(crate_name):
    url = f"https://crates.io/api/v1/crates/{crate_name}"
    response = requests.get(url)
    return response.status_code == 200

# Clone, modify, and publish the crate
def clone_modify_publish(crate_name, new_name):
    if check_crate_exists(new_name):
        print(f"Crate {new_name} already exists on crates.io. Skipping.")
        return

    repo_url = get_repo_url(crate_name)
    if not repo_url:
        print(f"No repository URL found for {crate_name}. Skipping.")
        return

    clone_dir = os.path.join(TARGET_DIR, new_name)
    os.makedirs(TARGET_DIR, exist_ok=True)

    try:
        subprocess.run(["git", "clone", repo_url, clone_dir], check=True)
    except subprocess.CalledProcessError:
        print(f"Failed to clone {crate_name}. Skipping.")
        return

    # Modify Cargo.toml
    cargo_toml_path = os.path.join(clone_dir, "Cargo.toml")
    if not os.path.exists(cargo_toml_path):
        print(f"{cargo_toml_path} not found. Skipping {crate_name}.")
        return

    with open(cargo_toml_path, "r") as f:
        cargo_data = toml.load(f)

    cargo_data["package"]["name"] = new_name
    cargo_data["package"]["authors"] = ["Hassnain"]
    cargo_data["package"].pop("repository", None)
    cargo_data["package"].pop("homepage", None)

    with open(cargo_toml_path, "w") as f:
        toml.dump(cargo_data, f)

    lib_rs_path = os.path.join(clone_dir, "src", "lib.rs")
    if os.path.exists(lib_rs_path):
        with open(lib_rs_path, "r") as f:
            lib_rs_content = f.read()

        underscore_name = new_name.replace("-", "_")
        if f'#![crate_name = "{crate_name}"]' in lib_rs_content:
            lib_rs_content = lib_rs_content.replace(
                f'#![crate_name = "{crate_name}"]',
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
        print(f"Published {new_name} successfully.")
    except subprocess.CalledProcessError:
        print(f"Failed to publish {new_name}.")
    finally:
        # Remove the clone regardless of success/failure so that you don't leave stale clones.
        shutil.rmtree(clone_dir, ignore_errors=True)

def main():
    if os.path.exists(CSV_FILE):
        crates = load_top_crates_from_csv()
    else:
        crates = fetch_and_save_top_crates()

    for i, crate_name in enumerate(crates):
        new_name = f"{CRATE_PREFIX}{str(i + 1).zfill(6)}"
        if check_crate_exists(new_name):
            print(f"{new_name} already exists on crates.io. Skipping.")
            continue
        try:
            clone_modify_publish(crate_name, new_name)
        except Exception as e:
            print(f"Unexpected error with {new_name}: {e}")
        # Wait 60 seconds before processing the next crate.
        print("Waiting 60 seconds before next attempt...")
        time.sleep(60)

if __name__ == "__main__":
    main()
