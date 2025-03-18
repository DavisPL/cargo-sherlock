import os
import requests
import subprocess
import shutil
import toml

# Configuration constants.
FAILED_LOG_FILE = "update_log.txt"   # Log file from the original process.
FAILED_DIR = "./failed_crates"         # Directory for cloned failed crates.
CRATE_PREFIX = "supply-chain-trust-example-crate-"
CRATES_API_URL_TEMPLATE = "https://crates.io/api/v1/crates/{}"

def get_failed_crates_with_index():
    """
    Reads the log file and returns a list of tuples (index, crate_name)
    for each failed crate. Expected log format is:
    "Fail X/Y: crate_name failed with error: <error details>"
    where X is the original 1-indexed position of the crate.
    """
    failed = []
    if os.path.exists(FAILED_LOG_FILE):
        with open(FAILED_LOG_FILE, "r") as log_file:
            for line in log_file:
                if line.startswith("Fail"):
                    parts = line.split()
                    if len(parts) > 2:
                        # parts[1] is in the form "X/Y:"; extract X.
                        index_token = parts[1]
                        index_str = index_token.split("/")[0]
                        try:
                            index_number = int(index_str)
                        except ValueError:
                            continue
                        crate_name = parts[2]
                        failed.append((index_number, crate_name))
    return failed

def get_repo_url(crate_name):
    """
    Fetches the repository URL for a given crate from crates.io.
    """
    url = CRATES_API_URL_TEMPLATE.format(crate_name)
    response = requests.get(url)
    if response.status_code == 200:
        return response.json()['crate'].get('repository')
    return None

def clone_and_rename(crate_name, new_name):
    """
    Clones the crate's repository into FAILED_DIR using new_name as the folder name,
    and updates Cargo.toml and src/lib.rs (if they exist) to use the new crate name.
    """
    repo_url = get_repo_url(crate_name)
    if not repo_url:
        print(f"No repository URL found for {crate_name}. Skipping.")
        return

    target_path = os.path.join(FAILED_DIR, new_name)
    # Remove target_path if it already exists.
    if os.path.exists(target_path):
        shutil.rmtree(target_path)
    os.makedirs(FAILED_DIR, exist_ok=True)

    try:
        subprocess.run(["git", "clone", repo_url, target_path], check=True)
        print(f"Cloned {crate_name} into {target_path}")
    except subprocess.CalledProcessError as e:
        print(f"Failed to clone {crate_name}. Error: {e}")
        return

    # Update Cargo.toml's package name if the file exists.
    cargo_toml_path = os.path.join(target_path, "Cargo.toml")
    if os.path.exists(cargo_toml_path):
        try:
            with open(cargo_toml_path, "r") as f:
                cargo_data = toml.load(f)
            if "package" in cargo_data:
                cargo_data["package"]["name"] = new_name
                with open(cargo_toml_path, "w") as f:
                    toml.dump(cargo_data, f)
                print(f"Updated Cargo.toml for {new_name}")
        except Exception as e:
            print(f"Error updating Cargo.toml for {new_name}: {e}")

    # Optionally update src/lib.rs if it contains the crate_name attribute.
    lib_rs_path = os.path.join(target_path, "src", "lib.rs")
    if os.path.exists(lib_rs_path):
        try:
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
                print(f"Updated lib.rs for {new_name}")
        except Exception as e:
            print(f"Error updating lib.rs for {new_name}: {e}")

def main():
    failed_crates = get_failed_crates_with_index()
    if not failed_crates:
        print("No failed crates found in the log.")
        return

    # Sort by the original index (optional)
    failed_crates.sort(key=lambda x: x[0])

    print(f"Found {len(failed_crates)} failed crate(s) to download and rename.")
    for index_number, crate in failed_crates:
        # Use the original 1-indexed number to form the new name.
        new_name = f"{CRATE_PREFIX}{str(index_number).zfill(6)}"
        print(f"Processing failed crate: {crate} -> {new_name}")
        clone_and_rename(crate, new_name)

if __name__ == "__main__":
    main()
