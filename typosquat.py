import os
import requests
import subprocess
import toml
import shutil

# Constants
CRATES_API_URL = "https://crates.io/api/v1/crates?page=1&per_page=100&sort=downloads"
CRATE_PREFIX = "supply-chain-trust-example-crate-"
TARGET_DIR = "./cloned_crates"
CRATES_IO_TOKEN = os.getenv("CRATES_IO_TOKEN")  # Ensure your token is set as an environment variable

# Function to get top 100 crates
def get_top_crates():
    response = requests.get(CRATES_API_URL)
    if response.status_code == 200:
        return [crate["id"] for crate in response.json().get("crates", [])]
    else:
        print("Failed to fetch top crates.")
        return []

# Function to get GitHub repository URL from Crates.io API
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

    # Update Cargo.toml with new name and author, remove repository and homepage
    with open(cargo_toml_path, "r") as f:
        cargo_data = toml.load(f)

    cargo_data["package"]["name"] = new_name
    cargo_data["package"]["authors"] = ["Hassnain"]
    cargo_data["package"].pop("repository", None)
    cargo_data["package"].pop("homepage", None)

    with open(cargo_toml_path, "w") as f:
        toml.dump(cargo_data, f)

    # Update lib.rs with new crate name using underscores
    lib_rs_path = os.path.join(clone_dir, "src", "lib.rs")
    if os.path.exists(lib_rs_path):
        with open(lib_rs_path, "r") as f:
            lib_rs_content = f.read()

        underscore_name = new_name.replace("-", "_")
        # Replace crate name if it's in the lib.rs file
        if '#![crate_name = "' in lib_rs_content:
            lib_rs_content = lib_rs_content.replace(
                f'#![crate_name = "{crate_name}"]',
                f'#![crate_name = "{underscore_name}"]'
            )
            with open(lib_rs_path, "w") as f:
                f.write(lib_rs_content)

    # Publish to Crates.io
    try:
        subprocess.run(
            ["cargo", "publish", "--token", CRATES_IO_TOKEN, "--allow-dirty"],
            cwd=clone_dir,
            check=True,
        )
        print(f"Published {new_name} successfully.")
    except subprocess.CalledProcessError:
        print(f"Failed to publish {new_name}.")

    # Clean up cloned directory
    shutil.rmtree(clone_dir)

# Main function
def main():
    crates = get_top_crates()
    for i, crate_name in enumerate(crates):
        try:
            new_name = f"{CRATE_PREFIX}{str(i + 1).zfill(6)}"
            # Check if the new crate name already exists on crates.io
            if check_crate_exists(new_name):
                print(f"{new_name} already exists on crates.io. Skipping.")
                continue
            clone_modify_publish(crate_name, new_name)
        except:
            continue
if __name__ == "__main__":
    main()
