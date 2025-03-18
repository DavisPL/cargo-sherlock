import os
import requests
import subprocess
import shutil
import toml

# Configuration constants.
FAILED_LOG_FILE = "update_log.txt"   # Log file from the original process.
FAILED_DIR = "./failed_crates"         # Directory for cloned failed workspaces.
CRATE_PREFIX = "supply-chain-trust-example-crate-"
CRATES_API_URL_TEMPLATE = "https://crates.io/api/v1/crates/{}"

def get_failed_crates_with_index():
    """
    Reads the log file and returns a list of tuples (index, crate_name)
    for each failed crate.
    Expected log format:
    "Fail X/Y: crate_name failed with error: <error details>"
    where X is the original 1-indexed position.
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

def update_package_manifest(manifest_path, new_name, original_name):
    """
    Updates the package name in a Cargo.toml file located at manifest_path.
    Also updates the crate_name attribute in src/lib.rs if found.
    """
    try:
        with open(manifest_path, "r") as f:
            cargo_data = toml.load(f)
    except Exception as e:
        print(f"Error reading {manifest_path}: {e}")
        return

    if "package" in cargo_data:
        cargo_data["package"]["name"] = new_name
        # Remove repository and homepage fields if desired.
        cargo_data["package"].pop("repository", None)
        cargo_data["package"].pop("homepage", None)
        try:
            with open(manifest_path, "w") as f:
                toml.dump(cargo_data, f)
            print(f"Updated {manifest_path} with new name {new_name}")
        except Exception as e:
            print(f"Error writing {manifest_path}: {e}")

    # Try to update src/lib.rs if it exists and contains the old crate name.
    package_dir = os.path.dirname(manifest_path)
    lib_rs_path = os.path.join(package_dir, "src", "lib.rs")
    if os.path.exists(lib_rs_path):
        try:
            with open(lib_rs_path, "r") as f:
                lib_rs_content = f.read()
            underscore_new = new_name.replace("-", "_")
            if f'#![crate_name = "{original_name}"]' in lib_rs_content:
                lib_rs_content = lib_rs_content.replace(
                    f'#![crate_name = "{original_name}"]',
                    f'#![crate_name = "{underscore_new}"]'
                )
                with open(lib_rs_path, "w") as f:
                    f.write(lib_rs_content)
                print(f"Updated {lib_rs_path} with new crate attribute {underscore_new}")
        except Exception as e:
            print(f"Error updating {lib_rs_path}: {e}")

def find_manifest_for_package(root_dir, package_name):
    """
    Recursively searches for a Cargo.toml file in root_dir whose [package].name matches package_name.
    Returns the full path to the manifest if found; otherwise, returns None.
    """
    for current_root, dirs, files in os.walk(root_dir):
        if "Cargo.toml" in files:
            candidate = os.path.join(current_root, "Cargo.toml")
            try:
                data = toml.load(candidate)
                if "package" in data and data["package"].get("name") == package_name:
                    return candidate
            except Exception as e:
                print(f"Error reading {candidate}: {e}")
    return None

def clone_modify_and_publish(crate_name, new_name):
    """
    Clones the repository for crate_name into FAILED_DIR, updates the desired package manifest
    to use new_name, finds the manifest for that package, and then publishes it using --manifest-path.
    This approach isolates the single package even if the repository is a workspace.
    """
    repo_url = get_repo_url(crate_name)
    if not repo_url:
        print(f"No repository URL found for {crate_name}. Skipping.")
        return

    target_path = os.path.join(FAILED_DIR, new_name)
    # Remove the target_path if it already exists.
    if os.path.exists(target_path):
        shutil.rmtree(target_path)
    os.makedirs(FAILED_DIR, exist_ok=True)

    try:
        subprocess.run(["git", "clone", repo_url, target_path], check=True)
        print(f"Cloned {crate_name} into {target_path}")
    except subprocess.CalledProcessError as e:
        print(f"Failed to clone {crate_name}. Error: {e}")
        return

    # Find the original manifest in the repository.
    orig_manifest = find_manifest_for_package(target_path, crate_name)
    if orig_manifest is None:
        print(f"Could not locate the manifest for {crate_name} in {target_path}.")
        return

    # Update the manifest with the new name.
    update_package_manifest(orig_manifest, new_name, crate_name)

    # Find the updated manifest.
    new_manifest = find_manifest_for_package(target_path, new_name)
    if new_manifest is None:
        print(f"Could not locate the updated manifest for {new_name} in {target_path}.")
        return

    # Convert the manifest path to an absolute path.
    abs_manifest_path = os.path.abspath(new_manifest)
    if not os.path.exists(abs_manifest_path):
        print(f"Manifest path {abs_manifest_path} does not exist.")
        return

    # Publish the crate using its absolute manifest path.
    try:
        print(f"Publishing {new_name} using manifest at {abs_manifest_path}")
        subprocess.run(
            ["cargo", "publish", "--manifest-path", abs_manifest_path, "--allow-dirty"],
            check=True
        )
        print(f"Published {new_name} successfully.")
    except subprocess.CalledProcessError as e:
        print(f"Failed to publish {new_name}. Error: {e}")
    finally:
        # Clean up the cloned repository.
        shutil.rmtree(target_path, ignore_errors=True)

def main():
    failed_crates = get_failed_crates_with_index()
    if not failed_crates:
        print("No failed crates found in the log.")
        return

    # Sort by the original index (optional).
    failed_crates.sort(key=lambda x: x[0])

    print(f"Found {len(failed_crates)} failed workspace(s) to process.")
    for index_number, crate in failed_crates:
        # Use the original index (1-indexed) to form the new name.
        new_name = f"{CRATE_PREFIX}{str(index_number).zfill(6)}"
        print(f"Processing failed workspace for crate: {crate} -> {new_name}")
        clone_modify_and_publish(crate, new_name)

if __name__ == "__main__":
    main()
