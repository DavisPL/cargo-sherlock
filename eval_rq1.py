import os
import csv
import shutil
import subprocess
import requests
import toml
import time
import re

CRATE_PREFIX = "supply-chain-trust-example-crate-"
CSV_FILE = "top100_crates.csv"
LOG_FILE = "prepare_log.txt"
TARGET_DIR = "./local_crates/typo"
OUTPUT_DIR_REAL = os.path.join("evaluation", "rq1", "real")
OUTPUT_DIR_TYPO = os.path.join("evaluation", "rq1", "typo")
RATE_LIMIT_SECONDS = 1.0  # wait between crates.io requests

os.makedirs(OUTPUT_DIR_REAL, exist_ok=True)
os.makedirs(OUTPUT_DIR_TYPO, exist_ok=True)
os.makedirs(TARGET_DIR, exist_ok=True)

TMP_PREFIX = "__tmp__" + CRATE_PREFIX
TMP_PATTERN = re.compile(rf"^__tmp__{re.escape(CRATE_PREFIX)}(\d{{6}})$")

def _load_crate_ids(csv_path: str):
    ids = []
    with open(csv_path, "r", newline="") as f:
        reader = csv.DictReader(f)
        key = "id" if "id" in reader.fieldnames else "name"
        for row in reader:
            ids.append(row[key].strip())
    return ids

def _crates_io_repo_url(crate_name: str):
    time.sleep(RATE_LIMIT_SECONDS)
    url = f"https://crates.io/api/v1/crates/{crate_name}"
    r = requests.get(url)
    if r.status_code == 200:
        return r.json().get("crate", {}).get("repository")
    return None

def _rewrite_cargo_toml(crate_dir: str, original: str, new_name: str):
    cargo_toml = os.path.join(crate_dir, "Cargo.toml")
    if not os.path.exists(cargo_toml):
        raise FileNotFoundError(f"Cargo.toml not found in {crate_dir}")
    with open(cargo_toml, "r", encoding="utf-8") as f:
        data = toml.load(f)
    if "package" not in data:
        raise ValueError("Missing [package] section in Cargo.toml")
    pkg = data["package"]
    pkg["name"] = new_name
    pkg["authors"] = ["Anonymous"]
    pkg.pop("repository", None)
    pkg.pop("homepage", None)
    with open(cargo_toml, "w", encoding="utf-8") as f:
        toml.dump(data, f)
    lib_rs = os.path.join(crate_dir, "src", "lib.rs")
    if os.path.exists(lib_rs):
        try:
            with open(lib_rs, "r", encoding="utf-8") as f:
                content = f.read()
            needle = f'#![crate_name = "{original}"]'
            if needle in content:
                underscore = new_name.replace("-", "_")
                content = content.replace(needle, f'#![crate_name = "{underscore}"]')
                with open(lib_rs, "w", encoding="utf-8") as f:
                    f.write(content)
        except Exception:
            pass

def run_top100_crates(csv_file: str = CSV_FILE, out_dir: str = OUTPUT_DIR_REAL) -> None:
    crates = _load_crate_ids(csv_file)
    for crate_name in crates:
        output_file = os.path.join(out_dir, crate_name)
        os.makedirs(os.path.dirname(output_file), exist_ok=True)
        cmd = ["python3", "sherlock.py", "trust", crate_name, "-o", output_file]
        print(f"Running: {' '.join(cmd)}")
        subprocess.run(cmd, check=False)

def prepare_typo_crates(csv_file: str = CSV_FILE, target_dir: str = TARGET_DIR, log_path: str = LOG_FILE):
    crates = _load_crate_ids(csv_file)
    total = len(crates)
    with open(log_path, "a", encoding="utf-8") as log:
        for i, crate in enumerate(crates, start=1):
            new_name = f"{CRATE_PREFIX}{i:06d}"
            dest_dir = os.path.join(target_dir, new_name)
            tmp_dir = os.path.join(target_dir, f"__tmp__{new_name}")

            if os.path.exists(dest_dir):
                shutil.rmtree(dest_dir, ignore_errors=True)

            repo_url = _crates_io_repo_url(crate)
            if not repo_url:
                msg = f"No repo URL for {crate}"
                print(msg)
                log.write(f"FAIL {i}/{total}: {crate} -> {new_name}: {msg}\n")
                continue

            print(f"[{i}/{total}] Cloning {crate} from {repo_url} into {tmp_dir}...")
            try:
                subprocess.run(["git", "clone", "--depth", "1", repo_url, tmp_dir], check=True)
            except subprocess.CalledProcessError as e:
                msg = f"git clone failed: {e}"
                print(msg)
                log.write(f"FAIL {i}/{total}: {crate} -> {new_name}: {msg}\n")
                # keep tmp_dir for inspection
                continue

            try:
                _rewrite_cargo_toml(tmp_dir, crate, new_name)
                # move finalized tree to dest; remove tmp dir marker
                if os.path.exists(dest_dir):
                    shutil.rmtree(dest_dir, ignore_errors=True)
                shutil.move(tmp_dir, dest_dir)
                print(f"OK  {crate} -> {new_name} at {dest_dir}")
                log.write(f"OK   {i}/{total}: {crate} -> {new_name}\n")
            except Exception as e:
                msg = f"rewrite/move failed: {e}"
                print(msg)
                log.write(f"FAIL {i}/{total}: {crate} -> {new_name}: {msg}\n")
                # keep tmp_dir for inspection
                continue

def _first_extracted_crate_root(path: str):
    # Look for a single subdirectory containing Cargo.toml
    candidates = []
    for entry in os.listdir(path):
        full = os.path.join(path, entry)
        if os.path.isdir(full) and os.path.exists(os.path.join(full, "Cargo.toml")):
            candidates.append(full)
    return candidates[0] if candidates else None

def patch_typo_crates_from_tmp(csv_file: str = CSV_FILE, target_dir: str = TARGET_DIR, log_path: str = LOG_FILE):
    crates = _load_crate_ids(csv_file)
    total = len(crates)
    entries = [d for d in os.listdir(target_dir) if TMP_PATTERN.match(d)]
    if not entries:
        return
    with open(log_path, "a", encoding="utf-8") as log:
        for tmp_name in entries:
            m = TMP_PATTERN.match(tmp_name)
            if not m:
                continue
            idx_str = m.group(1)
            i = int(idx_str)  # 1-based index from the six digits
            if i < 1 or i > len(crates):
                print(f"[patch] index {i} out of range for {tmp_name}")
                log.write(f"PATCH FAIL ?: {tmp_name}: index out of range\n")
                continue
            crate = crates[i - 1]
            final_name = f"{CRATE_PREFIX}{i:06d}"
            tmp_dir = os.path.join(target_dir, tmp_name)
            dest_dir = os.path.join(target_dir, final_name)

            print(f"[patch {i}/{total}] Re-trying via cargo download: {crate} -> {final_name}")

            # Delete existing tmp dir, recreate it empty (as requested)
            shutil.rmtree(tmp_dir, ignore_errors=True)
            os.makedirs(tmp_dir, exist_ok=True)

            try:
                # Download and extract into tmp_dir (creates <crate>-<ver>/...)
                subprocess.run(["cargo", "download", crate, "-x"], cwd=tmp_dir, check=True)
            except subprocess.CalledProcessError as e:
                msg = f"cargo download failed: {e}"
                print(msg)
                log.write(f"PATCH FAIL {i}/{total}: {crate} -> {final_name}: {msg}\n")
                # leave tmp_dir as-is for inspection
                continue

            extracted_root = _first_extracted_crate_root(tmp_dir)
            if not extracted_root:
                msg = "no extracted crate root with Cargo.toml found"
                print(msg)
                log.write(f"PATCH FAIL {i}/{total}: {crate} -> {final_name}: {msg}\n")
                # leave tmp_dir
                continue

            try:
                _rewrite_cargo_toml(extracted_root, crate, final_name)
                if os.path.exists(dest_dir):
                    shutil.rmtree(dest_dir, ignore_errors=True)
                shutil.move(extracted_root, dest_dir)
                # success → remove the empty tmp shell (the __tmp__ name disappears)
                shutil.rmtree(tmp_dir, ignore_errors=True)
                print(f"PATCH OK {crate} -> {final_name} at {dest_dir}")
                log.write(f"PATCH OK {i}/{total}: {crate} -> {final_name}\n")
            except Exception as e:
                msg = f"patch rewrite/move failed: {e}"
                print(msg)
                log.write(f"PATCH FAIL {i}/{total}: {crate} -> {final_name}: {msg}\n")
                # keep tmp_dir

def run_typo_crates(typo_output_dir: str = OUTPUT_DIR_TYPO, target_dir: str = TARGET_DIR) -> None:
    cwd = os.getcwd()
    for i in range(1, 101):
        crate_name = f"{CRATE_PREFIX}{i:06d}"
        crate_path = os.path.join(cwd, target_dir, crate_name)
        output_file = os.path.join(typo_output_dir, crate_name)
        os.makedirs(os.path.dirname(output_file), exist_ok=True)
        cmd = ["python3", "sherlock.py", "trust", crate_name, "--path", crate_path, "-o", output_file]
        print(f"Running: {' '.join(cmd)}")
        subprocess.run(cmd, check=False)

def main():
    run_top100_crates(CSV_FILE, OUTPUT_DIR_REAL)
    prepare_typo_crates(CSV_FILE, TARGET_DIR, LOG_FILE)
    patch_typo_crates_from_tmp(CSV_FILE, TARGET_DIR, LOG_FILE)
    run_typo_crates(OUTPUT_DIR_TYPO, TARGET_DIR)

if __name__ == "__main__":
    main()
