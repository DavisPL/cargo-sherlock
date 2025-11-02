import os
import csv
import time
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed

CSV_FILE = "random1000_crates.csv"
OUTPUT_HORN_CSV = "random_horn_results.csv"
OUTPUT_NAIVE_CSV = "random_naive_results.csv"
TIMEOUT_SECS = 600  # 10 minutes per crate
MAX_WORKERS = 10


def _process_one(crate_name: str, version: str, base_out_dir: str, naive: bool = False) -> tuple[str, float, int | None]:
    """
    Run sherlock for a single crate@version.
    Returns: (crate-ver, elapsed_seconds, return_code or None if timeout)
    """
    crate_ver = f"{crate_name}-{version}"
    output_file = os.path.join(base_out_dir, crate_ver)
    if naive:
        cmd = ["python3", "sherlock.py", "trust", crate_name, version, "--no-horn", "-o", output_file]
    else:
        cmd = ["python3", "sherlock.py", "trust", crate_name, version, "-o", output_file]

    print(f"[START] {' '.join(cmd)}")
    start = time.perf_counter()
    try:
        proc = subprocess.run(cmd, timeout=TIMEOUT_SECS)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        elapsed = time.perf_counter() - start
        print(f"[TIMEOUT] {crate_ver} after {elapsed:.2f}s")
        return crate_ver, elapsed, None

    elapsed = time.perf_counter() - start
    print(f"[DONE] {crate_ver} in {elapsed:.2f}s (rc={rc})")
    return crate_ver, elapsed, rc


def run_top_crates_horn():
    base_out_dir = os.path.join("evaluation", "rq4")
    os.makedirs(base_out_dir, exist_ok=True)

    # Load all tasks first
    tasks: list[tuple[str, str]] = []
    with open(CSV_FILE, newline="") as in_f:
        reader = csv.DictReader(in_f)
        for row in reader:
            crate_name = row["name"]
            version = row["version"]
            tasks.append((crate_name, version))

    # Open output CSV and write header once
    with open(OUTPUT_HORN_CSV, mode="w", newline="") as out_f:
        writer = csv.writer(out_f)
        writer.writerow(["crate-version", "time_seconds", "return_code"])  # include rc for visibility
        out_f.flush()

        # Execute in a thread pool
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            futures = {
                pool.submit(_process_one, crate, ver, base_out_dir): (crate, ver)
                for crate, ver in tasks
            }

            # Write rows as tasks complete
            for fut in as_completed(futures):
                crate, ver = futures[fut]
                try:
                    crate_ver, elapsed, rc = fut.result()
                except Exception as e:
                    # Unexpected error in worker; log with rc = -1
                    crate_ver = f"{crate}-{ver}"
                    elapsed = 0.0
                    rc = -1
                    print(f"[ERROR] {crate_ver}: {e}")

                writer.writerow([crate_ver, f"{elapsed:.2f}", "" if rc is None else rc])
                out_f.flush()

def run_top_crates_naive():
    base_out_dir = os.path.join("evaluation", "naive", "rq4")
    os.makedirs(base_out_dir, exist_ok=True)

    # Load all tasks first
    tasks: list[tuple[str, str]] = []
    with open(CSV_FILE, newline="") as in_f:
        reader = csv.DictReader(in_f)
        for row in reader:
            crate_name = row["name"]
            version = row["version"]
            tasks.append((crate_name, version))

    # Open output CSV and write header once
    with open(OUTPUT_NAIVE_CSV, mode="w", newline="") as out_f:
        writer = csv.writer(out_f)
        writer.writerow(["crate-version", "time_seconds", "return_code"])  # include rc for visibility
        out_f.flush()

        # Execute in a thread pool
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            futures = {
                pool.submit(_process_one, crate, ver, base_out_dir , True): (crate, ver)
                for crate, ver in tasks
            }

            # Write rows as tasks complete
            for fut in as_completed(futures):
                crate, ver = futures[fut]
                try:
                    crate_ver, elapsed, rc = fut.result()
                except Exception as e:
                    # Unexpected error in worker; log with rc = -1
                    crate_ver = f"{crate}-{ver}"
                    elapsed = 0.0
                    rc = -1
                    print(f"[ERROR] {crate_ver}: {e}")

                writer.writerow([crate_ver, f"{elapsed:.2f}", "" if rc is None else rc])
                out_f.flush()


if __name__ == "__main__":
    run_top_crates_horn()
    run_top_crates_naive()

    # now we need a function to get the number of dependencies for each crate and create a csv

    # we need to make a CDF of time taken 

    # we need to make a plot about time taken vs number of dependencies
