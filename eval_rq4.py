import os
import csv
import time
import subprocess

CSV_FILE = "top1000_crates.csv"
OUTPUT_CSV = "random_horn_results.csv"
TIMEOUT_SECS = 600  # 10 minutes per crate


def run_top_crates_horn():
    base_out_dir = os.path.join("evaluation", "rq4")
    os.makedirs(base_out_dir, exist_ok=True)

    # Open output once; write header and then stream results row-by-row
    with open(OUTPUT_CSV, mode="w", newline="") as out_f:
        writer = csv.writer(out_f)
        writer.writerow(["crate-version", "time_seconds"])
        out_f.flush()

        # Iterate input CSV and process each row
        with open(CSV_FILE, newline="") as in_f:
            reader = csv.DictReader(in_f)
            for row in reader:
                crate_name = row["name"]
                version = row["version"]

                crate_ver = f"{crate_name}-{version}"
                output_file = os.path.join(base_out_dir, crate_ver)

                # Build command safely (no shell=True)
                cmd = ["python3", "sherlock.py", "trust", crate_name, version, "-o", output_file]
                print(f"Running: {' '.join(cmd)}")

                start = time.perf_counter()
                try:
                    # Run command (capture return code but don't raise on nonzero)
                    proc = subprocess.run(cmd, timeout=TIMEOUT_SECS)
                    rc = proc.returncode
                except subprocess.TimeoutExpired:
                    # Log timeout as the elapsed time up to now; continue
                    elapsed = time.perf_counter() - start
                    print(f"Timeout after {elapsed:.2f}s for {crate_ver}")
                    writer.writerow([crate_ver, f"{elapsed:.2f}"])
                    out_f.flush()
                    continue

                elapsed = time.perf_counter() - start
                print(f"Finished {crate_ver} in {elapsed:.2f}s (rc={rc})")

                # Write row immediately and flush so progress is saved
                writer.writerow([crate_ver, f"{elapsed:.2f}"])
                out_f.flush()


if __name__ == "__main__":
    run_top_crates_horn()
