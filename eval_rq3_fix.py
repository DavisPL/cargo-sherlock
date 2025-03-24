import os
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed

# Configuration
invalid_file = "invalid_reports.txt"
output_dir = "evaluation/rq3/random1000"  # Base directory for output
num_threads = 10

# Ensure the output directory exists.
os.makedirs(output_dir, exist_ok=True)

# Regular expression to split the crate name and version.
# Expects the version to follow the last '-' (e.g., "crate-name-0.1.2").
pattern = re.compile(r"^(.*)-(\d+\.\d+\.\d+)$")

def process_line(line):
    try:
        line = line.strip()
        if not line:
            return None

        # Match the expected pattern.
        match = pattern.match(line)
        if not match:
            print(f"Skipping invalid format: {line}")
            return None

        crate_name = match.group(1)
        version = match.group(2)

        # Construct the output file path.
        output_path = os.path.join(output_dir, f"{crate_name}-{version}")

        # Construct the command.
        command = f"python3 sherlock.py trust {crate_name} {version} -o {output_path}"
        print("Executing:", command)

        # Execute the command.
        subprocess.run(command, shell=True, check=True)
        return f"Success: {crate_name}-{version}"
    except Exception as e:
        error_msg = f"Error processing line '{line}': {e}"
        print(error_msg)
        return error_msg

# Read all lines from the invalid_reports.txt file.
with open(invalid_file, "r") as f:
    lines = f.readlines()

# Process lines concurrently using 10 threads.
results = []
with ThreadPoolExecutor(max_workers=num_threads) as executor:
    future_to_line = {executor.submit(process_line, line): line for line in lines}
    for future in as_completed(future_to_line):
        try:
            res = future.result()
            if res is not None:
                results.append(res)
        except Exception as e:
            print(f"Unhandled exception: {e}")

# Optionally, print the results summary.
print("Processing complete. Summary:")
for r in results:
    print(r)
