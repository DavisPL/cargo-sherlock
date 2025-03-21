import os
import csv
import subprocess

# Path to the CSV file
csv_file = "top100_crates.csv"

# Define the output directory
output_dir = os.path.join("evaluation", "rq1", "real")
os.makedirs(output_dir, exist_ok=True)

# Open the CSV file and process each row
with open(csv_file, newline='') as f:
    reader = csv.DictReader(f)
    for row in reader:
        # Assuming both 'id' and 'name' are available; using 'name' here.
        crate_name = row['name']
        # Placeholder for version; replace with actual version when available.
        output_file = os.path.join(output_dir, f"{crate_name}")
        # Build the command string
        command = f"python3 sherlock.py trust {crate_name} -o {output_file}"
        print(f"Running command: {command}")
        # Execute the command
        subprocess.run(command, shell=True)
