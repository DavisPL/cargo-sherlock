import os
import subprocess

# List of crates with placeholder versions.
crates = [
    ("serde_yaml", "0.9.33"),
    ("serde_yml", "0.0.12"),
    ("iter_tools", "0.24.0"),
    ("itertools", "0.14.0")
]

# Define the output directory structure: evaluation/rq2
output_dir = os.path.join("evaluation", "rq2")
os.makedirs(output_dir, exist_ok=True)

# Iterate over each crate and run the command with the output flag.
for crate_name, version in crates:
    # Construct the output file path (e.g., evaluation/rq2/serde_yaml-VERSION_PLACEHOLDER)
    output_file = os.path.join(output_dir, f"{crate_name}-{version}")
    # Build the command string
    command = f"python3 sherlock.py trust {crate_name} {version} -o {output_file}"
    print(f"Running: {command}")
    # Run the command
    subprocess.run(command, shell=True)
