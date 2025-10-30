import os
import subprocess

crates = [
    ("serde_yaml", "0.9.33"),
    ("serde_yml", "0.0.12"),
    ("iter_tools", "0.24.0"),
    ("itertools", "0.14.0")
]

# an output dir to store the results 
output_dir = os.path.join("evaluation", "rq2")
os.makedirs(output_dir, exist_ok=True)

# Iterate over each crate and run the command with the output flag.
for crate_name, version in crates:

    output_file = os.path.join(output_dir, f"{crate_name}-{version}")
    # Build the command string
    command = f"python3 sherlock.py trust {crate_name} {version} -o {output_file}"
    
    print(f"Running: {command}")
    # Run the command
    subprocess.run(command, shell=True)