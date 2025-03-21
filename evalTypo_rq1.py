# import os
# import subprocess

# # Define the output directory and create it if it doesn't exist.
# output_dir = os.path.join("evaluation", "rq1", "typo")
# os.makedirs(output_dir, exist_ok=True)

# # Iterate over crate numbers 1 to 100
# for i in range(1, 101):
#     # Create the crate name with zero-padding to 6 digits (e.g., 000001)
#     crate_name = f"supply-chain-trust-example-crate-{i:06d}"
    
#     # Construct the output file path.
#     output_file = os.path.join(output_dir, crate_name)
    
#     # Build the command.
#     # Note: Since you want to ignore the version, we only pass the crate name.
#     command = f"python3 sherlock.py trust {crate_name} -o {output_file}"
    
#     print(f"Running command: {command}")
    
#     # Execute the command.
#     subprocess.run(command, shell=True)

import os
import subprocess
import sys

# Define the output directory and create it if it doesn't exist.
output_dir = os.path.join("evaluation", "rq1", "typo")
os.makedirs(output_dir, exist_ok=True)

# Iterate over crate numbers 1 to 100
for i in range(1, 101):
    crate_name = f"supply-chain-trust-example-crate-{i:06d}"
    output_file = os.path.join(output_dir, crate_name)
    command = f"python3 sherlock.py trust {crate_name} -o {output_file}"
    
    print(f"Running command: {command}")
    
    # Execute the command and check for errors.
    result = subprocess.run(command, shell=True)
    if result.returncode != 0:
        print(f"Command for {crate_name} failed with return code {result.returncode}")
        sys.exit(result.returncode)
