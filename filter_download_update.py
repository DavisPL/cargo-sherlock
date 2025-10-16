import pandas as pd 
import os
import subprocess
import sys

pattern = "supply-chain-trust-example-crate-"

df = pd.read_csv("downloads_20250601_20250831.csv")

print(df["total_downloads"].mean()) #171.51 

average_downloads = 171.51
directory = "logs/cache/"

files = os.listdir(directory)
pattern = "supply-chain-trust-example-crate-"
relevant_files = sorted([f for f in files if f.startswith(pattern) and f.endswith(".json")])    

# now let's write this as downloads in each json file
for file_name in relevant_files:
    file_path = os.path.join(directory, file_name)
    with open(file_path, 'r') as file:
        content = file.readlines()
    
    with open(file_path, 'w') as file:
        for line in content:
            if '"downloads":' in line:
                # Replace the downloads line with the average downloads
                indent = line[:line.index('"downloads":')]
                line = f'{indent}"downloads": {average_downloads},\n'
            file.write(line)

print("Updated all files with average downloads.")

for i in range(1, 101):
    crate_name = f"supply-chain-trust-example-crate-{i:06d}"
    output_file = os.path.join("evaluation", "rq1", "typo", crate_name)
    command = f"python3 sherlock.py trust {crate_name} -o {output_file}"
    
    print(f"Running command: {command}")
    
    # Execute the command and check for errors.
    result = subprocess.run(command, shell=True)
    if result.returncode != 0:
        print(f"Command for {crate_name} failed with return code {result.returncode}")
        sys.exit(result.returncode)