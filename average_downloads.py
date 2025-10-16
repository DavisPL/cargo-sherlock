import os
import subprocess
import sys

pattern = "supply-chain-trust-example-crate-"


# this part below gave us the log files for all the crates we had pushed
# output_dir = os.path.join("evaluation", "rq1", "typo")
# os.makedirs(output_dir, exist_ok=True)

# # Iterate over crate numbers 1 to 100
# for i in range(1, 101):
#     crate_name = f"supply-chain-trust-example-crate-{i:06d}"
#     output_file = os.path.join(output_dir, crate_name)
#     command = f"python3 sherlock.py log {crate_name}"
    
#     print(f"Running command: {command}")
    
#     # Execute the command and check for errors.
#     result = subprocess.run(command, shell=True)
#     if result.returncode != 0:
#         print(f"Command for {crate_name} failed with return code {result.returncode}")
#         sys.exit(result.returncode)

# now we get an average of downloads for all the crates we had pushed

directory = "logs/cache/"

files = os.listdir(directory)
pattern = "supply-chain-trust-example-crate-"
relevant_files = sorted([f for f in files if f.startswith(pattern) and f.endswith(".json")])    


# yup we have correct files

# print(f"Found {len(relevant_files)} relevant files.")
# print(f"Files: {relevant_files}")

# with open('dump.txt', 'w') as dump_file:
#     dump_file.write('\n'.join(relevant_files))

# original_downloads = {}
# total_downloads = 0
# for file_name in relevant_files:
#     file_path = os.path.join(directory, file_name)
#     with open(file_path, 'r') as file:
#         content = file.read()
#         try:
#             # Find the line containing "downloads"
#             for line in content.splitlines():
#                 if '"downloads":' in line:
#                     # Extract the number using string manipulation
#                     parts = line.split(':')
#                     if len(parts) == 2:
#                         downloads_str = parts[1].strip().rstrip(',')  # Remove whitespace and trailing comma
#                         downloads = int(downloads_str)
#                         original_downloads[file_name] = downloads
#                         total_downloads += downloads
#                         # print(f"{file_name}: {downloads} downloads")
#         except ValueError as e:
#             print(f"Error processing {file_name}: {e}")

# with open("saving_downloads.txt", 'w') as f:
#     f.write("File Name,Downloads\n")
#     for file_name, downloads in original_downloads.items():
#         f.write(f"{file_name},{downloads}\n")

# average_downloads = total_downloads / len(relevant_files) if relevant_files else 0
# print(f"Average downloads across {len(relevant_files)} crates: {average_downloads}")


# average_downloads = 1479
# now let's write this as downloads in each json file
# for file_name in relevant_files:
#     file_path = os.path.join(directory, file_name)
#     with open(file_path, 'r') as file:
#         content = file.readlines()
    
#     with open(file_path, 'w') as file:
#         for line in content:
#             if '"downloads":' in line:
#                 # Replace the downloads line with the average downloads
#                 indent = line[:line.index('"downloads":')]
#                 line = f'{indent}"downloads": {average_downloads},\n'
#             file.write(line)

# print("Updated all files with average downloads.")

# now let's run the trust command again on all these crates to get updated results
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