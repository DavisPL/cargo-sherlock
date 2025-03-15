import os
import json

# Set the directory path
directory_path = 'evaluation/typo'

for filename in os.listdir(directory_path):
    if filename.endswith('.json'):
        file_path = os.path.join(directory_path, filename)
        
        try:
            with open(file_path, 'r') as file:
                # Read all lines in the file
                lines = file.readlines()
                
                # Check if the file contains exactly one line
                if len(lines) == 1:
                    # Delete the file if it has only one line
                    os.remove(file_path)
                    print(f"Deleted {file_path}")
        
        except Exception as e:
            print(f"Error with file {file_path}: {e}")