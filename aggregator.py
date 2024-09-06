import re
import os
from collections import defaultdict
import csv
import sys
import pandas as pd
import json

text_file_path = 'helpers/data.txt'

directory = 'processing/rustsec'

csv.field_size_limit(sys.maxsize)

# Function to read the text file and extract package names and affected functions
def extract_info_from_text_file(file_path):
    with open(file_path, 'r') as file:
        text = file.read()

    # Extract package names
    package_info_matches = re.findall(r"package: {'name': '([^']+)'", text)
    cleaned_package_names = [re.sub(r'\(.*\)', '', name).replace('-', '_') for name in package_info_matches]

    # Extract affected functions
    affected_functions = re.findall(r'affected_functions: (.+)', text)
    # Splitting by ',' assuming multiple affected functions could be listed in one line
    affected_functions_list = [func.strip() for sublist in affected_functions for func in sublist.split(',')]

    return cleaned_package_names, affected_functions_list

# Extract package names and affected functions from the text file
package_names, affected_functions = extract_info_from_text_file(text_file_path)
affected_functions = [x.replace(";;", "::") for x in affected_functions]

# Debug: Print the cleaned package names, affected functions, and file patterns
# print("Cleaned Package Names:")
# for name in package_names:
#     print(name)

# print("\nAffected Functions:")
# for function in affected_functions:
#     print(function)

files = os.listdir(directory)
csv_files = [file for file in files if ".csv" in file]
# print(csv_files)

def exists(name):
    targets = []
    for file in csv_files:
        if file.startswith(name):
            # print("here")
            # print(name , file)
            targets.append(file)
    return targets

def remove_after_value(list_of_lists, value):
    # Find the index where the value is found
    index_to_cut = None
    for i, sublist in enumerate(list_of_lists):
        if value in sublist:
            index_to_cut = i
            break
    
    if index_to_cut is not None:
        return list_of_lists[:index_to_cut-1]
    else:
        return list_of_lists 

def formatter(codex):
    formatted_data = []
    for sequence in codex:
        split_list = re.split(r'(?<!\\),', str(sequence))
        split_list = [item.replace('\\,', ',') for item in split_list]
        split_list = [x.strip() for x in split_list]
        formatted_data.append(split_list)
    return formatted_data

def clean_row(row):
    '''
    Input : ["['crate", 'fn_decl', 'callee', 'effect', 'dir', 'file', 'line', "col']"]
    output : ['crate", 'fn_decl', 'callee', 'effect', 'dir', 'file', 'line', "col']
    '''
    row_str = ','.join(row)
    row_str = row_str.lstrip("['").rstrip("']")
    cleaned_row = re.split(r'(?<!\\),', row_str)
    cleaned_row = [item.strip().strip("'\"") for item in cleaned_row]
    return cleaned_row


def searcher(affected_functions, crate_name , functions):
    name = list(crate_name)[0]
    # print(name)
    target_functions = [x for x in affected_functions if x.startswith(name)]
    # print("here")
    return target_functions

def count_elements(lst):
    counts = {}  # Create an empty dictionary to store the counts
    for element in lst:
        if element in counts:
            counts[element] += 1  # Increment count if element already in dictionary
        else:
            counts[element] = 1  # Initialize count if element not in dictionary yet
    return counts

# Function to check each CSV file for affected functions and tally the effects
def tally_effects_in_files(files, affected_functions):
    effect_counts = defaultdict(int)  # Dictionary to store effect counts
    
    for file in files:
        file_path = os.path.join(directory, file)
        print(f"Checking file: {file_path}")
        try:
            with open(file_path) as csv_file:
                reader = list(csv.reader(csv_file))
                reader = remove_after_value(reader , "num_effects")
                # print(reader)
                lines = reader[2:-3] # removing the first two and last three lines
                # print(lines)
            formatted_lines = formatter(lines)
            formatted_lines = [clean_row(row) for row in formatted_lines]
            df = pd.DataFrame(formatted_lines[1:] , columns=formatted_lines[0])
            print(df)
            target = searcher(affected_functions , df['crate'] , df['fn_decl'])
            df['fn_decl_lower'] = df['fn_decl'].str.lower()
            # Convert the target list to lowercase
            target_lower = [item.lower() for item in target]
            # Apply the filter using the lowercase column and modified target list
            concerned_df = df[df['fn_decl_lower'].isin(target_lower)]
            # print(concerned_df)
            if not concerned_df.empty:
                for effect in concerned_df["effect"]:
                    effect_counts[effect] += 1
            # print(list(df['fn_decl']))
            # print(df['crate'])
        except IndexError:
            # Handle rows that may not have enough columns
            continue
    return effect_counts

total_effect_counts = defaultdict(int)
for package in package_names:
    target = exists(package) 
    
    effect_counts = tally_effects_in_files(target, affected_functions)
    # Aggregate effect counts from each file
    for effect, count in effect_counts.items():
        total_effect_counts[effect] += count

print("Effect counts across all files:")
for effect, count in total_effect_counts.items():
    print(f"{effect}: {count}")

with open("helpers/effect_counts.json", "w") as file:
    json.dump(total_effect_counts, file, indent=4)  # The `indent` parameter makes the file easy to read
