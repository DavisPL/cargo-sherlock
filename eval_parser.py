import os
import json
import pandas as pd

# Function to parse JSON file and extract relevant information
def parse_json(file_path, distribution):
    with open(file_path, 'r') as f:
        data = f.read().splitlines()
    
    crate_name_version = os.path.basename(file_path).replace('.json', '')
    
    # Find trust score line if it exists
    trust_score_line = next((line for line in data if line.startswith('Trust Score')), None)
    if trust_score_line:
        trust_score = trust_score_line.split(': ')[1]
    else:
        trust_score = None  # Handle missing trust score
    
    # Check for assumptions section
    try:
        assumptions_start = data.index('Assumptions Made:') + 1
        logging_info = data[1:data.index('Assumptions Made:')]  # Everything above 'Assumptions Made:'
        assumptions = data[assumptions_start:]  # Everything below 'Assumptions Made:'
    except ValueError:
        logging_info = []  # Handle missing sections
        assumptions = []
    
    return {
        'crate_name_version': crate_name_version,
        'distribution': distribution,
        'trust_score': trust_score,
        'logging_info': ' | '.join(logging_info),
        'assumptions': ' | '.join(assumptions)
    }

# Function to process directory
def process_directory(base_dir):
    result = []
    for json_file in os.listdir(base_dir):
        if json_file.endswith('.json'):
            file_path = os.path.join(base_dir, json_file)
            result.append(parse_json(file_path, base_dir))
    return result

# Directory paths
# normal_dir = '/home/ubuntu/typo/cargo-sherlock/evaluation/top100'
# typo_dir = '/home/ubuntu/typo/cargo-sherlock/evaluation/typo'

optimal_dir = "/Users/hassnain/Desktop/cargo-sherlock/data/timing/random500/single_query"
optimized_dir = "/Users/hassnain/Desktop/cargo-sherlock/data/timing/random500/optimized"

# Process both normal and rustsec directories
optimal_data = process_directory(optimal_dir)
optimized_data = process_directory(optimized_dir)

# Create DataFrames
optimal_df = pd.DataFrame(optimal_data)
optimized_df = pd.DataFrame(optimized_data)

# Save to CSV files
optimal_df.to_csv('/Users/hassnain/Desktop/cargo-sherlock/data/timing/random500/single_query.csv', index=False)
optimized_df.to_csv('/Users/hassnain/Desktop/cargo-sherlock/data/timing/random500/optimized.csv', index=False)

# print("CSV files generated: 'top100_data.csv' and 'typo_data.csv'")
