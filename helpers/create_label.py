import re
import json
import csv

def read_dicts_from_txt(text_file, separator="\n---\n"):
    """
    Reads a text file containing multiple dictionary entries separated by a delimiter.
    Each entry is turned into a separate string for parsing.
    """
    with open(text_file, "r") as file:
        content = file.read()
        dict_strings = [s for s in content.split(separator) if s.strip()]
    return dict_strings

def parse_dict_string(dict_string):
    """
    Converts a string representation of a dictionary (with keys and values on separate lines)
    into an actual Python dictionary.
    """
    def string_to_dict(s):
        try:
            return json.loads(s.replace("'", '"'))
        except json.JSONDecodeError:
            return s
    
    kv_pattern = re.compile(r"(\w+):\s*(.+)")
    result_dict = {}
    
    for line in dict_string.split('\n'):
        match = kv_pattern.match(line.strip())
        if match:
            key, value = match.groups()
            if value.startswith('{') or value.startswith('['):
                # Attempt to parse JSON-like structures
                result_dict[key] = string_to_dict(value)
            else:
                result_dict[key] = value
    return result_dict

if __name__ == '__main__':
    # Read and parse the advisories from data.txt
    codex = read_dicts_from_txt("data.txt")

    # Open a CSV file for writing
    with open("../rustsec_labels.csv", "w", newline="") as csvfile:
        fieldnames = ["crate_name", "rustsec_label", "advisory_type"]
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()

        # Iterate over each advisory record
        for data in codex:
            record = parse_dict_string(data)

            # Extract the crate name and version from "package.name", which might look like "crateName(1.2.3)"
            package_field = record.get("package", {}).get("name", "")
            if "(" in package_field:
                parts = package_field.split("(")
                crate_name = parts[0].strip()
            else:
                crate_name = package_field.strip()

            # Classification is the label; if missing, default to "CRITICAL"
            classification = record.get("classification", "CRITICAL")
            
            # Advisory type (may or may not exist)
            advisory_type = record.get("type", None)

            # Write a row to the CSV
            writer.writerow({
                "crate_name": crate_name,
                "rustsec_label": classification,
                "advisory_type": advisory_type
            })

    print("CSV file 'rustsec_labels.csv' created successfully.")
