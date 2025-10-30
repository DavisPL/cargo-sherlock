import json
import re
import matplotlib.pyplot as plt
from collections import Counter

def read_dicts_from_txt(text_file, separator="\n---\n"):
    """
    Reads a text file containing multiple dictionary entries separated by a delimiter.
    """
    with open(text_file, "r") as file:
        content = file.read()
    dict_strings = [s for s in content.split(separator) if s.strip()]
    return dict_strings

def parse_dict_string(dict_string):
    """
    Converts a string representation of a dictionary (with keys and values on separate lines)
    into an actual Python dictionary.
    Uses a regex that captures keys with spaces.
    Skips lines that don't have a colon.
    """
    def string_to_dict(s):
        try:
            return json.loads(s.replace("'", '"'))
        except json.JSONDecodeError:
            return s

    # Updated regex: capture any characters up to the first colon.
    kv_pattern = re.compile(r"([^:]+):\s*(.+)")
    result_dict = {}

    for line in dict_string.split('\n'):
        line = line.strip()
        if not line or ":" not in line:
            continue  # skip lines without a colon
        match = kv_pattern.match(line)
        if match:
            key, value = match.groups()
            key = key.strip()
            value = value.strip()
            if value.startswith('{') or value.startswith('['):
                result_dict[key] = string_to_dict(value)
            else:
                result_dict[key] = value
    return result_dict

def main():
    dict_strings = read_dicts_from_txt("data.txt")
    entries = [parse_dict_string(ds) for ds in dict_strings]
    
    type_counter = Counter()
    for entry in entries:
        if "type" in entry:
            type_counter[entry["type"]] += 1
    
    print("Advisory Type Counts:")
    for advisory_type, count in type_counter.items():
        print(f"{advisory_type}: {count}")
    
    # Plot the counts using a bar chart
    plt.figure(figsize=(10, 6))
    plt.bar(list(type_counter.keys()), list(type_counter.values()))
    plt.xlabel("Advisory Type")
    plt.ylabel("Count")
    plt.title("Counts of Unique Advisory Types")
    plt.xticks(rotation=45)
    plt.tight_layout()
    plt.show()

if __name__ == "__main__":
    main()
