import csv
import glob
import os
import sys

csv.field_size_limit(sys.maxsize)

directory_path = '/logs/Random500/'
full_path = os.path.join(os.getcwd() + directory_path)
files = glob.glob(os.path.join(full_path, '*.csv'))

# print(files)
result = []
for file in files:
    print(file)
    with open(file, 'r') as f:
        contents = f.read()
        sections = contents.split('************************************')
        for section in sections:
        # Remove any leading/trailing whitespace
            section = section.strip()
            if not section:
                continue
            # print(section)
            lines = section.splitlines()
            reader = csv.DictReader(lines)
            result.append(reader)
    # break

for item in result:
    print(*item)