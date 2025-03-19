import requests
from bs4 import BeautifulSoup
from urllib.parse import urljoin
import pprint
import csv
import os 
import time
from tqdm import tqdm


def get_text_or_default(element, default=''):
    return element.get_text(strip=True) if element else default

def extract_links(element):
    return [{'text': a.get_text(strip=True), 'url': a['href']} for a in element.find_all('a')]

def flatten_dict(d, parent_key='', sep='_'):
    """
    Flatten a nested dictionary into a flat dictionary.
    """
    items = []
    for k, v in d.items():
        new_key = f'{parent_key}{sep}{k}' if parent_key else k
        if isinstance(v, dict):
            items.extend(flatten_dict(v, new_key, sep=sep).items())
        elif isinstance(v, list):
            # Convert list to a string
            items.append((new_key, ', '.join(str(item) for item in v)))
        else:
            items.append((new_key, v))
    return dict(items)

def write_dict_to_csv(data, csv_file):
    """
    Write a dictionary to a CSV file. If the file exists, append new rows; 
    otherwise, create a new file.
    """
    flat_data = flatten_dict(data)

    # Check if file exists
    file_exists = os.path.isfile(csv_file)

    # Writing to CSV
    with open(csv_file, 'a' if file_exists else 'w', newline='', encoding='utf-8') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=flat_data.keys())

        if not file_exists:
            writer.writeheader()  # Write header if file does not exist

        writer.writerow(flat_data)

def get_index(hay, stack):
    for i in range(0,len(stack)):
        # print(hay, stack[i])
        if stack[i] == hay:
            return i

def write_dict_to_txt(data, text_file, separator="\n---\n"):
    # Open the file in append mode
    with open(text_file, "a") as file:
        # Write the dictionary with the separator at the beginning
        file.write(separator)
        # Iterate through the dictionary and write each key-value pair
        for key, value in data.items():
            file.write(f"{key}: {value}\n")



url = "https://rustsec.org/advisories/"

response = requests.get(url)

soup = BeautifulSoup(response.text, 'html.parser')

# print(soup.prettify())

advisories = {}
count = 0

for h3 in soup.find_all('h3'):
    # Try to get the tag text; if not present, assign a default value.
    tag_element = h3.find('span')
    tag = tag_element.text.strip() if tag_element else "Uncategorized"

    # Get the advisory link
    link_element = h3.find('a')
    if not link_element:
        continue
    link = link_element['href']

    # Add the advisory link under the tag in your dictionary.
    if tag not in advisories:
        advisories[tag] = [link]
    else:
        advisories[tag].append(link)
    # print(count)
    # break

# print(advisories)
for k in tqdm(advisories.keys(), desc="Scraping RustSec"):
    print(f"Working on: {k} Labels")
    for link in advisories[k]:
        full_url = urljoin(url, link)
        response = requests.get(full_url)
        soup = BeautifulSoup(response.text, 'html.parser')
        # print(soup.prettify())
        
        vulnerability_report = {}

        vulnerability_report["classification"] = k

        subtitle = soup.find(class_="subtitle")
        vulnerability_report["subtitle"] = get_text_or_default(subtitle, "No subtitle")

        # Other details
        for dt in soup.find_all("dt"):
            key = dt.get_text(strip=True).lower()
            next_sibling = dt.find_next_sibling("dd")
            
            if next_sibling:
                if key == "cvss details":
                    # Nested dictionary for CVSS details
                    cvss_details = {}
                    for dt_cvss in next_sibling.find_all("dt"):
                        cvss_key = dt_cvss.get_text(strip=True)
                        cvss_value = get_text_or_default(dt_cvss.find_next_sibling("dd"))
                        cvss_details[cvss_key] = cvss_value
                    vulnerability_report[key] = cvss_details
                elif key in ["categories", "keywords"]:
                    # List for certain keys
                    items = [li.get_text(strip=True) for li in next_sibling.find_all("li")]
                    vulnerability_report[key] = items
                elif key in ["aliases", "references"]:
                    # List of dicts for links
                    vulnerability_report[key] = extract_links(next_sibling)
                elif key == "package":
                    # Special handling for package with link
                    package_info = {}
                    package_info['name'] = get_text_or_default(next_sibling)
                    package_link = next_sibling.find('a')
                    if package_link:
                        package_info['url'] = package_link['href']
                    vulnerability_report[key] = package_info
                else:
                    # Single value for other keys
                    vulnerability_report[key] = next_sibling.get_text(strip=True)

        flag = False
        for h3 in soup.find_all("h3"):
            key = h3.get_text(strip=True).lower()

            if key == "description":
                description_text = ""
                for sibling in h3.next_siblings:
                    if sibling.name == "p":
                        description_text += get_text_or_default(sibling) + " "
                    elif sibling.name == "h3":
                        break
                vulnerability_report["description"] = description_text.strip()
            else:
                content = []
                for sibling in h3.next_siblings:
                    if sibling.name == "p":
                        content.append(get_text_or_default(sibling))
                        content.extend(extract_links(sibling))
                    elif sibling.name == "ul":
                        for li in sibling.find_all('li'):
                            content.append(get_text_or_default(li))
                            content.extend(extract_links(li))
                    elif sibling.name == "h3":
                        break

                if flag:
                    vulnerability_report["References"] = content
                else:    
                    vulnerability_report["unaffected"] = content
                    flag = True

                
        # print((vulnerability_report))
        keys = list(vulnerability_report.keys())
        if 'affected functions' in keys:
            target = get_index("affected functions" , keys)
            # print("target :" , target)
            func = keys[target+1]
            func = func.replace(":" , ";")
            vulnerability_report['affected_functions'] = func
            vulnerability_report["version_of_Affected"] = vulnerability_report[keys[target+1]]
        # print(vulnerability_report)
        # exit()
        # write_dict_to_csv( vulnerability_report , "results.csv")
        write_dict_to_txt(vulnerability_report, "helpers/data.txt")
        # print("-----")
        # break
        time.sleep(0.1)
    # break
    


