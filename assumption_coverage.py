import random
import requests
from helpers.crate_data import CrateVersion
from helpers.logger import get_crate_names
from solver import memoized_crate_analysis
from collections import Counter

# Function to get the latest version of a crate
def get_latest_version(crate_name):
    url = f'https://crates.io/api/v1/crates/{crate_name}'
    response = requests.get(url)
    crate_info = response.json()['crate']
    return crate_info['newest_version']

def get_random_crates(count: int):
    # Get all crate names from a random page
    all_crate_names = []
    per_page = 20
    visited = []

    while len(all_crate_names) < count:
        while True:
            random_page = random.randint(200, 3000)
            if random_page in visited:
                continue
            visited.append(random_page)
            break
        crates = get_crate_names(random_page, per_page)
        if not crates:
            continue
        all_crate_names.extend([crate['id'] for crate in crates])

    # Randomly select 1000 crate names
    random_crates = random.sample(all_crate_names, count)

    # Get the latest version of each selected crate
    return [CrateVersion(crate_name, get_latest_version(crate_name)) for crate_name in random_crates]

def get_assumptions_made(crate: CrateVersion) -> list[int]:
    """
    Returns a list of assumption IDs made for a given crate.
    """
    summary = memoized_crate_analysis(crate)
    return [assumption.id for assumption in summary.assumptions_made]

def main():
    random_crates = get_random_crates(30)
    for crate in random_crates:
        print(f"{crate} assumptions:")
        assumptions_made = get_assumptions_made(crate)
        for assumption_id in assumptions_made:
            print(f"Assumption {assumption_id}")


if __name__ == "__main__":
    main()