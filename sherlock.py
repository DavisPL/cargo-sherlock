import argparse
import subprocess
import sys
import helpers.sherlock as sherlock
from helpers.assumption import CrateVersion
from pprint import pprint
from helpers.logger import get_versions

def get_latest_version(crate_name):
    versions = get_versions(crate_name)
    if versions:
        return versions[-1]  
    else:
        print(f"Could not fetch the latest version for crate {crate_name}.")
        sys.exit(1)

def main():
    parser = argparse.ArgumentParser(description='A utility script for managing crates.')
    
    parser.add_argument('crate_name', type=str, help='Name of the crate')
    parser.add_argument('version', type=str, nargs='?', default=None, help='Version of the crate (optional)')

    parser.add_argument('-a', '--assumptions', action='store_true', help='Solve using assumptions to assign a trust score to the crate') 
    parser.add_argument('-u', '--update', action='store_true', help='Update information by running scrapper.py, getCrates.py, and aggregator.py')
    parser.add_argument('-H', '--help_extended', action='store_true', help='Show extended help information')

    args = parser.parse_args()

    if args.help_extended:
        print("""
        Usage: python script.py [crate_name] [version] [options]

        Options:
            -a, --assumptions   Solve using assumptions to assign a trust score to the crate
            -u, --update        Update rustsec information
            -h, --help_extended Show this extended help message
        """)
        sys.exit(0)

    # Fetch the latest version if not provided
    if args.version is None:
        print(f"No version specified for {args.crate_name}. Fetching the latest version...")
        args.version = get_latest_version(args.crate_name)
        print(f"Latest version of {args.crate_name} is {args.version}.")

    if args.update:
        print("Updating information...")
        
        print("Running scrapper.py to collect information from the RUST SEC website...")
        # subprocess.run([sys.executable, 'scrapper.py'])

        print("Running getCrates.py to get all crates and their side effects...")
        # subprocess.run([sys.executable, 'getCrates.py'])

        print("Running aggregator.py to get the side effects for all reported vulnerable functions...")
        subprocess.run([sys.executable, 'aggregator.py'])

    # Check if the assumptions flag is present
    if args.assumptions:
        # Run solver.py with crate_name and version
        crate = CrateVersion(args.crate_name, args.version)
        print(f"Solving for required Assumptions to trust {crate}...")
        subprocess.run([sys.executable, 'solver.py', args.crate_name, args.version])
    else:
        # Get logging information about the crate
        crate = CrateVersion(args.crate_name, args.version)
        print(f"Getting Logging Information About Crate {crate}...")
        crate_information = sherlock.get_crate_metadata(crate)
        print(f"Logging information for {args.crate_name}-{args.version}:")
        pprint(crate_information)

if __name__ == "__main__":
    main()
