import argparse
import subprocess
import sys
import helpers.sherlock as sherlock
import helpers.logger as logger
from helpers.assumption import CrateVersion
from pprint import pprint

def main():
    parser = argparse.ArgumentParser(description='A utility script for managing crates.')
    
    parser.add_argument('crate_name', type=str, help='Name of the crate')
    parser.add_argument('version', type=str, help='Version of the crate')
    
    parser.add_argument('-a', '--assumptions', action='store_true', help='Run solver.py with assumptions')
    parser.add_argument('-u', '--update', action='store_true', help='Update information by running scrapper.py, getCrates.py, and aggregator.py')
    parser.add_argument('-H', '--help_extended', action='store_true', help='Show extended help information')

    args = parser.parse_args()

    if args.help_extended:
        print("""
        Usage: python script.py [crate_name] [version] [options]

        Options:
            -a, --assumptions   Run solver.py with assumptions
            -u, --update        Update rustsec information
            -H, --help_extended Show this extended help message
        """)
        sys.exit(0)

    if args.update:
        print("Updating information...")
        
        print("Running scrapper.py to collect information from the RUST SEC website...")
        subprocess.run([sys.executable, 'scrapper.py'])

        print("Running getCrates.py to get all crates and their side effects...")
        subprocess.run([sys.executable, 'getCrates.py'])

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
        # print(crate_information)
        pprint(crate_information)

    # Output a log with crate information
    print(f"Crate: {args.crate_name}, Version: {args.version}")

if __name__ == "__main__":
    main()
