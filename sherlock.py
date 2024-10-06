import argparse
import subprocess
import sys
import helpers.crate_data as crate_data
from helpers.assumption import CrateVersion
from pprint import pprint
from helpers.logger import get_latest_version

def main():
    parser = argparse.ArgumentParser(description='Rust Holmes Sherlock: A tool to analye Rust crates')
    
    subparsers = parser.add_subparsers(dest='command', help='Subcommands (log, trust)')

    # Subcommand for logging information
    log_parser = subparsers.add_parser('log', help='Get logging information about a crate')
    log_parser.add_argument('crate_name', type=str, help='Name of the crate')
    log_parser.add_argument('version', type=str, nargs='?', default=None, help='Version of the crate (optional)')
    log_parser.add_argument('-u', '--update', action='store_true', help='Update information by running scrapper.py, getCrates.py, and aggregator.py')
    log_parser.add_argument('-o', '--output', type=str, help='Output file path to save crate information')

    # Subcommand for trust score
    trust_parser = subparsers.add_parser('trust', help='Solve using assumptions to assign a trust score to the crate')
    trust_parser.add_argument('crate_name', type=str, help='Name of the crate')
    trust_parser.add_argument('version', type=str, nargs='?', default=None, help='Version of the crate (optional)')
    trust_parser.add_argument('-o', '--output', type=str, help='Output file path to save trust score information')

    args = parser.parse_args()

    if args.command is None:
        parser.print_help()
        sys.exit(1)

    # Fetch the latest version if not provided
    if args.version is None:
        args.version = get_latest_version(args.crate_name)
        print(f"Latest version of {args.crate_name} is {args.version}.")

    # Handle the 'log' subcommand
    if args.command == 'log':
        if args.update:
            print("Updating information...")
            print("Running scrapper.py to collect information from the RUST SEC website...")
            subprocess.run([sys.executable, 'scrapper.py'])

            print("Running getCrates.py to get all crates and their side effects...")
            subprocess.run([sys.executable, 'getCrates.py'])

            print("Running aggregator.py to get the side effects for all reported vulnerable functions...")
            subprocess.run([sys.executable, 'aggregator.py'])

        # Get logging information about the crate
        crate = CrateVersion(args.crate_name, args.version)
        print(f"Getting logging information About crate {crate}...")
        crate_information = crate_data.get_crate_metadata(crate)
        print(f"Logging information for {args.crate_name}-{args.version}:")
        pprint(crate_information)

        # Save crate information to the output file if provided
        if args.output:
            with open(args.output, 'w') as output_file:
                pprint(crate_information, stream=output_file)
            print(f"Crate information saved to {args.output}.")

    # Handle the 'trust' subcommand
    elif args.command == 'trust':
        from solver import complete_analysis
        crate = CrateVersion(args.crate_name, args.version)
        print(f"Solving for required assumptions to trust {crate}...", file=args.output)
        complete_analysis(crate, args.output)

if __name__ == "__main__":
    main()
