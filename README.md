# Cargo-Sherlock 🕵️
`Cargo-Sherlock` (alternative name RHS for Rust Sherlock Holmes) is a Python-based tool designed to enhance the security of Rust projects by leveraging different metadata information about Rust crates. It is an automated reasoning tool that attempts to determine the safety of Rust crates by modeling trust. 

⚠️ Cargo Sherlock is under active development. Some features may not work on all crates!

## Installation

1. Clone this repository and the [cargo-scan](https://github.com/PLSysSec/cargo-scan) submodule.
```Bash
git clone --recurse-submodules https://github.com/DavisPL/cargo-sherlock.git
```
2. Run `rustup update` to ensure you have the latest version of Rust (or install it via the [official website]((https://www.rust-lang.org/tools/install))).
```Bash
rustup update
```
3. Run `make` to create a Python virtual environment, install all Python dependencies, activate the virtual environment, and build cargo-scan.
```Bash
make
```
4. Generate a GitHub personal access token. Go to the [token page](https://github.com/settings/tokens/new) and select Generate new token (classic). Then, name your token, select an expiration date, and grant the token at least the `public_repo` scope by checking the box. Finally, create and copy your token, pasting it into the file `helpers/token.txt`.

5. You can activate the python virtual environment by running: 
```bash
source .venv/bin/activate 
```

## Usage
To run the tool, run the Python interpreter on `sherlock.py`, supplying the crate name and version(optional) you would like to analyze. Additionally, you can use various flags to control its behaviour. The tool supports two modes log and trust. You will have to specify the mode while using it. 

```bash 
python3 sherlock.py trust <crate_name> 
```
The above command will run the tool in trust mode for specified crate. Since no version is provided, it will use the latest version by default. For `log` mode, you can run:

```bash 
python3 sherlock.py log <crate_name>
```

⚠️ The tool is under active developmenet. The documentation below this is outdated. 


Here is an example output:
```
❯ python3 sherlock.py -a abomonation
This crate has been flagged by RustSec.
This crate has not been audited by any organization.
Trust Score for abomonation-0.7.3: 60
Assumptions Made:
abomonation-0.7.3 has many downloads: 0 wt
abomonation-0.7.3 having many downloads implies it is safe: 10 wt
abomonation-0.7.3 has all safe dependencies: 0 wt
abomonation-0.7.3 appearing in RustSec implies it is less safe (score penalty): 50 wt
```

### Basic Usage

To analyze a specific crate and version:

```bash
python3 sherlock.py <crate_name> [version]
```
Replace <crate_name> with the actual crate name you want to analyze. If you omit the [version], the tool will fetch and use the latest version of the crate by default. By default, this will run the logger.py script to log information about the specified crate, printing the logging information to the screen. This information is also stored at logs/exp/<crate_name>-<version>.csv

### Available Flags

- `-a` or `--assumptions`: Runs `solver.py` to perform a detailed analysis of the crate. It prints a trust score representing how trustworthy the crate is and the assumptions made to prove the crate was safe.
  
  Note: This flag reasons about all the dependencies in the dependency tree of the crate, which may take a very long time for crates with large dependency trees. This flag is also still a work-in-progress; it may not work for all crates.


```bash
python3 sherlock.py <crate_name> [version] -a
```

- `-u` or `--update`: Updates the information needed for analysis by running three scripts sequentially:
  1. `scrapper.py` to collect information from the RustSec website.
  2. `getCrates.py` to retrieve all crates and their side effects.
  3. `aggregator.py` to compile side effects for all reported vulnerable functions.
  
  This flag ensures that the latest data is used for analysis.
  
  Note: This flag updates information by scraping RustSec and retrieving side effects using cargo-scan for all RustSec crates. Depending upon the internet connection and processing power, it can take a fair amount of time.

- `-o` or `--output`: Specifies an output file path to save the crate information. When used, the tool will write the logging information to the specified file. If you do not provide this flag, the information is stored at `logs/exp/<crate_name>-.csv`.

Note: This flag currently does not work in combination with the `-a` (assumptions) flag. 

```bash
python3 sherlock.py <crate_name> [version] -o <output_file_path>
```

- `-h`: Displays a help message.

## Outputs

Depending on the flags used, Cargo Sherlock will output different information:
- **Default Output**: Logs the crate information using `logger.py`, printing the results to the terminal.
- **With `-a` Flag**: Provides detailed analysis results from `solver.py`.
- **With `-u` Flag**: Updates the data from external sources, followed by either `solver.py` or `logger.py` execution based on additional flags.

## Additional Information 

### Credits
Cargo Sherlock is an open source project from Professor [Caleb Stanford's](https://web.cs.ucdavis.edu/~cdstanford/) Davis PL research group. For copyright information, see the LICENSE.

The following members of the Davis PL research group have made contributions to this project (names in alphabetical order):
- Anirudh Basu
- Audrey Gobaco
- Muhammad Hassnain
- Ethan Ng

A portion of this project was funded by the NSF.

### Issues
If you encounter an issue while using Cargo Sherlock, we would love to hear about it! Please raise a GitHub issue with any bugs you find, features you would like, or pull requests you have.
