# Cargo-Sherlock 🕵️
`Cargo-Sherlock` is a Python-based tool designed to enhance the security of Rust projects by leveraging different metadata information about Rust crates. It is an automated reasoning tool that attempts to determine the safety of Rust crates by modeling trust. 

## Installation

1. Clone this repository and the cargo-scan submodule.
2. Run `rustup update` to ensure you have the latest version of Rust (or install it via the [official website]((https://www.rust-lang.org/tools/install))).
3. Run `make` to create a Python virtual environment, install all Python dependencies, and build cargo-scan.
4. Generate a GitHub personal access token. Go to the [token page](https://github.com/settings/tokens/new) and select Generate new token (classic). Then, name your token, select an expiration date, and grant the token at least the `public_repo` scope by checking the box. Finally, create and copy your token, pasting it into the file `helpers/token.txt`.

Assuming you have Rust and Python installed, you can perform the installation by running the following commands:
```
git clone --recurse-submodules https://github.com/DavisPL/supply-chain-trust.git
git submodule init
git submodule update
rustup update
make
```

## Usage
To run the tool, run the Python interpreter on `detective.py`, supplying the crate name and version you would like to analyze. Additionally, you can use various flags to control its behaviour. 

### Basic Usage

To analyze a specific crate and version:

```bash
python3 detective.py <crate_name> <version>
```

Replace `<crate_name>` and `<version>` with the actual crate name and version you want to analyze. By default, this will run the `logger.py` script to log information about the specified crate, this prints the logging information on the screen. This information is is also stored at `logs/exp/<crate_name>-<version>.csv`.

### Available Flags

- `-a` or `--assumptions`: Runs `solver.py` to perform a detailed analysis of the crate logging information. It uses Z3 modeling to determine which assumptions should be made to trust this crate and returns a trust score representing how trustworthy the crate is.


```bash
python3 detective.py <crate_name> <version> -a
```

- `-u` or `--update`: Updates the information needed for analysis by running three scripts sequentially:
  1. `scrapper.py` to collect information from the RustSec website.
  2. `getCrates.py` to retrieve all crates and their side effects.
  3. `aggregator.py` to compile side effects for all reported vulnerable functions.
  
  This flag ensures that the latest data is used for analysis.
  
  Note: This updating information scrapes RustSec and gets side effects using cargo-scan for all RustSec crates to updates information about dangerous side effects. **Running this can take up to 2 hours.**

- `-h`: Displays a help message.

## Outputs

Depending on the flags used, Cargo-Sherlock will output different information:
- **Default Output**: Logs the crate information using `logger.py`, printing the results to the terminal.
- **With `-a` Flag**: Provides detailed analysis results from `solver.py`.
- **With `-u` Flag**: Updates the data from external sources, followed by either `solver.py` or `logger.py` execution based on additional flags.

