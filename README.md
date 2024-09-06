# RHS

RHS (name pending) is an automated reasoning tool that attempts to determine the safety of Rust crates by modeling trust.

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
To run the tool, run the Python interpreter on `solver.py`, supplying the crate name and version you would like to analyze. For example:
```
python3 solver.py tokio 1.39.3
```