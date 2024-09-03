# RHS

RHS (name pending) is an automated reasoning tool that attempts to determine the safety of Rust crates by modeling trust.

## Installation

1. Clone this repository and the cargo-scan submodule.
2. Run `rustup update` to ensure you have the latest version of Rust (or install it via the [official website]((https://www.rust-lang.org/tools/install))).
3. Run `make` to create a Python virtual environment, install all Python dependencies, and build cargo-scan.

Assuming you have Rust and Python installed, you can perform the installation by running the following commands:
```
git clone --recurse-submodules https://github.com/DavisPL/supply-chain-trust.git
git submodule init
rustup update
make
```

## Usage
To run the tool, run the Python interpreter on `solver.py`, supplying the crate name and version you would like to analyze. For example:
```
python3 solver.py tokio 1.39.3
```