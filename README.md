# Cargo-Sherlock 🕵️
`Cargo-Sherlock` (alternative name RHS for Rust Sherlock Holmes) is a Python-based tool designed to enhance the security of Rust projects by leveraging different metadata information about Rust crates. It is an automated reasoning tool that attempts to determine the safety of Rust crates by modeling trust. 

## Installation

For the installation, you can either follow the steps below or download our pre-configured Virtual Machine with all dependencies installed from [Cargo Sherlock VM](). If you downloaded the VM, you can skip step 1-5. 

1. Clone this repository and the [cargo-scan](https://github.com/PLSysSec/cargo-scan) submodule.
```Bash
git clone --recurse-submodules https://github.com/muhammad-hassnain/cargo-sherlock-artifact
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

You can check your installation is successful by running:
```bash
python3 sherlock.py trust anyhow 1.0.97
```
You should see the output of the tool for the crate `anyhow-1.0.97`.

#TODO[add an image]

## Usage
To run the tool, run the Python interpreter on `sherlock.py`, supplying the crate name and version(optional) you would like to analyze. Additionally, you can use various flags to control its behaviour. The tool supports two modes log and trust. You will have to specify the mode while using it. 

```bash 
python3 sherlock.py trust <crate_name> 
```
The above command will run the tool in trust mode for specified crate. Since no version is provided, it will use the latest version by default. For `log` mode, you can run:

```bash 
python3 sherlock.py log <crate_name>
```
