# Cargo-Sherlock Artifact 🕵️
`Cargo-Sherlock` (alternative name RHS for Rust Sherlock Holmes) is a Python-based tool designed to enhance the security of Rust projects by leveraging different metadata information about Rust crates. It is an automated reasoning tool that attempts to determine the safety of Rust crates by modeling trust. 
This repository contains the artifact for paper[] submitted to FORMALISE 2026. 

## Installation

For the installation, you can either follow the steps below or download our pre-configured Virtual Machine with all dependencies installed from [Cargo Sherlock VM](). If you downloaded the VM, you can skip step 1-5. 

1. Clone this repository and the [cargo-scan](https://github.com/PLSysSec/cargo-scan) submodule.
```Bash
git clone --recurse-submodules https://github.com/muhammad-hassnain/cargo-sherlock-artifact
```
2. Install Rust via the [official website](https://www.rust-lang.org/tools/install). After installing Rust, you can verify the installation by running:
```Bash
rustc --version
```
This should display the installed Rust version.

3. Ensure you have Python 3 installed. You can verify your Python installation by running:
```Bash
python3 --version
```
This should display the installed Python version. If not installed, you can download it from the [official website](https://www.python.org/downloads/).

4. Run `make` to create a Python virtual environment, this will install all Python dependencies, activate the virtual environment, and build cargo-scan.
```Bash
make
```

This should take 3-5 minutes and will prompt you for your GitHub personal access token (see step 5 below).

5. You can Generate a GitHub personal access token from [token page](https://github.com/settings/tokens/new). Please select Generate new token (classic). Then, name your token, select an expiration date, and grant the token at least the `public_repo` scope by checking the box. Finally, create and copy your token and paste it. In case, you didn't provide a token at installation time, you can create the file `helpers/token.txt` and paste your token there later.

6. You can activate the python virtual environment by running: 
```bash
source .venv/bin/activate 
```
You should now see a `(.venv)` prefix in your terminal indicating that the virtual environment is active.

You can check your installation is successful by running:
```bash
python3 sherlock.py trust anyhow 1.0.97
```
You should see something like:
 
![image here](output.png "Screenshot from 10/30")


## Replication Instructions


We provide you with step-by-step instructions and scripts to replicate the results for each research question (RQ) presented in the paper.

### RQ1: Synthetic Tuposquatted Attacks

### RQ2: Real-World Supply Chain Risks
We will replicate the experiment and the regenerate the table [Table 4] presented in the paper. The source code for faster_log crate is not publicly available on crates.io, therefore, we have included the results for that crate cached in the `evaluation/rq2` directory.

```Bash
python3 eval_rq2.py
```


### RQ3:

### RQ4:


