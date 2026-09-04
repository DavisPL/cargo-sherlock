.PHONY: install clean activate
VENV = .venv
PYTHON = $(VENV)/bin/python3
PIP = $(VENV)/bin/pip
NIGHTLY_VERSION = nightly-2025-01-09
PIP_VERSION = 25.0

install: $(VENV)/bin/activate cargo-scan/Cargo.toml
	git submodule init
	git submodule update
	. ./$(VENV)/bin/activate

	# Ensure the specific Rust Nightly version is installed and used
	rustup install $(NIGHTLY_VERSION)
	rustup override set $(NIGHTLY_VERSION)
	rustup component add miri --toolchain $(NIGHTLY_VERSION)

	# Build the Cargo project using the specific Nightly version
	cargo +$(NIGHTLY_VERSION) build --manifest-path cargo-scan/Cargo.toml

	# Please enter your GitHub personal access token:
	# Instructions on how to do this can be found in the README.md file (installation step 5).
	@read token; \
	if [ ! -z "$$token" ]; then \
		echo "$$token" > helpers/token.txt; \
		echo "Token saved to helpers/token.txt"; \
	else \
		echo "No token entered. Please generate a GitHub personal access token and store it in helpers/token.txt manually."; \
	fi
	# Optional: contact email for the crates.io crawler policy.
	# crates.io asks that automated requests identify the app and provide a
	# way to contact you if their team ever needs to. The repository URL in
	# the User-Agent already covers this, so an email is entirely optional.
	# Leave blank to skip; if provided it is stored in helpers/contact.txt
	# and added to the User-Agent for crates.io / GitHub requests.
	@echo "Optional: enter a contact email for the crates.io crawler policy (press Enter to skip):"
	@read contact; \
	if [ ! -z "$$contact" ]; then \
		echo "$$contact" > helpers/contact.txt; \
		echo "Contact saved to helpers/contact.txt"; \
	else \
		echo "No contact entered. Requests will identify cargo-sherlock by its repository URL only."; \
	fi
	@echo "Press Enter to continue..."
	@read dummy

activate: $(VENV)/bin/activate
	. ./$(VENV)/bin/activate

$(VENV)/bin/activate: requirements.txt
	python3 -m venv $(VENV)
	$(PIP) install --upgrade "pip==$(PIP_VERSION)"
	$(PIP) install -r requirements.txt

cargo-scan/Cargo.toml:
	git submodule update --remote

clean:
	rm -rf processing/*
	rm -rf __pycache__
	rm -rf $(VENV)
	cargo clean --manifest-path cargo-scan/Cargo.toml
