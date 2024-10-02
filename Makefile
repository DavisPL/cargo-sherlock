.PHONY: install clean activate
VENV = .venv
PYTHON = $(VENV)/bin/python3
PIP = $(VENV)/bin/pip

install: $(VENV)/bin/activate cargo-scan/Cargo.toml
	git submodule init
	git submodule update
	. ./$(VENV)/bin/activate
	cargo build --manifest-path cargo-scan/Cargo.toml
	# Please enter your GitHub personal access token:
	# Instructions on how to do this can be found in the README.md file (installation step 4).
	@read token; \
	if [ ! -z "$$token" ]; then \
		echo "$$token" > helpers/token.txt; \
		echo "Token saved to helpers/token.txt"; \
	else \
		echo "No token entered. Please generate a GitHub personal access token and store it in helpers/token.txt manually."; \
	fi
	@echo "Press Enter to continue..."
	@read dummy

activate: $(VENV)/bin/activate
	. ./$(VENV)/bin/activate

$(VENV)/bin/activate: requirements.txt
	python3 -m venv $(VENV)
	$(PIP) install -r requirements.txt

cargo-scan/Cargo.toml:
	git submodule update --remote

clean:
	rm -rf processing/*
	rm -rf __pycache__
	rm -rf $(VENV)
	cargo clean --manifest-path cargo-scan/Cargo.toml
