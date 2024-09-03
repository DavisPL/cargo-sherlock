.PHONY: install clean
VENV = .venv
PYTHON = $(VENV)/bin/python3
PIP = $(VENV)/bin/pip

install: $(VENV)/bin/activate cargo-scan/Cargo.toml
	cargo build --manifest-path cargo-scan/Cargo.toml

$(VENV)/bin/activate: requirements.txt
	python3 -m venv $(VENV)
	$(PIP) install -r requirements.txt

cargo-scan/Cargo.toml:
	git submodule update --remote

clean:
	rm -rf __pycache__
	rm -rf $(VENV)
	cargo clean --manifest-path cargo-scan/Cargo.toml