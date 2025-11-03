import os
import csv
import shutil
import subprocess
import requests
import toml
import time
import re
import matplotlib.pyplot as plt
import pandas as pd
import seaborn as sns
import argparse
import logging
import textwrap


CRATE_PREFIX = "supply-chain-trust-example-crate-"
CSV_FILE = "top100_crates.csv"
LOG_FILE = "prepare_log.txt"          # existing per-crate progress log (kept)
RUN_LOG_FILE = "rq1_run.log"          # NEW: global run log for all non-main output

TARGET_DIR = "./local_crates/typo"
OUTPUT_DIR_REAL = os.path.join("evaluation", "rq1", "real")
OUTPUT_DIR_TYPO = os.path.join("evaluation", "rq1", "typo")
RATE_LIMIT_SECONDS = 1.0  # wait between crates.io requests
OUTPUT_SEVERITY_CSV = "rq1_severities.csv"

# --- Logging setup (for all code outside main) ---
LOGGER = logging.getLogger("rq1_eval")
LOGGER.setLevel(logging.INFO)

os.makedirs(os.path.dirname(RUN_LOG_FILE) or ".", exist_ok=True)
_file_handler = logging.FileHandler(RUN_LOG_FILE, encoding="utf-8")
_file_handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
LOGGER.addHandler(_file_handler)

# Ensure these dirs exist early
os.makedirs(OUTPUT_DIR_REAL, exist_ok=True)
os.makedirs(OUTPUT_DIR_TYPO, exist_ok=True)
os.makedirs(TARGET_DIR, exist_ok=True)

TMP_PREFIX = "__tmp__" + CRATE_PREFIX
TMP_PATTERN = re.compile(rf"^__tmp__{re.escape(CRATE_PREFIX)}(\d{{6}})$")

def _run_and_log(cmd, *, cwd=None, log_prefix=None, check=False):
    """Run a subprocess, capture stdout/stderr, and log them."""
    try:
        if log_prefix:
            LOGGER.info(f"{log_prefix} Running: {' '.join(cmd)} (cwd={cwd or os.getcwd()})")
        else:
            LOGGER.info(f"Running: {' '.join(cmd)} (cwd={cwd or os.getcwd()})")
        res = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, check=check)
        if res.stdout:
            LOGGER.info(res.stdout.rstrip("\n"))
        if res.stderr:
            # treat any stderr as error-level for visibility
            LOGGER.error(res.stderr.rstrip("\n"))
        return res
    except subprocess.CalledProcessError as e:
        # CalledProcessError contains returncode, stdout, stderr
        stdout = e.stdout or ""
        stderr = e.stderr or ""
        if stdout:
            LOGGER.info(stdout.rstrip("\n"))
        if stderr:
            LOGGER.error(stderr.rstrip("\n"))
        LOGGER.error(f"Command failed with exit code {e.returncode}: {' '.join(cmd)}")
        raise

def _load_crate_ids(csv_path: str):
    ids = []
    with open(csv_path, "r", newline="") as f:
        reader = csv.DictReader(f)
        key = "id" if "id" in reader.fieldnames else "name"
        for row in reader:
            ids.append(row[key].strip())
    return ids

def _crates_io_repo_url(crate_name: str):
    time.sleep(RATE_LIMIT_SECONDS)
    url = f"https://crates.io/api/v1/crates/{crate_name}"
    r = requests.get(url)
    if r.status_code == 200:
        return r.json().get("crate", {}).get("repository")
    return None

def _rewrite_cargo_toml(crate_dir: str, original: str, new_name: str):
    cargo_toml = os.path.join(crate_dir, "Cargo.toml")
    if not os.path.exists(cargo_toml):
        raise FileNotFoundError(f"Cargo.toml not found in {crate_dir}")
    with open(cargo_toml, "r", encoding="utf-8") as f:
        data = toml.load(f)
    if "package" not in data:
        raise ValueError("Missing [package] section in Cargo.toml")
    pkg = data["package"]
    pkg["name"] = new_name
    pkg["authors"] = ["Anonymous"]
    pkg.pop("repository", None)
    pkg.pop("homepage", None)
    with open(cargo_toml, "w", encoding="utf-8") as f:
        toml.dump(data, f)
    lib_rs = os.path.join(crate_dir, "src", "lib.rs")
    if os.path.exists(lib_rs):
        try:
            with open(lib_rs, "r", encoding="utf-8") as f:
                content = f.read()
            needle = f'#![crate_name = "{original}"]'
            if needle in content:
                underscore = new_name.replace("-", "_")
                content = content.replace(needle, f'#![crate_name = "{underscore}"]')
                with open(lib_rs, "w", encoding="utf-8") as f:
                    f.write(content)
        except Exception:
            pass

def run_top100_crates(csv_file: str = CSV_FILE, out_dir: str = OUTPUT_DIR_REAL) -> None:
    os.makedirs(out_dir, exist_ok=True)
    with open(csv_file, "r", newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            crate_name = (row.get("id") or row.get("name") or "").strip()
            version = (row.get("version") or "").strip()
            if not crate_name or not version:
                continue

            output_file = os.path.join(out_dir, f"{crate_name}-{version}")
            os.makedirs(os.path.dirname(output_file), exist_ok=True)

            cmd = ["python3", "sherlock.py", "trust", crate_name, version, "-o", output_file]
            _run_and_log(cmd, log_prefix="[real]")

def prepare_typo_crates(csv_file: str = CSV_FILE, target_dir: str = TARGET_DIR, log_path: str = LOG_FILE):
    crates = _load_crate_ids(csv_file)
    total = len(crates)
    with open(log_path, "a", encoding="utf-8") as log:
        for i, crate in enumerate(crates, start=1):
            new_name = f"{CRATE_PREFIX}{i:06d}"
            dest_dir = os.path.join(target_dir, new_name)
            tmp_dir = os.path.join(target_dir, f"__tmp__{new_name}")

            if os.path.exists(dest_dir):
                shutil.rmtree(dest_dir, ignore_errors=True)

            repo_url = _crates_io_repo_url(crate)
            if not repo_url:
                msg = f"No repo URL for {crate}"
                LOGGER.info(msg)
                log.write(f"FAIL {i}/{total}: {crate} -> {new_name}: {msg}\n")
                continue

            LOGGER.info(f"[{i}/{total}] Cloning {crate} from {repo_url} into {tmp_dir}...")
            try:
                _run_and_log(["git", "clone", "--depth", "1", repo_url, tmp_dir], check=True)
            except subprocess.CalledProcessError as e:
                msg = f"git clone failed: {e}"
                LOGGER.error(msg)
                log.write(f"FAIL {i}/{total}: {crate} -> {new_name}: {msg}\n")
                # keep tmp_dir for inspection
                continue

            try:
                _rewrite_cargo_toml(tmp_dir, crate, new_name)
                # move finalized tree to dest; remove tmp dir marker
                if os.path.exists(dest_dir):
                    shutil.rmtree(dest_dir, ignore_errors=True)
                shutil.move(tmp_dir, dest_dir)
                LOGGER.info(f"OK  {crate} -> {new_name} at {dest_dir}")
                log.write(f"OK   {i}/{total}: {crate} -> {new_name}\n")
            except Exception as e:
                msg = f"rewrite/move failed: {e}"
                LOGGER.error(msg)
                log.write(f"FAIL {i}/{total}: {crate} -> {new_name}: {msg}\n")
                # keep tmp_dir for patching
                continue

def _first_extracted_crate_root(path: str):
    # Look for a single subdirectory containing Cargo.toml
    candidates = []
    for entry in os.listdir(path):
        full = os.path.join(path, entry)
        if os.path.isdir(full) and os.path.exists(os.path.join(full, "Cargo.toml")):
            candidates.append(full)
    return candidates[0] if candidates else None

def patch_typo_crates_from_tmp(csv_file: str = CSV_FILE, target_dir: str = TARGET_DIR, log_path: str = LOG_FILE):
    crates = _load_crate_ids(csv_file)
    total = len(crates)
    entries = [d for d in os.listdir(target_dir) if TMP_PATTERN.match(d)]
    if not entries:
        return
    with open(log_path, "a", encoding="utf-8") as log:
        for tmp_name in entries:
            m = TMP_PATTERN.match(tmp_name)
            if not m:
                continue
            idx_str = m.group(1)
            i = int(idx_str)  # 1-based index from the six digits
            if i < 1 or i > len(crates):
                LOGGER.error(f"[patch] index {i} out of range for {tmp_name}")
                log.write(f"PATCH FAIL ?: {tmp_name}: index out of range\n")
                continue
            crate = crates[i - 1]
            final_name = f"{CRATE_PREFIX}{i:06d}"
            tmp_dir = os.path.join(target_dir, tmp_name)
            dest_dir = os.path.join(target_dir, final_name)

            LOGGER.info(f"[patch {i}/{total}] Re-trying via cargo download: {crate} -> {final_name}")

            # Delete existing tmp dir, recreate it empty (as requested)
            shutil.rmtree(tmp_dir, ignore_errors=True)
            os.makedirs(tmp_dir, exist_ok=True)

            try:
                # Download and extract into tmp_dir (creates <crate>-<ver>/...)
                _run_and_log(["cargo", "download", crate, "-x"], cwd=tmp_dir, check=True)
            except subprocess.CalledProcessError as e:
                msg = f"cargo download failed: {e}"
                LOGGER.error(msg)
                log.write(f"PATCH FAIL {i}/{total}: {crate} -> {final_name}: {msg}\n")
                # leave tmp_dir as-is for inspection
                continue

            extracted_root = _first_extracted_crate_root(tmp_dir)
            if not extracted_root:
                msg = "no extracted crate root with Cargo.toml found"
                LOGGER.error(msg)
                log.write(f"PATCH FAIL {i}/{total}: {crate} -> {final_name}: {msg}\n")
                # leave tmp_dir
                continue

            try:
                _rewrite_cargo_toml(extracted_root, crate, final_name)
                if os.path.exists(dest_dir):
                    shutil.rmtree(dest_dir, ignore_errors=True)
                shutil.move(extracted_root, dest_dir)
                # success → remove the empty tmp shell (the __tmp__ name disappears)
                shutil.rmtree(tmp_dir, ignore_errors=True)
                LOGGER.info(f"PATCH OK {crate} -> {final_name} at {dest_dir}")
                log.write(f"PATCH OK {i}/{total}: {crate} -> {final_name}\n")
            except Exception as e:
                msg = f"patch rewrite/move failed: {e}"
                LOGGER.error(msg)
                log.write(f"PATCH FAIL {i}/{total}: {crate} -> {final_name}: {msg}\n")
                # keep tmp_dir

def run_typo_crates(typo_output_dir: str = OUTPUT_DIR_TYPO, target_dir: str = TARGET_DIR) -> None:
    cwd = os.getcwd()
    for i in range(1, 101):
        crate_name = f"{CRATE_PREFIX}{i:06d}"
        crate_path = os.path.join(cwd, target_dir, crate_name)
        output_file = os.path.join(typo_output_dir, crate_name)
        os.makedirs(os.path.dirname(output_file), exist_ok=True)
        cmd = ["python3", "sherlock.py", "trust", crate_name, "--path", crate_path, "-o", output_file]
        _run_and_log(cmd, log_prefix="[typo]")

ANSI_RE = re.compile(r"\x1B\[[0-?]*[ -/]*[@-~]")

def strip_ansi(s: str) -> str:
    return ANSI_RE.sub("", s)

def _last_int_on_line_containing(t: str, needle: str):
    for line in t.splitlines():
        if needle.lower() in line.lower():
            ints = re.findall(r"(\d{1,3})\b", line)
            if ints: return ints[-1]
    return None

def _value_after_colon_on_line_containing(t: str, needle: str):
    for line in t.splitlines():
        if needle.lower() in line.lower():
            m = re.search(r":\s*([A-Z0-9_\-]+)", line, flags=re.IGNORECASE)
            if m: return m.group(1)
    return None

def parse_analysis_report(text: str):
    t = strip_ansi(text).replace("\u00A0", " ")
    def first_int_on_same_line(label_pat: str):
        m = re.search(label_pat, t, flags=re.IGNORECASE)
        if not m: return None
        start = t.rfind("\n", 0, m.start()) + 1
        end = t.find("\n", m.end()); end = len(t) if end == -1 else end
        line = t[start:end]
        n = re.search(r"(\d{1,3})\b", line)
        return n.group(1) if n else None
    trust = first_int_on_same_line(r"Trust\s*Cost")
    distrust = first_int_on_same_line(r"Distrust\s*Cost")
    m = re.search(r"Severity\s*Label:\s*([A-Z0-9_\-]+)", t, flags=re.IGNORECASE)
    sev = m.group(1) if m else None
    if trust is None:
        trust = _last_int_on_line_containing(t, "Trust Cost")
    if distrust is None:
        distrust = _last_int_on_line_containing(t, "Distrust Cost")
    if sev is None:
        sev = _value_after_colon_on_line_containing(t, "Severity Label")
    return {"trust_cost": trust, "distrust_cost": distrust, "severity_label": sev}

def _read_dir_reports(dir_path: str):
    out = {}
    if not os.path.isdir(dir_path):
        return out
    for fname in os.listdir(dir_path):
        fpath = os.path.join(dir_path, fname)
        if not os.path.isfile(fpath):
            continue
        try:
            with open(fpath, "r", encoding="utf-8", errors="replace") as fh:
                parsed = parse_analysis_report(fh.read())
            out[fname] = parsed
        except Exception:
            pass
    return out

def build_severity_csv(csv_in: str = CSV_FILE,
                       real_dir: str = OUTPUT_DIR_REAL,
                       typo_dir: str = OUTPUT_DIR_TYPO,
                       csv_out: str = OUTPUT_SEVERITY_CSV):
    # read reports once
    real_reports = _read_dir_reports(real_dir)   # keys are filenames like "syn-2.0.100"
    typo_reports = _read_dir_reports(typo_dir)   # keys are names like "supply-chain-trust-example-crate-000001"

    rows = []
    with open(csv_in, "r", newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for idx, row in enumerate(reader, start=1):
            crate_id = (row.get("id") or row.get("name") or "").strip()
            version = (row.get("version") or "").strip()

            # real file key is "<id>-<version>"
            real_key = f"{crate_id}-{version}" if crate_id and version else crate_id

            # typo key is index-based synthetic name
            typo_key = f"{CRATE_PREFIX}{idx:06d}"

            real_label = (real_reports.get(real_key) or {}).get("severity_label", "")
            typo_label = (typo_reports.get(typo_key) or {}).get("severity_label", "")

            rows.append({"name": crate_id, "real_label": real_label, "typo_label": typo_label})

    with open(csv_out, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["name", "real_label", "typo_label"])
        w.writeheader()
        w.writerows(rows)

    LOGGER.info(f"Wrote {len(rows)} rows to {csv_out}")

SEVERITY_COLORS = {
    "SAFE":            (55, 126, 33),    # bold green
    "LOW_SEVERITY":    (167, 94, 33),    # bold dark_orange
    "MEDIUM_SEVERITY": (134, 198, 227),  # bold cyan
    "HIGH_SEVERITY":   (194, 102, 204),  # bold violet
    "CRITICAL":        (187, 39, 26),    # bold red
}

def _rgb01_for_label(label: str):
    """Return an RGB tuple normalized to 0..1 for Matplotlib."""
    lab = (label or "").upper()
    # resolve by substring to be robust
    if "CRITICAL" in lab:
        key = "CRITICAL"
    elif "HIGH" in lab:
        key = "HIGH_SEVERITY"
    elif "MEDIUM" in lab:
        key = "MEDIUM_SEVERITY"
    elif "LOW" in lab:
        key = "LOW_SEVERITY"
    elif "SAFE" in lab:
        key = "SAFE"
    else:
        return (0, 0, 0)
    r, g, b = SEVERITY_COLORS[key]
    return (r/255.0, g/255.0, b/255.0)

def plot_severity_heatmap_from_csv(
    csv_path: str,
    x_order = ("SAFE", "LOW_SEVERITY"),
    y_order = ("CRITICAL", "HIGH_SEVERITY", "MEDIUM_SEVERITY", "LOW_SEVERITY", "SAFE"),
):
    df = pd.read_csv(csv_path)
    df["real_label"] = df["real_label"].astype(str).str.strip().str.upper()
    df["typo_label"] = df["typo_label"].astype(str).str.strip().str.upper()

    ct = pd.crosstab(df["typo_label"], df["real_label"])
    ct = ct.reindex(index=list(y_order), columns=list(x_order), fill_value=0)

    sns.set_theme(style="whitegrid", context="talk")
    plt.figure(figsize=(6, 5))
    ax = sns.heatmap(
        ct,
        annot=True,         # numbers shown
        fmt="d",
        cmap="Blues",       # keep cells in Blues
        cbar=False,
        linewidths=1,       # grid/boundaries
        linecolor="white",  # boundaries stay white
    )

    ax.set_xlabel("Real Crate Severity Label", fontsize=14, fontweight="bold")
    ax.set_ylabel("Typosquatted Crate Severity Label", fontsize=14, fontweight="bold")
    
    # Bold + LaTeX color for tick labels ONLY (numbers remain default)
    for lbl in ax.get_xticklabels():
        sev = lbl.get_text().upper()
        lbl.set_color(_rgb01_for_label(sev))
        lbl.set_fontweight("bold")

    for lbl in ax.get_yticklabels():
        sev = lbl.get_text().upper()
        lbl.set_color(_rgb01_for_label(sev))
        lbl.set_fontweight("bold")

    plt.tight_layout()
    plt.savefig("severity_heatmap.pdf", bbox_inches="tight")
    LOGGER.info("Saved severity heatmap to 'severity_heatmap.pdf'")
    print("Saved severity heatmap to 'severity_heatmap.pdf'")

def main():

    parser = argparse.ArgumentParser(
        prog="eval_rq1.py",
        description="Evaluate RQ1: Real vs Typosquatted Crates Analysis",
        formatter_class=argparse.RawTextHelpFormatter,
        epilog=textwrap.dedent("""\
            Examples:
              # Full experiment: run on top100, synthesize typos, run on typos, then analyze & plot
              python3 eval_rq1.py -m full

              # Partial: reuse existing typos (in local_crates/typo), run, then analyze & plot
              python3 eval_rq1.py -m partial

              # Cached: skip running, analyze precomputed outputs only (default)
              python3 eval_rq1.py -m cached
        """),
    )

    parser.add_argument(
        "-m", "--mode",
        choices=["full", "partial", "cached"],
        default="cached",
        metavar="MODE",
        help=textwrap.dedent("""\
            Choose how much work to do:

              full
                • Run Cargo-Sherlock on the top 100 crates
                • Generate typosquatted versions
                • Run Cargo-Sherlock on those typo crates
                • Analyze results and plot the heatmap

              partial
                • Reuses existing typosquatted crates (skip generation)
                • Run Cargo-Sherlock on real + typo crates
                • Analyze results and plot the heatmap

              cached  (default)
                • Skip all runs
                • Use existing outputs to analyze and plot
        """),
    )

    parsed_args = parser.parse_args()
    mode = parsed_args.mode

    if mode == "full":
        print("Running in full mode")

        print("1) Running on real crates...")
        run_top100_crates(CSV_FILE, OUTPUT_DIR_REAL)
        print("2) Deleting existing typosquatted crates...")
        if os.path.exists(TARGET_DIR):
            shutil.rmtree(TARGET_DIR, ignore_errors=True)
        os.makedirs(TARGET_DIR, exist_ok=True)
        print("3) Preparing typosquatted crates...")
        prepare_typo_crates(CSV_FILE, TARGET_DIR, LOG_FILE)
        patch_typo_crates_from_tmp(CSV_FILE, TARGET_DIR, LOG_FILE)
        print("4) Running on typosquatted crates...")
        run_typo_crates(OUTPUT_DIR_TYPO, TARGET_DIR)
        print("5) Analyzing results and plotting heatmap...")
        build_severity_csv(CSV_FILE, OUTPUT_DIR_REAL, OUTPUT_DIR_TYPO, OUTPUT_SEVERITY_CSV)
        plot_severity_heatmap_from_csv(
            OUTPUT_SEVERITY_CSV,
            x_order=("SAFE", "LOW_SEVERITY"),
            y_order=("CRITICAL", "HIGH_SEVERITY", "MEDIUM_SEVERITY", "LOW_SEVERITY", "SAFE"),
        )
    elif mode == "partial":
        print("Running in partial mode")

        print("1) Running on real crates...")
        run_top100_crates(CSV_FILE, OUTPUT_DIR_REAL)
        print("2) Running on typosquatted crates...")
        run_typo_crates(OUTPUT_DIR_TYPO, TARGET_DIR)
        print("3) Analyzing results and plotting heatmap...")
        build_severity_csv(CSV_FILE, OUTPUT_DIR_REAL, OUTPUT_DIR_TYPO, OUTPUT_SEVERITY_CSV)
        plot_severity_heatmap_from_csv(
            OUTPUT_SEVERITY_CSV,
            x_order=("SAFE", "LOW_SEVERITY"),
            y_order=("CRITICAL", "HIGH_SEVERITY", "MEDIUM_SEVERITY", "LOW_SEVERITY", "SAFE"),
        )  
    elif mode == "cached":
        print("Running in cached mode: using existing output files for analysis.")
        print("Plotting heatmap from existing severity CSV...")
        plot_severity_heatmap_from_csv(
            OUTPUT_SEVERITY_CSV,
            x_order=("SAFE", "LOW_SEVERITY"),
            y_order=("CRITICAL", "HIGH_SEVERITY", "MEDIUM_SEVERITY", "LOW_SEVERITY", "SAFE"),
        )  


if __name__ == "__main__":
    main()
