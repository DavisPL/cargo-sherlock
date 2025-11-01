import os
import re
import json
import subprocess
from datetime import datetime
from functools import lru_cache
from typing import Dict, List, Union, Optional
from concurrent.futures import ThreadPoolExecutor, as_completed
import threading
import csv
import requests
from packaging import version as pkg_version
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from tqdm import tqdm
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt

DATA_FILE = "helpers/data.txt"
OUTPUT_DIR = os.path.join("evaluation", "rq3")
FAILED_PATH = "rustsec_failed.txt"
DEFAULT_LOG = os.path.join("evaluation", "rustsec_run.log")

# ---------- Locks ----------
LOG_LOCK = threading.Lock()
FAIL_LOCK = threading.Lock()

# ---------- Thread-local session (safe + keep-alive) ----------
_thread_local = threading.local()

def make_session() -> requests.Session:
    s = requests.Session()
    retries = Retry(
        total=3,
        backoff_factor=0.5,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=frozenset(["GET"]),
    )
    adapter = HTTPAdapter(max_retries=retries, pool_connections=20, pool_maxsize=20)
    s.mount("http://", adapter)
    s.mount("https://", adapter)
    s.headers.update({"User-Agent": "reqwest"})
    return s

def get_session() -> requests.Session:
    sess = getattr(_thread_local, "session", None)
    if sess is None:
        sess = make_session()
        _thread_local.session = sess
    return sess

# ---------- Utilities ----------
def read_dicts_from_txt(text_file: str, separator: str = "\n---\n") -> List[str]:
    with open(text_file, "r", encoding="utf-8") as f:
        content = f.read()
    return [s for s in content.split(separator) if s.strip()]

_KV = re.compile(r"(\w+):\s*(.+)")
_VERSION = re.compile(r"(\d+\.\d+\.\d+)")

def parse_dict_string(dict_string: str) -> dict:
    def string_to_dict(s: str) -> Union[dict, str]:
        try:
            return json.loads(s.replace("'", '"'))
        except json.JSONDecodeError:
            return s

    result = {}
    for line in dict_string.splitlines():
        line = line.strip()
        if not line:
            continue
        m = _KV.match(line)
        if not m:
            continue
        key, value = m.groups()
        if value.startswith("{") or value.startswith("["):
            result[key] = string_to_dict(value)
        else:
            result[key] = value
    return result

def file_nonempty(path: str) -> bool:
    try:
        return os.path.getsize(path) > 0
    except OSError:
        return False

# ---------- Crates.io versions (cached) ----------
@lru_cache(maxsize=4096)
def get_versions(crate: str) -> Optional[List[str]]:
    url = f"https://crates.io/api/v1/crates/{crate}/versions"
    try:
        resp = get_session().get(url, timeout=10)
        resp.raise_for_status()
    except requests.RequestException:
        return None
    data = resp.json()
    if "errors" in data:
        return None
    versions = [v["num"] for v in data.get("versions", [])]
    versions = [v for v in versions if not any(ch.isalpha() for ch in v)]
    versions.sort(key=pkg_version.parse)
    return versions or None

# ---------- Advisory indexing & candidate computation ----------
def build_advisory_index() -> Dict[str, List[dict]]:
    out: Dict[str, List[dict]] = {}
    for s in read_dicts_from_txt(DATA_FILE):
        rec = parse_dict_string(s)
        pkg_name = rec.get("package", {}).get("name", "").split("(")[0]
        if not pkg_name:
            continue
        out.setdefault(pkg_name, []).append(rec)
    return out

def compute_candidate_version(crate: str, advisories: List[dict]) -> Optional[str]:
    # Case 1: explicit "no patched versions" — take highest advisory version given
    no_patch_candidates: List[pkg_version.Version] = []
    for rec in advisories:
        patched = (rec.get("patched") or "").strip()
        if patched == "no patched versions":
            v_str = rec.get("version")
            if v_str:
                try:
                    no_patch_candidates.append(pkg_version.parse(v_str))
                except Exception:
                    pass
    if no_patch_candidates:
        return str(max(no_patch_candidates))

    # Collect thresholds (can be multiple across advisories)
    thresholds: List[pkg_version.Version] = []
    for rec in advisories:
        patched = (rec.get("patched") or "").strip()
        if not patched:
            continue
        for m in _VERSION.findall(patched):
            try:
                thresholds.append(pkg_version.parse(m))
            except Exception:
                pass

    available = get_versions(crate)
    if available:
        avail_parsed = [pkg_version.parse(v) for v in available]
        candidates: List[pkg_version.Version] = []
        for thr in thresholds:
            below = [v for v in avail_parsed if v < thr]
            if below:
                candidates.append(max(below))
        if candidates:
            return str(max(candidates))
        # Fallback: latest
        return str(avail_parsed[-1])

    # If crates.io failed, try any advisory 'version' we have as a weak fallback
    fallback_advisory_versions: List[pkg_version.Version] = []
    for rec in advisories:
        v_str = rec.get("version")
        if v_str:
            try:
                fallback_advisory_versions.append(pkg_version.parse(v_str))
            except Exception:
                pass
    if fallback_advisory_versions:
        return str(max(fallback_advisory_versions))

    return None

# ---------- Thread worker ----------
def process_crate(
    crate: str,
    advisories: List[dict],
    timeout_sec: int,
    log_path: str,
) -> str:
    """
    Returns a status string for progress bar display; writes logs under LOG_LOCK.
    """
    candidate = compute_candidate_version(crate, advisories)
    if not candidate:
        block = f"[SKIP] {crate}: no candidate version derived."
        with LOG_LOCK:
            with open(log_path, "a", encoding="utf-8") as lf:
                lf.write(block + "\n")
        return f"SKIP {crate}"

    out_file = os.path.join(OUTPUT_DIR, f"{crate}-{candidate}")

    # Skip if output already exists and is non-empty
    if file_nonempty(out_file):
        block = f"[SKIP] {crate}@{candidate}: output already present."
        with LOG_LOCK:
            with open(log_path, "a", encoding="utf-8") as lf:
                lf.write(block + "\n")
        return f"SKIP {crate}"

    cmd = [
        "python3", "sherlock.py", "trust",
        crate, candidate, "-o", out_file
    ]

    # Run subprocess and capture output to avoid interleaving
    header = []
    header.append("=" * 80)
    header.append(f"CRATE: {crate}")
    header.append(f"CANDIDATE: {candidate}")
    header.append(f"OUTPUT: {out_file}")
    header.append(f"COMMAND: {' '.join(cmd)}")
    header.append("-" * 80)

    try:
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout_sec,
            text=True,
            shell=False,
        )
        rc = result.returncode
        output = result.stdout or ""
    except subprocess.TimeoutExpired:
        rc = None
        output = f"[TIMEOUT] {crate} exceeded {timeout_sec}s.\n"

    # Compose a single log block and write it atomically under lock
    log_block = "\n".join(header) + "\n" + output
    if rc is None:
        # timeout
        with LOG_LOCK:
            with open(log_path, "a", encoding="utf-8") as lf:
                lf.write(log_block)
                lf.write("\n")
        with FAIL_LOCK:
            with open(FAILED_PATH, "a", encoding="utf-8") as f:
                f.write(crate + "\n")
        return f"TIMEOUT {crate}"

    if rc != 0:
        with LOG_LOCK:
            with open(log_path, "a", encoding="utf-8") as lf:
                lf.write(log_block)
                lf.write(f"[FAIL] rc={rc} for {crate}.\n")
        with FAIL_LOCK:
            with open(FAILED_PATH, "a", encoding="utf-8") as f:
                f.write(crate + "\n")
        return f"FAIL {crate}"

    # Success
    with LOG_LOCK:
        with open(log_path, "a", encoding="utf-8") as lf:
            lf.write(log_block)
            lf.write(f"[OK] {crate}@{candidate}\n")
    return f"OK {crate}"

def run_sherlock_on_vulnerable_rustsec_crates(
    log_file: Optional[str] = None,
    timeout_sec: int = 300,
    max_workers: int = 10,
):
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    log_path = log_file or DEFAULT_LOG

    index = build_advisory_index()
    crates = list(index.keys())

    # Write start banner
    with LOG_LOCK:
        with open(log_path, "a", encoding="utf-8") as lf:
            lf.write(f"\n===== Run started {datetime.now().isoformat()} =====\n")
            lf.write(f"Total unique crates: {len(crates)}\n")

    futures = []
    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        for crate in crates:
            futures.append(
                pool.submit(process_crate, crate, index[crate], timeout_sec, log_path)
            )

        # Progress from main thread
        for _ in tqdm(as_completed(futures), total=len(futures), desc="Processing crates", unit="crate"):
            pass

    with LOG_LOCK:
        with open(log_path, "a", encoding="utf-8") as lf:
            lf.write(f"===== Run finished {datetime.now().isoformat()} =====\n")

def rerun_failed():
    files = os.listdir(OUTPUT_DIR)
    # get all the empty files 
    empty_files = [f for f in files if not file_nonempty(os.path.join(OUTPUT_DIR, f))]
    print(len(empty_files))
    print(empty_files)
    for f in empty_files:
        name, ver = f.rsplit("-", 1)
        command = f"python3 sherlock.py trust {name} {ver} -o {os.path.join(OUTPUT_DIR, f)}"
        print(f"Re-running: {command}")
        subprocess.run(command, shell=True)

# Now we need to make the plot
REPORTS_DIR = "evaluation/rq3/"
OUTPUT_CSV  = "rq3_rustsec.csv"
_FILENAME_SEMVER = re.compile(r"^(?P<base>.+)-(?P<ver>\d+\.\d+\.\d+)$")

ANSI_RE = re.compile(r"\x1B\[[0-?]*[ -/]*[@-~]")

def strip_ansi(s: str) -> str:
    return ANSI_RE.sub("", s)

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


def build_rq3_csv(reports_dir: str, out_csv: str) -> None:
    """
    Scan sherlock outputs in `reports_dir`, parse Trust/Distrust/Severity using the
    existing RQ2 `parse_analysis_report` helper, and write a CSV.
    """
    os.makedirs(os.path.dirname(out_csv) or ".", exist_ok=True)

    headers = [
        "Crate Name",     # e.g., "serde_yaml-0.9.33"
        "Severity Label", # e.g., "LOW", "MEDIUM", etc.
    ]

    try:
        entries = [os.path.join(reports_dir, f) for f in os.listdir(reports_dir)]
    except FileNotFoundError:
        raise SystemExit(f"Reports directory not found: {reports_dir}")

    files = [p for p in entries if os.path.isfile(p)]
    print(f"Processing {len(files)} report files...")

    with open(out_csv, "w", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh)
        writer.writerow(headers)

        for path in tqdm(files, desc="Building rq3 CSV", unit="file"):
            name = os.path.basename(path)
            m = _FILENAME_SEMVER.match(name)
            if not m:
                # Not a standard "<base>-<x.y.z>" report — skip
                continue

            base = m.group("base")
            ver  = m.group("ver")

            try:
                with open(path, "r", encoding="utf-8", errors="r`eplace") as fh2:
                    parsed = parse_analysis_report(fh2.read())  
            except Exception:
                parsed = {"severity_label": "UNKNOWN"}

            writer.writerow([
                name,                            
                (parsed.get("severity_label") or "UNKNOWN"),
            ])

def build_rustsec_advisories_csv(data_file: str, out_csv: str) -> None:
    """
    Read helpers/data.txt-style advisories and write:
    CrateName, RustSec Severity Label, Advisory Type
    One row per advisory record found in the file.
    """
    rows = []
    for s in read_dicts_from_txt(data_file):
        rec = parse_dict_string(s)

        base = (rec.get("package", {}) or {}).get("name", "")
        base = base.split("(")[0].strip() if isinstance(base, str) else ""
        ver  = (rec.get("version") or "").strip()

        name = f"{base}-{ver}" if base and ver else base

        rustsec_label = (rec.get("severity") or rec.get("rustsec_severity") or "UNCATEGORIZED")
        rustsec_label = str(rustsec_label).upper().strip()

        advisory_type = (
            rec.get("advisory_type")
            or (rec.get("advisory", {}) or {}).get("type")
            or rec.get("type")
            or "UNKNOWN"
        )
        advisory_type = str(advisory_type).upper().strip()

        if name:
            rows.append([name, rustsec_label, advisory_type])

    os.makedirs(os.path.dirname(out_csv) or ".", exist_ok=True)
    with open(out_csv, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["name", "rustsec_label", "advisory_type"])
        w.writerows(rows)

    print(f"Wrote {len(rows)} rows to {out_csv}")



if __name__ == "__main__":
    # run_sherlock_on_vulnerable_rustsec_crates()
    rerun_failed()
    # build_rq3_csv(REPORTS_DIR, OUTPUT_CSV)
    # build_rustsec_advisories_csv(DATA_FILE, os.path.join("evaluation", "rustsec_advisories.csv"))


