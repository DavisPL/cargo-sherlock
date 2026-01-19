import os
import re
import json
import csv
import subprocess
from datetime import datetime
from typing import Dict, List, Union, Optional
import requests
from packaging import version as pkg_version
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from concurrent.futures import ThreadPoolExecutor, as_completed
import threading
import argparse
import textwrap

# Constants
DATA_FILE   = "helpers/data.txt"
REPORTS_DIR = "evaluation/rq3"
OUTPUT_CSV  = os.path.join("evaluation", "rq3_rustsec.csv")
RUSTSEC_CSV = os.path.join("evaluation", "rustsec_advisories.csv")
MERGED_CSV  = os.path.join("evaluation", "rq3_rustsec_merged.csv")
RUN_LOG     = os.path.join("evaluation", "rustsec_run.log")

# Parsing helpers
_KV = re.compile(r"(\w+):\s*(.+)")
_VERSION_PAT = re.compile(r"(\d+\.\d+\.\d+)")
_FILENAME_SEMVER = re.compile(r"^(?P<base>.+)-(?P<ver>\d+\.\d+\.\d+)$")
_ANSI = re.compile(r"\x1B\[[0-?]*[ -/]*[@-~]")
_NAME_VER_RE = re.compile(r"^(?P<base>.+)-\d+\.\d+\.\d+$")

def strip_ansi(s: str) -> str:
    return _ANSI.sub("", s)

def read_dicts_from_txt(text_file: str, separator: str = "\n---\n") -> List[str]:
    with open(text_file, "r", encoding="utf-8") as f:
        content = f.read()
    return [s for s in content.split(separator) if s.strip()]

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

def _base_name(s: str) -> str:
    s = str(s).strip()
    m = _NAME_VER_RE.match(s)
    return m.group("base") if m else s

def _parse_analysis_report(text: str):
    t = strip_ansi(text).replace("\u00A0", " ")
    m = re.search(r"Severity\s*Label:\s*([A-Z0-9_\-]+)", t, flags=re.IGNORECASE)
    sev = m.group(1) if m else None
    return {"severity_label": sev}

# crates.io versions 
def get_versions(crate: str) -> Optional[List[str]]:
    """
    Fetch versions from crates.io for a crate.
    Returns a sorted list of numeric semver strings, or None on error.
    """
    url = f"https://crates.io/api/v1/crates/{crate}/versions"
    headers = {"User-Agent": "reqwest"}
    try:
        resp = requests.get(url, headers=headers, timeout=10)
        resp.raise_for_status()
        data = resp.json()
    except Exception:
        return None

    if not isinstance(data, dict) or "versions" not in data:
        return None

    versions = [v.get("num") for v in data.get("versions", []) if isinstance(v, dict)]
    versions = [v for v in versions if isinstance(v, str) and not any(ch.isalpha() for ch in v)]
    try:
        versions.sort(key=pkg_version.parse)
    except Exception:
        return None
    return versions or None


def build_advisory_index() -> Dict[str, List[dict]]:
    out: Dict[str, List[dict]] = {}
    for s in read_dicts_from_txt(DATA_FILE):
        rec = parse_dict_string(s)
        pkg_name = (rec.get("package", {}) or {}).get("name", "").split("(")[0]
        pkg_name = pkg_name.strip()
        if not pkg_name:
            continue
        out.setdefault(pkg_name, []).append(rec)
    return out

def _extract_thresholds(patched: str) -> List[str]:
    """
    Extract semver thresholds from an advisory 'patched' string.
    Handles: '>=1.2.3', '^1.4.0 and ^2.3.1', '>= 3.7.2, < 3.8.0', etc.
    We collect all x.y.z tokens; the selection logic uses them as upper bounds.
    """
    if not patched:
        return []
    return re.findall(r'(\d+\.\d+\.\d+)', patched)

def _best_available_below(crate: str, threshold_str: str) -> Optional[str]:
    """Pick the highest available version strictly less than 'threshold_str'."""
    available = get_versions(crate)
    if not available:
        return None
    thr = pkg_version.parse(threshold_str)
    below = [pkg_version.parse(v) for v in available if pkg_version.parse(v) < thr]
    return str(max(below)) if below else None

def compute_candidate_version(crate: str, advisories: List[dict]) -> Optional[str]:
    """
    Version selection:
      1) If any advisory has 'no patched versions', use the highest advisory 'version'.
      2) Otherwise, collect thresholds from 'patched' fields. For each threshold,
         pick the highest available version < threshold. Take the max across all.
      3) Fallback to the latest available crates.io version.
      4) Final fallback to highest advisory 'version'.
    """
    # 1) explicit "no patched versions" -> use highest advisory version
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

    # 2) thresholds -> highest available < threshold
    threshold_candidates: List[pkg_version.Version] = []
    thresholds: List[str] = []
    for rec in advisories:
        thresholds.extend(_extract_thresholds((rec.get("patched") or "").strip()))
    if thresholds:
        seen = set()
        for thr in thresholds:
            if not thr or thr in seen:
                continue
            seen.add(thr)
            chosen = _best_available_below(crate, thr)
            if chosen:
                try:
                    threshold_candidates.append(pkg_version.parse(chosen))
                except Exception:
                    pass
        if threshold_candidates:
            return str(max(threshold_candidates))

    # 3) fallback: latest available on crates.io
    available = get_versions(crate)
    if available:
        try:
            return str(max((pkg_version.parse(v) for v in available)))
        except Exception:
            pass

    # 4) fallback: highest advisory 'version'
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

_log_lock = threading.Lock()

def _run_one(crate: str, advisories: List[dict]) -> None:
    candidate = compute_candidate_version(crate, advisories)
    if not candidate:
        with _log_lock:
            with open(RUN_LOG, "a", encoding="utf-8") as lf:
                lf.write(f"[SKIP] {crate}: no candidate version\n")
        return

    out_file = os.path.join(REPORTS_DIR, f"{crate}-{candidate}")
    if os.path.exists(out_file) and os.path.getsize(out_file) > 0:
        with _log_lock:
            with open(RUN_LOG, "a", encoding="utf-8") as lf:
                lf.write(f"[SKIP] {crate}@{candidate}: output exists\n")
        return

    cmd = ["python3", "sherlock.py", "trust", crate, candidate, "-o", out_file]
    try:
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            shell=False,
            timeout=900,
        )
        rc = result.returncode
        output = result.stdout or ""
    except subprocess.TimeoutExpired:
        rc = None
        output = f"[TIMEOUT] {crate}\n"

    header = [
        "=" * 80,
        f"CRATE: {crate}",
        f"CANDIDATE: {candidate}",
        f"OUTPUT: {out_file}",
        f"COMMAND: {' '.join(cmd)}",
        "-" * 80,
    ]
    block = "\n".join(header) + "\n" + output
    with _log_lock:
        with open(RUN_LOG, "a", encoding="utf-8") as lf:
            lf.write(block + ("\n[OK]\n" if rc == 0 else f"\n[RC={rc}]\n"))

def run_sherlock_all(max_workers: int = 10):
    """
    Threaded implementation:
      - Builds advisory index once
      - Submits one job per unique crate
      - Logs start/finish with totals
    """
    os.makedirs(REPORTS_DIR, exist_ok=True)
    index = build_advisory_index()
    crates = sorted(index.keys())

    with open(RUN_LOG, "a", encoding="utf-8") as lf:
        lf.write(f"\n===== Run started {datetime.now().isoformat()} =====\n")
        lf.write(f"Total crates: {len(crates)}\n")

    # Run concurrently
    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        futures = {pool.submit(_run_one, crate, index[crate]): crate for crate in crates}
        for _ in as_completed(futures):
            pass  # task-level logging already done

    with open(RUN_LOG, "a", encoding="utf-8") as lf:
        lf.write(f"===== Run finished {datetime.now().isoformat()} =====\n")

# builds CSV files from reports
def build_rq3_csv(reports_dir: str = REPORTS_DIR, out_csv: str = OUTPUT_CSV) -> None:
    os.makedirs(os.path.dirname(out_csv) or ".", exist_ok=True)
    try:
        entries = [os.path.join(reports_dir, f) for f in os.listdir(reports_dir)]
    except FileNotFoundError:
        raise SystemExit(f"Reports directory not found: {reports_dir}")

    files = [p for p in entries if os.path.isfile(p)]
    with open(out_csv, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["Crate Name", "Severity Label"])
        for path in files:
            name = os.path.basename(path)
            m = _FILENAME_SEMVER.match(name)
            if not m:
                continue
            try:
                with open(path, "r", encoding="utf-8", errors="replace") as fh2:
                    parsed = _parse_analysis_report(fh2.read())
            except Exception:
                parsed = {"severity_label": "UNKNOWN"}
            w.writerow([name, parsed.get("severity_label") or "UNKNOWN"])

def build_rustsec_advisories_csv():
    codex = read_dicts_from_txt(DATA_FILE)
    with open(RUSTSEC_CSV, "w", newline="", encoding="utf-8") as csvfile:
        fieldnames = ["crate_name", "rustsec_label", "advisory_type"]
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()

        for data in codex:
            record = parse_dict_string(data)

            package_field = (record.get("package", {}) or {}).get("name", "")
            if "(" in package_field:
                parts = package_field.split("(")
                crate_name = parts[0].strip()
            else:
                crate_name = package_field.strip()

            classification = record.get("classification", "CRITICAL")
            advisory_type = record.get("type", None)

            writer.writerow({
                "crate_name": crate_name,
                "rustsec_label": classification,
                "advisory_type": advisory_type
            })

def combine_rq3_and_rustsec(
    rq3_csv: str = OUTPUT_CSV,
    rustsec_csv: str = RUSTSEC_CSV,
    out_csv: str = MERGED_CSV,
) -> None:
    df_rq3 = pd.read_csv(rq3_csv)            # "Crate Name", "Severity Label"
    df_rs  = pd.read_csv(rustsec_csv)        # "crate_name", "rustsec_label", "advisory_type"

    for col in ["Crate Name", "Severity Label"]:
        if col not in df_rq3.columns:
            raise KeyError(f"rq3 file missing column: {col}")
    for col in ["crate_name", "rustsec_label", "advisory_type"]:
        if col not in df_rs.columns:
            raise KeyError(f"rustsec file missing column: {col}")

    df_rq3["crate_name"] = df_rq3["Crate Name"].map(_base_name)
    df_rs["crate_name"]  = df_rs["crate_name"].map(_base_name)

    df_rs_collapsed = (
        df_rs.groupby("crate_name", as_index=False)
             .agg({
                 "rustsec_label": lambda s: "|".join(sorted(set(str(x).strip() for x in s if pd.notna(x) and str(x).strip()))),
                 "advisory_type": lambda s: "|".join(sorted(set(str(x).strip() for x in s if pd.notna(x) and str(x).strip())))
             })
    )

    merged = pd.merge(
        df_rq3,
        df_rs_collapsed,
        on="crate_name",
        how="left",
        validate="m:1",
    )
    merged["rustsec_label"] = merged["rustsec_label"].fillna("Not in RustSec")
    out = merged.rename(columns={"Severity Label": "sherlock_label"})[
        ["crate_name", "sherlock_label", "rustsec_label", "advisory_type"]
    ]

    os.makedirs(os.path.dirname(out_csv) or ".", exist_ok=True)
    out.to_csv(out_csv, index=False)

def plot_rustsec_download_distribution(cached=True):
    # Data from the table
    data = {}
    if cached:
        data = {
                "Top Percent of crates.io": [
                    "Top 5%", "Top 10%", "Top 20%", "Top 30%", "Top 40%",
                "Top 50%", "Top 60%", "Top 70%", "Top 80%"
            ],
            "Percentage of RustSec Crates": [
                63.6, 75.1, 86.3, 92.2, 95.4, 97.9, 99.4, 99.6, 100.0
            ]
        }
    else:
        pass

    df = pd.DataFrame(data)

    # Use a pleasant style.
    plt.style.use("ggplot")

    fig, ax = plt.subplots(figsize=(6, 4))

    # Create a numeric index for bars
    x = np.arange(len(df))

    # Generate a gradient of blues for the bars
    bar_colors = plt.cm.Blues(np.linspace(0.5, 0.9, len(df)))

    # Plot a bar chart
    bars = ax.bar(x, df["Percentage of RustSec Crates"], 
                color=bar_colors, edgecolor="black")

    # X-axis labels
    ax.set_xticks(x)
    ax.set_xticklabels(df["Top Percent of crates.io"], rotation=45, ha="right")

    # Axis labels and title
    ax.set_xlabel("Top Percent of crates.io", fontsize=12)
    ax.set_ylabel("Percentage of RustSec Crates", fontsize=12)
    # ax.set_title("Distribution of crates in RustSec by downloads", 
                # fontsize=14, fontweight="bold")

    # Remove top/right spines for a cleaner look
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)

    # Annotate each bar with its value, skipping 0 if any
    for bar in bars:
        height = bar.get_height()
        if height > 0:
            ax.annotate(f"{height:.1f}%",
                        xy=(bar.get_x() + bar.get_width() / 2, height),
                        xytext=(0, 3),  # 3 points vertical offset
                        textcoords="offset points",
                        ha="center", va="bottom", fontsize=10)

    plt.tight_layout()
    plt.savefig("rustsec-percentiles.pdf", bbox_inches="tight")
    # plt.show()


def plot_rustsec_grouped_by_sherlock(
    in_csv: str,
    out_pdf: str,
    include_uncategorized: bool = True,
) -> pd.DataFrame:
    df = pd.read_csv(in_csv)

    # keep only rows that have a RustSec label
    df = df[df["rustsec_label"].ne("Not in RustSec")]

    # split "A|B|C" labels into separate rows
    df = df.assign(rustsec_label=df["rustsec_label"].astype(str).str.split("|")).explode("rustsec_label")
    df["rustsec_label"] = df["rustsec_label"].str.strip()

    rustsec_order = ["INFO", "LOW", "MEDIUM", "HIGH", "CRITICAL", "Uncategorized"]
    if not include_uncategorized:
        rustsec_order.remove("Uncategorized")

    sherlock_order = ["SAFE", "LOW_SEVERITY", "MEDIUM_SEVERITY", "HIGH_SEVERITY", "CRITICAL"]

    # keep only desired buckets + order them
    df = df[df["rustsec_label"].isin(rustsec_order) & df["sherlock_label"].isin(sherlock_order)]

    counts = (
        df.groupby(["rustsec_label", "sherlock_label"])
          .size()
          .unstack("sherlock_label", fill_value=0)
          .reindex(index=rustsec_order, columns=sherlock_order, fill_value=0)
    )

    # same colors as synthesizer in paper
    palette = {
        "SAFE": "#B4FFB3",
        "LOW_SEVERITY": "#F1FF99",
        "MEDIUM_SEVERITY": "#B3EDFF",
        "HIGH_SEVERITY": "#DDB3FF",
        "CRITICAL": "#FB9393",
    }

    # positions
    x = np.arange(len(rustsec_order))
    n_series = len(sherlock_order)
    bar_w = 0.8 / n_series
    group_w = n_series * bar_w
    base = x - group_w / 2.0

    fig, ax = plt.subplots(figsize=(12, 8), facecolor="white")
    ax.set_facecolor("#f3f4f6")

    # symmetric side padding 
    side_pad = (1.0 - group_w) / 2.0
    ax.set_xlim(-0.5 - side_pad, len(rustsec_order) - 0.5 + side_pad)

    ax.grid(True, which="major", axis="both", color="white", linewidth=1.2)
    ax.minorticks_on()
    ax.grid(True, which="minor", axis="both", color="white", linewidth=0.6)
    ax.set_axisbelow(True)

    # bars
    for i, lab in enumerate(sherlock_order):
        vals = counts[lab].values
        bars = ax.bar(base + i * bar_w, vals, bar_w, label=lab,
                      edgecolor="black", color=palette[lab])
        for b in bars:
            h = b.get_height()
            if h > 0:
                ax.text(b.get_x() + b.get_width()/2, h, f"{int(h)}",
                        ha="center", va="bottom", fontsize=11, fontweight="bold")

    # axes/labels
    ax.set_xticks(x)
    ax.set_xticklabels(rustsec_order, fontsize=14)
    ax.set_xlabel("RustSec Label", fontsize=16)
    ax.set_ylabel("Number of Crates", fontsize=16)
    ax.tick_params(axis="y", labelsize=14)

    # legend
    leg = ax.legend(title="Cargo-Sherlock Label", fontsize=14, title_fontsize=14, ncol=2,
                    frameon=True, framealpha=0.95)
    leg.get_frame().set_facecolor("white")
    leg.get_frame().set_edgecolor("black")

    plt.tight_layout()
    os.makedirs(os.path.dirname(out_pdf) or ".", exist_ok=True)
    plt.savefig(out_pdf, bbox_inches="tight")
    plt.close(fig)

    return counts

def main():

    parser = argparse.ArgumentParser(
        prog="eval_rq3.py",
        description="Evaluate RQ3: Cargo-Sherlock on RustSec crates",
        formatter_class=argparse.RawTextHelpFormatter,
        epilog=textwrap.dedent("""\
            Examples:
            # Full: run Cargo-Sherlock on all RustSec crates, plot the label and download distributions
            python3 eval_rq3.py --mode full

            # Cached: use existing reports only (default)
            python3 eval_rq3.py --mode cached
        """),
    )

    parser.add_argument(
        "--mode", "-m",
        choices=["full", "cached"],
        default="cached",
        metavar="MODE",
        help=textwrap.dedent("""\
            Mode of operation:

            full
                • Run Cargo-Sherlock on all RustSec crates
                • Compare RustSec labels to Cargo-Sherlock labels
                • Plot label distribution and RustSec downloads distribution

            cached (default)
                • Skip running Cargo-Sherlock
                • Use existing reports to compile CSVs and plot distributions
        """),
    )

    args = parser.parse_args()
    mode = args.mode


    if mode == "full":
        print("Running in 'full' mode...")
        print("1) Running Cargo-Sherlock on RustSec crates...")
        run_sherlock_all()
        print("2) Compiling Results into a CSV...")
        build_rq3_csv()
        print("3) Building a CSV with RustSec advisories labels...")
        build_rustsec_advisories_csv()
        print("4) Combining Cargo-Sherlock and RustSec Labels...")
        combine_rq3_and_rustsec()
        print("5) Plotting RustSec distribution grouped by Cargo-Sherlock labels - saved at 'rustsec-distribution.pdf'...")
        plot_rustsec_grouped_by_sherlock(MERGED_CSV, "rustsec-distribution.pdf")
        print("6) Plotting rustsec downloads distribution - saved at 'rustsec-percentiles.pdf'...")
        plot_rustsec_download_distribution()

    elif mode == "cached":
        print("Running in 'cached' mode...")
        print("1) Plotting RustSec distribution grouped by Cargo-Sherlock labels - saved at 'rustsec-distribution.pdf'...")
        plot_rustsec_grouped_by_sherlock(MERGED_CSV, "rustsec-distribution.pdf")
        print("2) Plotting rustsec downloads distribution - saved at 'rustsec-percentiles.pdf'...")
        plot_rustsec_download_distribution()


if __name__ == "__main__":
    main()