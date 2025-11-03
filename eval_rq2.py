import os
import subprocess
from typing import Dict
import regex as re
from rich.console import Console
from rich.table import Table
from rich.text import Text
from rich import box
import logging

# Logging setup
RUN_LOG_FILE = "rq2_run.log" 

logging.basicConfig(
    filename=RUN_LOG_FILE,
    filemode="a",
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    encoding="utf-8"
)
LOGGER = logging.getLogger("rq2")

# Input crates and versions to analyze
crates = [
    ("serde_yaml", "0.9.33"),
    ("serde_yml", "0.0.12"),
    ("fast_log", "1.7.7"),
]

# output dir
output_dir = os.path.join("evaluation", "rq2")
os.makedirs(output_dir, exist_ok=True)

# results table path
RESULTS_TABLE_PATH = "rq2_results.md"

# helpers

def _run_and_log(cmd, *, cwd=None, check=False):
    """Run a subprocess; log stdout/stderr to RUN_LOG_FILE."""
    try:
        LOGGER.info("Running: %s (cwd=%s)", " ".join(cmd), cwd or os.getcwd())
        res = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, check=check)
        if res.stdout:
            LOGGER.info(res.stdout.rstrip("\n"))
        if res.stderr:
            LOGGER.error(res.stderr.rstrip("\n"))
        return res
    except subprocess.CalledProcessError as e:
        if e.stdout:
            LOGGER.info(e.stdout.rstrip("\n"))
        if e.stderr:
            LOGGER.error(e.stderr.rstrip("\n"))
        LOGGER.error("Command failed with exit code %s: %s", e.returncode, " ".join(cmd))
        raise

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

def severity_style(label: str):
    lab = (label or "UNKNOWN").upper()
    if lab == "SAFE": return lab, "bold green", "\x1b[1;32m"
    if "LOW" in lab:  return lab, "bold dark_orange", "\x1b[38;5;208m\x1b[1m"
    if "MEDIUM" in lab: return lab, "bold cyan", "\x1b[1;36m"
    if "HIGH" in lab or "CRITICAL" in lab: return lab, "bold red", "\x1b[1;31m"
    return lab, "bold", "\x1b[1m"

def print_and_save_grouped_table(group_rows, save_path: str):
    """
    Prints the rich table to terminal, and saves the same rendering to a Markdown file.
    """
    console = Console(record=True)  # record=True lets us export the rendered text later
    table = Table(show_header=True, header_style="bold", pad_edge=False, expand=True, box=box.SQUARE)
    table.add_column("Crate", no_wrap=True)
    table.add_column("Trust Cost", justify="right")
    table.add_column("Distrust Cost", justify="right")
    table.add_column("Severity Label", no_wrap=True)

    first = True
    for title, rows in group_rows:
        if not first:
            table.add_row(Text("·" * 40, style="dim"), "", "", "")  # dotted separator
        first = False
        table.add_row(Text(title, style="bold"), "", "", "")
        for r in rows:
            lab, style, _ = severity_style(r["severity"])
            table.add_row(r["crate"], r["trust"] or "", r["distrust"] or "", Text(lab, style=style))

    # Print to terminal
    console.print(table)

    # Save the same rendered text to Markdown with fenced block (preserves spacing)
    rendered = console.export_text(clear=False)
    with open(save_path, "w", encoding="utf-8") as fh:
        fh.write("```text\n")
        fh.write(rendered)
        fh.write("\n```\n")
    LOGGER.info("Saved results table to %s", save_path)

# let's run the tool now
for crate_name, version in crates:
    output_file = os.path.join(output_dir, f"{crate_name}-{version}")
    cmd = ["python3", "sherlock.py", "trust", crate_name, version, "-o", output_file]
    _run_and_log(cmd)

# Special case: faster_log from local path
cwd = os.getcwd()
fast_log_path = os.path.join(cwd, "local_crates", "faster_log")
output_file = os.path.join(output_dir, "faster_log-1.7.8")
cmd = ["python3", "sherlock.py", "trust", "faster_log", "1.7.8", "--path", fast_log_path, "-o", output_file]
_run_and_log(cmd)

# Now parse results and prepare table
PAIRS = {
    "Pair 1: serde_yaml vs serde_yml": ["serde_yaml", "serde_yml"],
    "Pair 2: fast_log vs faster_log":  ["fast_log",  "faster_log"],
}

files = [os.path.join(output_dir, f) for f in os.listdir(output_dir)]
files = [p for p in files if os.path.isfile(p)]  # skip subdirs

rows_by_base: Dict[str, list] = {}
for path in files:
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        parsed = parse_analysis_report(fh.read())
    crate_version_name = os.path.basename(path)
    stem = os.path.splitext(os.path.basename(path))[0]
    base, _version = (stem.rsplit("-", 1) if "-" in stem else (stem, ""))
    row = {
        "crate": crate_version_name,
        "trust": parsed.get("trust_cost"),
        "distrust": parsed.get("distrust_cost"),
        "severity": parsed.get("severity_label"),
    }
    rows_by_base.setdefault(base, []).append(row)

grouped = []
for title, bases in PAIRS.items():
    grp_rows = []
    for b in bases:
        grp_rows.extend(rows_by_base.get(b, []))
    grp_rows.sort(key=lambda r: r["crate"])
    grouped.append((title, grp_rows))

# print and save the table
print_and_save_grouped_table(grouped, RESULTS_TABLE_PATH)

print(f"Results table saved to {RESULTS_TABLE_PATH}")
