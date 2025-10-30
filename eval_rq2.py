import os
import subprocess
from typing import Dict
import regex as re
from rich.console import Console
from rich.table import Table
from rich.text import Text
from rich import box

crates = [
    ("serde_yaml", "0.9.33"),
    ("serde_yml", "0.0.12"),
    ("fast_log", "1.7.7"),
]

# an output dir to store the results 
output_dir = os.path.join("evaluation", "rq2")
os.makedirs(output_dir, exist_ok=True)

# Iterate over each crate and run the command with the output flag.
for crate_name, version in crates:

    output_file = os.path.join(output_dir, f"{crate_name}-{version}")
    # Build the command string
    command = f"python3 sherlock.py trust {crate_name} {version} -o {output_file}"
    
    print(f"Running: {command}")
    # Run the command
    subprocess.run(command, shell=True)

# Now we will run the faster_log locally 

cwd = os.getcwd()
fast_log_path = os.path.join(cwd, "local_crates", "faster_log")
output_file = os.path.join(output_dir, f"faster_log-1.7.8")
command = f"python3 sherlock.py trust faster_log 1.7.8 --path {fast_log_path} -o {output_file}"
print(f"Running: {command}")
subprocess.run(command, shell=True)

# After this we should have all the outputs in the evaluation/rq2 folder

# Now we need to print the table that we have in RQ2

PAIRS = {
    "Pair 1: serde_yaml vs serde_yml": ["serde_yaml", "serde_yml"],
    "Pair 2: fast_log vs faster_log":  ["fast_log",  "faster_log"],
}

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

def severity_style(label: str):
    lab = (label or "UNKNOWN").upper()
    if lab == "SAFE": return lab, "bold green", "\x1b[1;32m"
    if "LOW" in lab:  return lab, "bold dark_orange", "\x1b[38;5;208m\x1b[1m"
    if "MEDIUM" in lab: return lab, "bold cyan", "\x1b[1;36m"
    if "HIGH" in lab or "CRITICAL" in lab: return lab, "bold red", "\x1b[1;31m"
    return lab, "bold", "\x1b[1m"

def print_grouped_table(group_rows):
    try:
        console = Console()
        table = Table(show_header=True, header_style="bold", pad_edge=False,     expand=True,     box=box.SQUARE)
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
        console.print(table)
    except ImportError:
        headers = ["Crate", "Trust Cost", "Distrust Cost", "Severity Label"]
        all_rows = []
        for _, rows in group_rows:
            for r in rows:
                lab, _, _ = severity_style(r["severity"])
                all_rows.append([r["crate"], r["trust"] or "", r["distrust"] or "", lab])
        cols = list(zip(*([headers] + all_rows))) if all_rows else list(zip(*([headers])))
        widths = [max(len(str(x)) for x in col) for col in cols]

        def draw_row(vals, bold=False, sev_color=None):
            parts = []
            for i, v in enumerate(vals):
                s = str(v)
                if i == 3 and sev_color:
                    s = f"{sev_color}{s}\x1b[0m"
                if bold and i != 3:
                    s = f"\x1b[1m{s}\x1b[0m"
                parts.append(s.ljust(widths[i]))
            print(" | ".join(parts))

        sep = "-+-".join("-" * w for w in widths)
        dot_sep = "-·-".join("·" * w for w in widths)

        draw_row(headers, bold=True); print(sep)
        first = True
        for title, rows in group_rows:
            if not first: print(dot_sep)
            first = False
            print(f"\x1b[1m{title}\x1b[0m")
            for r in rows:
                lab, _, ansi = severity_style(r["severity"])
                draw_row([r["crate"], r["trust"] or "", r["distrust"] or "", lab], sev_color=ansi)

files = [os.path.join(output_dir, f) for f in os.listdir(output_dir)]
files = [p for p in files if os.path.isfile(p)]  # skip subdirs

rows_by_base = {}
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

# build groups AFTER reading all files
grouped = []
for title, bases in PAIRS.items():
    grp_rows = []
    for b in bases:
        grp_rows.extend(rows_by_base.get(b, []))
    grp_rows.sort(key=lambda r: r["crate"])
    grouped.append((title, grp_rows))

print_grouped_table(grouped)