import os
import csv
import time
import subprocess
import json
from concurrent.futures import ThreadPoolExecutor, as_completed

import pandas as pd
import numpy as np
import matplotlib as mpl
import matplotlib.pyplot as plt
import seaborn as sns
from scipy.optimize import curve_fit

CSV_FILE = "random1000_crates.csv"
OUTPUT_HORN_CSV = "random_horn_results.csv"
OUTPUT_NAIVE_CSV = "random_naive_results.csv"
DEP_COUNT_CSV = "random1000_dep_count.csv"
CACHE_DIR = "logs/cache"
TIMEOUT_SECS = 600
MAX_WORKERS = 10
TOTAL_EXPECTED = 1000  # unused

def _process_one(crate_name: str, version: str, base_out_dir: str, naive: bool = False) -> tuple[str, float, int | None]:
    crate_ver = f"{crate_name}-{version}"
    output_file = os.path.join(base_out_dir, crate_ver)
    cmd = ["python3", "sherlock.py", "trust", crate_name, version, "-o", output_file]
    if naive:
        cmd.insert(4, "--no-horn")
    print(f"[START] {' '.join(cmd)}")
    start = time.perf_counter()
    try:
        proc = subprocess.run(cmd, timeout=TIMEOUT_SECS)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        elapsed = time.perf_counter() - start
        print(f"[TIMEOUT] {crate_ver} after {elapsed:.2f}s")
        return crate_ver, elapsed, None
    elapsed = time.perf_counter() - start
    print(f"[DONE] {crate_ver} in {elapsed:.2f}s (rc={rc})")
    return crate_ver, elapsed, rc

def run_top_crates_horn():
    base_out_dir = os.path.join("evaluation", "rq4")
    os.makedirs(base_out_dir, exist_ok=True)
    tasks: list[tuple[str, str]] = []
    with open(CSV_FILE, newline="") as in_f:
        reader = csv.DictReader(in_f)
        for row in reader:
            tasks.append((row["name"], row["version"]))
    with open(OUTPUT_HORN_CSV, mode="w", newline="") as out_f:
        writer = csv.writer(out_f)
        writer.writerow(["crate-version", "time_seconds", "return_code"])
        out_f.flush()
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            futures = {pool.submit(_process_one, crate, ver, base_out_dir): (crate, ver) for crate, ver in tasks}
            for fut in as_completed(futures):
                crate, ver = futures[fut]
                try:
                    crate_ver, elapsed, rc = fut.result()
                except Exception as e:
                    crate_ver, elapsed, rc = f"{crate}-{ver}", 0.0, -1
                    print(f"[ERROR] {crate_ver}: {e}")
                writer.writerow([crate_ver, f"{elapsed:.2f}", "" if rc is None else rc])
                out_f.flush()

def run_top_crates_naive():
    base_out_dir = os.path.join("evaluation", "naive", "rq4")
    os.makedirs(base_out_dir, exist_ok=True)
    tasks: list[tuple[str, str]] = []
    with open(CSV_FILE, newline="") as in_f:
        reader = csv.DictReader(in_f)
        for row in reader:
            tasks.append((row["name"], row["version"]))
    with open(OUTPUT_NAIVE_CSV, mode="w", newline="") as out_f:
        writer = csv.writer(out_f)
        writer.writerow(["crate-version", "time_seconds", "return_code"])
        out_f.flush()
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            futures = {pool.submit(_process_one, crate, ver, base_out_dir, True): (crate, ver) for crate, ver in tasks}
            for fut in as_completed(futures):
                crate, ver = futures[fut]
                try:
                    crate_ver, elapsed, rc = fut.result()
                except Exception as e:
                    crate_ver, elapsed, rc = f"{crate}-{ver}", 0.0, -1
                    print(f"[ERROR] {crate_ver}: {e}")
                writer.writerow([crate_ver, f"{elapsed:.2f}", "" if rc is None else rc])
                out_f.flush()

def get_dependency_counts(
    cache_dir: str = CACHE_DIR,
    input_crates_csv: str = CSV_FILE,
    output_dep_csv: str = DEP_COUNT_CSV,
) -> pd.DataFrame:
    rows = []
    failed_files = []
    if os.path.isdir(cache_dir):
        for filename in os.listdir(cache_dir):
            if not filename.endswith(".json"):
                continue
            path = os.path.join(cache_dir, filename)
            base = filename[:-5]
            crate_name, crate_version = (base.rsplit("-", 1) if "-" in base else (base, "0.0.0"))
            try:
                with open(path, "r", encoding="utf-8") as f:
                    data = json.load(f)
            except json.JSONDecodeError as e:
                print(f"JSON decode error in file {filename}: {e}")
                failed_files.append(filename)
                continue
            deps = data.get("dependencies", [])
            rows.append({"crate_name": crate_name, "version": crate_version, "dependency_count": len(deps)})
    else:
        print(f"[WARN] Cache dir not found: {cache_dir}")

    df_deps = pd.DataFrame(rows)
    print("Dependency counts extracted:")
    print(df_deps.head())

    df_crates = pd.read_csv(input_crates_csv)
    if "crate_name" not in df_crates.columns and "name" in df_crates.columns:
        df_crates = df_crates.rename(columns={"name": "crate_name"})
    if "crate_name" not in df_crates.columns or "version" not in df_crates.columns:
        raise KeyError("Input CSV must have columns ['name' or 'crate_name', 'version'].")

    df_out = pd.merge(df_crates, df_deps, on=["crate_name", "version"], how="left")
    if "name" not in df_out.columns:
        df_out = df_out.rename(columns={"crate_name": "name"})
    if "dependency_count" not in df_out.columns:
        df_out["dependency_count"] = np.nan

    df_out.to_csv(output_dep_csv, index=False)
    print(f"[OK] Wrote dependency counts to {output_dep_csv}")
    return df_out

def _split_crate_ver(col: pd.Series) -> pd.DataFrame:
    parts = col.astype(str).str.rsplit("-", n=1, expand=True)
    parts.columns = ["name", "version"]
    return parts

def _load_times(horn_csv=OUTPUT_HORN_CSV, naive_csv=OUTPUT_NAIVE_CSV) -> pd.DataFrame:
    df_h = pd.read_csv(horn_csv)
    hv = _split_crate_ver(df_h["crate-version"])
    df_h = pd.concat([hv, df_h.drop(columns=["crate-version"])], axis=1)
    df_h = df_h.rename(columns={"time_seconds": "time_horn", "return_code": "rc_horn"})
    df_n = pd.read_csv(naive_csv)
    nv = _split_crate_ver(df_n["crate-version"])
    df_n = pd.concat([nv, df_n.drop(columns=["crate-version"])], axis=1)
    df_n = df_n.rename(columns={"time_seconds": "time_naive", "return_code": "rc_naive"})
    df_times = pd.merge(
        df_h[["name", "version", "time_horn", "rc_horn"]],
        df_n[["name", "version", "time_naive", "rc_naive"]],
        on=["name", "version"], how="outer"
    )
    return df_times

def _file_exists(directory: str, name: str, version: str) -> bool:
    return os.path.exists(os.path.join(directory, f"{name}-{version}"))

def _counts_from_rc_present(df: pd.DataFrame, rc_col: str) -> dict:
    rc_raw = df[rc_col]
    rc_num = pd.to_numeric(rc_raw, errors="coerce")
    success = (rc_num == 0).sum()
    crash   = (rc_num == 1).sum()
    timeout = rc_raw.isna().sum()
    total   = int(len(df))
    return {"total": total, "success": int(success), "timeout": int(timeout), "crash": int(crash)}

def make_cdf_plot(df_times: pd.DataFrame, out_path: str = "rq4_cdf.pdf") -> None:
    HORN_LABEL  = "Horn Clause Optimized"
    NAIVE_LABEL = "Naive"
    HORN_DIR    = os.path.join("evaluation", "rq4")
    timeout_threshold = TIMEOUT_SECS

    # keep only crates that actually ran (horn file exists)
    mask_horn_exists = df_times.apply(lambda r: _file_exists(HORN_DIR, r["name"], r["version"]), axis=1)
    df_keep = df_times[mask_horn_exists].copy()

    # times → numeric; NaN means timeout in CSV semantics
    t_horn  = pd.to_numeric(df_keep.get("time_horn"),  errors="coerce")
    t_naive = pd.to_numeric(df_keep.get("time_naive"), errors="coerce")

    # CDF data (NaNs filled with timeout to push them to right edge)
    times_horn  = np.sort(t_horn.fillna(timeout_threshold).values)
    times_naive = np.sort(t_naive.fillna(timeout_threshold).values)
    cdf_horn    = np.arange(1, len(times_horn)  + 1) / len(times_horn)  if len(times_horn)  else np.array([])
    cdf_naive   = np.arange(1, len(times_naive) + 1) / len(times_naive) if len(times_naive) else np.array([])

    # counts (success=0, crash=1, timeout=blank), among ran-only
    def _counts_from_rc_present(df: pd.DataFrame, rc_col: str) -> dict:
        rc_raw = df[rc_col]
        rc_num = pd.to_numeric(rc_raw, errors="coerce")
        return {
            "success": int((rc_num == 0).sum()),
            "crash":   int((rc_num == 1).sum()),
            "timeout": int(rc_raw.isna().sum()),
        }

    horn_counts  = _counts_from_rc_present(df_keep, "rc_horn")
    naive_counts = _counts_from_rc_present(df_keep, "rc_naive")

    # ---- plotting (match your style/colors) ----
    sns.set_style("white")
    fig, ax = plt.subplots(figsize=(8, 6))

    sns.lineplot(x=times_naive, y=cdf_naive, drawstyle="steps-post", color="red",
                 label=NAIVE_LABEL, ax=ax)
    sns.lineplot(x=times_horn,  y=cdf_horn,  drawstyle="steps-post", color="green",
                 label=HORN_LABEL, ax=ax)

    ax.axvline(timeout_threshold, color="black", linestyle="--",
               label=f"Timeout ({timeout_threshold}s)")

    ax.set_xlabel("Time Taken (seconds)", fontsize=12)
    ax.set_ylabel("Cumulative Probability", fontsize=12)
    ax.set_title("CDF of Execution Time (with Timeouts)", fontsize=14, fontweight="bold")
    ax.legend(loc="lower right")

    table_data = [
        ["Algorithm",   "Successful", "Timeout", "Crashed"],
        ["Naive",       naive_counts["success"], naive_counts["timeout"], naive_counts["crash"]],
        ["Horn Clause", horn_counts["success"],  horn_counts["timeout"],  horn_counts["crash"]],
    ]

    the_table = ax.table(
        cellText=table_data,
        loc="upper right",
        cellLoc="center",
        bbox=[0.28, 0.61, 0.65, 0.2]
    )
    the_table.scale(0.6, 1)
    the_table.auto_set_font_size(False)
    the_table.set_fontsize(14)

    for (row, col), cell in the_table.get_celld().items():
        cell.set_edgecolor("black")
        cell.set_linewidth(0.6)
        if row == 0:
            cell.set_facecolor("#d9ead3")
            cell.set_text_props(weight="bold", color="black")
        else:
            cell.set_facecolor("white")

    plt.tight_layout()
    plt.savefig(out_path, bbox_inches="tight")
    print(f"[OK] Saved CDF to {out_path}")


def _file_has_more_than_one_line(directory: str, name: str, version: str) -> bool:
    file_path = os.path.join(directory, f"{name}-{version}")
    if os.path.exists(file_path):
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                for i, _ in enumerate(f, start=1):
                    if i > 1:
                        return True
                return False
        except Exception:
            return True
    return True

def make_scatter_plot(df_times: pd.DataFrame, df_dep: pd.DataFrame, out_path: str = "rq4_scatter.pdf") -> None:
    HORN_DIR  = os.path.join("evaluation", "rq4")
    NAIVE_DIR = os.path.join("evaluation", "naive", "rq4")

    mask_horn_exists = df_times.apply(lambda r: _file_exists(HORN_DIR, r["name"], r["version"]), axis=1)
    df_times = df_times[mask_horn_exists].copy()

    if "crate_name" in df_dep.columns and "name" not in df_dep.columns:
        df_dep = df_dep.rename(columns={"crate_name": "name"})
    df_m = pd.merge(df_times, df_dep[["name", "version", "dependency_count"]],
                    on=["name", "version"], how="left")

    df_m["time_naive_num"] = pd.to_numeric(df_m.get("time_naive"), errors="coerce")
    df_m["time_horn_num"]  = pd.to_numeric(df_m.get("time_horn"),  errors="coerce")

    df_m = df_m[df_m["dependency_count"] <= 400].copy()

    df_m["keep_basic"] = df_m.apply(lambda r: _file_has_more_than_one_line(NAIVE_DIR, r["name"], r["version"]), axis=1)
    df_m["keep_horn"]  = df_m.apply(lambda r: _file_has_more_than_one_line(HORN_DIR,  r["name"], r["version"]), axis=1)

    df_plot_basic = df_m.loc[
        df_m["keep_basic"] & df_m["time_naive_num"].notna(),
        ["name", "version", "dependency_count", "time_naive_num"]
    ].rename(columns={"time_naive_num": "time_basic_numeric"})

    df_plot_horn = df_m.loc[
        df_m["keep_horn"] & df_m["time_horn_num"].notna(),
        ["name", "version", "dependency_count", "time_horn_num"]
    ].rename(columns={"time_horn_num": "time_horn_numeric"})

    def f(x, A, B, C):
        return A * np.exp(B * x) + C

    xh = df_plot_horn["dependency_count"].to_numpy(float)
    yh = df_plot_horn["time_horn_numeric"].to_numpy(float)
    m_fit = np.isfinite(xh) & np.isfinite(yh) & (yh > 0)
    xh_fit, yh_fit = xh[m_fit], yh[m_fit]

    fit_ok = False
    A = B = C = np.nan
    R2 = np.nan
    AIC = np.nan
    x_seg = y_seg = None

    if yh_fit.size >= 3:
        order = np.argsort(xh_fit)
        xh_fit, yh_fit = xh_fit[order], yh_fit[order]
        spread = np.ptp(yh_fit) if yh_fit.size else 1.0
        ymin, ymax = float(yh_fit.min()), float(yh_fit.max())
        p0 = [max(1.0, ymax), 0.01, max(0.0, ymin - 0.1 * spread)]
        bounds = ([0.0, -np.inf, -np.inf], [np.inf, np.inf, np.inf])

        try:
            popt, pcov = curve_fit(f, xh_fit, yh_fit, p0=p0, bounds=bounds, maxfev=30000)
            A, B, C = popt
            x_line = np.linspace(xh_fit.min(), xh_fit.max(), 700)
            y_line = f(x_line, *popt)

            residuals = yh_fit - f(xh_fit, *popt)
            ss_res = float(np.sum(residuals**2))
            ss_tot = float(np.sum((yh_fit - yh_fit.mean())**2))
            R2 = 1 - ss_res / ss_tot if ss_tot > 0 else np.nan

            n = len(yh_fit)
            k = 3
            if n > k and ss_res > 0:
                AIC = n * float(np.log(ss_res / n)) + 2 * k

            fit_ok = True

            Y_CAP = 650.0
            under = y_line <= Y_CAP
            if not under.all():
                idx = np.argmax(~under)
                x_seg, y_seg = x_line[:idx], y_line[:idx]
            else:
                x_seg, y_seg = x_line, y_line
        except Exception:
            fit_ok = False

    sns.set_style("whitegrid")
    mpl.rcParams.update({
        "figure.dpi": 170, "savefig.dpi": 300,
        "font.size": 10, "axes.labelsize": 12, "axes.titlesize": 16,
        "legend.fontsize": 12,
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "axes.spines.top": False, "axes.spines.right": False,
    })

    fig, ax = plt.subplots(figsize=(12.0, 6.8))

    ax.scatter(
        df_plot_basic["dependency_count"], df_plot_basic["time_basic_numeric"],
        color="#d62728", alpha=0.75, marker="o",
        edgecolors="black", linewidths=0.9, s=46, label="Naive"
    )
    ax.scatter(
        df_plot_horn["dependency_count"], df_plot_horn["time_horn_numeric"],
        color="#1f77b4", alpha=0.85, marker="o",
        edgecolors="black", linewidths=0.9, s=46, label="Horn Clause Optimized"
    )

    if fit_ok:
        fit_label = f"Exponential fit: y = A e^{{Bx}} + C (R²={R2:.3f})"
        ax.plot(x_seg, y_seg, linestyle="--", linewidth=2.2, color="#1f77b4", label=fit_label)

    ax.axhline(TIMEOUT_SECS, linestyle="--", linewidth=1.2, color="#555555", alpha=0.9)
    ax.annotate("Timeout (600 s)",
                xy=(0.01, TIMEOUT_SECS), xycoords=("axes fraction", "data"),
                xytext=(6, 4), textcoords="offset points",
                fontsize=10, color="#555555",
                ha="left", va="bottom",
                bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="none", alpha=0.9))

    ax.set_xlabel("Number of Dependencies")
    ax.set_ylabel("Time Taken (seconds)")
    ax.set_title("Time Taken vs Number of Dependencies")

    Y_CAP = 650.0
    LOWER_PAD_FRAC = 0.06
    LOWER_FLOOR = -10.0
    y_all = np.concatenate([
        df_plot_basic["time_basic_numeric"].to_numpy(float),
        df_plot_horn["time_horn_numeric"].to_numpy(float)
    ])
    y_all = y_all[np.isfinite(y_all) & (y_all >= 0)]
    y_lo = np.percentile(y_all, 0.5) if y_all.size else 0.0
    margin = LOWER_PAD_FRAC * (Y_CAP - y_lo)
    y_min = max(LOWER_FLOOR, y_lo - margin)
    ax.set_ylim(y_min, Y_CAP)

    x_all = np.concatenate([
        df_plot_basic["dependency_count"].to_numpy(float),
        df_plot_horn["dependency_count"].to_numpy(float)
    ])
    x_all = x_all[np.isfinite(x_all)]
    x_min, x_max = (x_all.min(), x_all.max()) if x_all.size else (0, 1)
    x_pad = 0.02 * (x_max - x_min if x_max > x_min else 1)
    ax.set_xlim(x_min - x_pad, x_max + x_pad)

    ax.grid(True, which="both", linewidth=0.6, alpha=0.28)
    ax.legend(loc="lower right", frameon=True, fancybox=True, framealpha=0.95)

    plt.tight_layout()
    plt.savefig(out_path, bbox_inches="tight")
    print(f"[OK] Saved scatter (focused + exponential fit) to {out_path}")

if __name__ == "__main__":
    # run_top_crates_horn()
    # run_top_crates_naive()
    df_dep = get_dependency_counts(cache_dir=CACHE_DIR, input_crates_csv=CSV_FILE, output_dep_csv=DEP_COUNT_CSV)
    df_times = _load_times(OUTPUT_HORN_CSV, OUTPUT_NAIVE_CSV)
    make_cdf_plot(df_times, out_path="rq4_cdf.pdf")
    make_scatter_plot(df_times, df_dep, out_path="rq4_scatter.pdf")
