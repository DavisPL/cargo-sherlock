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
import argparse
import textwrap
import logging 

CSV_FILE = "random1000_crates.csv"
OUTPUT_HORN_CSV = "random_horn_results.csv"
OUTPUT_NAIVE_CSV = "random_naive_results.csv"
DEP_COUNT_CSV = "random1000_dep_count.csv"
CACHE_DIR = "logs/cache"
TIMEOUT_SECS = 600
MAX_WORKERS = 10

# logging
RUN_LOG_FILE = "rq4_run.log"
logging.basicConfig(
    filename=RUN_LOG_FILE,
    filemode="a",
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    encoding="utf-8"
)
LOGGER = logging.getLogger("rq4")

def _process_one(crate_name: str, version: str, base_out_dir: str, naive: bool = False) -> tuple[str, float, int | None]:
    crate_ver = f"{crate_name}-{version}"
    output_file = os.path.join(base_out_dir, crate_ver)
    cmd = ["python3", "sherlock.py", "trust", crate_name, version, "-o", output_file]
    if naive:
        cmd.insert(4, "--no-horn")
    LOGGER.info("[START] %s", " ".join(cmd))
    start = time.perf_counter()
    try:
        proc = subprocess.run(cmd, timeout=TIMEOUT_SECS, text=True, capture_output=True)
        rc = proc.returncode
        if proc.stdout:
            LOGGER.info(proc.stdout.rstrip("\n"))
        if proc.stderr:
            LOGGER.error(proc.stderr.rstrip("\n"))
    except subprocess.TimeoutExpired as e:
        elapsed = time.perf_counter() - start
        out = getattr(e, "output", None)
        err = getattr(e, "stderr", None)
        if out:
            LOGGER.info(str(out).rstrip("\n"))
        if err:
            LOGGER.error(str(err).rstrip("\n"))
        LOGGER.warning("[TIMEOUT] %s after %.2fs", crate_ver, elapsed)
        return crate_ver, elapsed, None
    elapsed = time.perf_counter() - start
    LOGGER.info("[DONE] %s in %.2fs (rc=%s)", crate_ver, elapsed, rc)
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
                    LOGGER.error("[ERROR] %s: %s", crate_ver, e)
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
                    LOGGER.error("[ERROR] %s: %s", crate_ver, e)
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
                LOGGER.warning("JSON decode error in file %s: %s", filename, e)
                failed_files.append(filename)
                continue
            deps = data.get("dependencies", [])
            rows.append({"crate_name": crate_name, "version": crate_version, "dependency_count": len(deps)})
    else:
        LOGGER.warning("[WARN] Cache dir not found: %s", cache_dir)

    df_deps = pd.DataFrame(rows)

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
    LOGGER.info("[OK] Wrote dependency counts to %s", output_dep_csv)
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
    HORN_LABEL  = "Algorithm 2"
    NAIVE_LABEL = "Algorithm 1"
    HORN_DIR    = os.path.join("evaluation", "rq4")
    timeout_threshold = TIMEOUT_SECS

    # keep only crates that actually ran (horn file exists)
    mask_horn_exists = df_times.apply(lambda r: _file_exists(HORN_DIR, r["name"], r["version"]), axis=1)
    df_keep = df_times[mask_horn_exists].copy()

    t_horn  = pd.to_numeric(df_keep.get("time_horn"),  errors="coerce")
    t_naive = pd.to_numeric(df_keep.get("time_naive"), errors="coerce")

    # CDF data (NaNs filled with timeout to push them to right edge)
    times_horn  = np.sort(t_horn.fillna(timeout_threshold).values)
    times_naive = np.sort(t_naive.fillna(timeout_threshold).values)
    cdf_horn    = np.arange(1, len(times_horn)  + 1) / len(times_horn)  if len(times_horn)  else np.array([])
    cdf_naive   = np.arange(1, len(times_naive) + 1) / len(times_naive) if len(times_naive) else np.array([])

    # counts (success=0, crash=1, timeout=blank), among those that ran
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

    # plot timee
    sns.set_style("white")
    fig, ax = plt.subplots(figsize=(8, 6))

    sns.lineplot(x=times_naive, y=cdf_naive, drawstyle="steps-post", color="red",
                 label=NAIVE_LABEL, ax=ax)
    sns.lineplot(x=times_horn,  y=cdf_horn,  drawstyle="steps-post", color="green",
                 label=HORN_LABEL, ax=ax)

    ax.axvline(timeout_threshold, color="black", linestyle="--",
               label=f"Timeout ({timeout_threshold}s)")

    ax.set_xlabel("Time Taken (seconds)", fontsize=14)
    ax.set_ylabel("Cumulative Probability", fontsize=14)
    # ax.set_title("CDF of Execution Time (with Timeouts)", fontsize=14, fontweight="bold")
    ax.legend(loc="lower right")

    table_data = [
        ["",   "Successful", "Timeout", "Crashed"],
        ["Algorithm 1",       naive_counts["success"], naive_counts["timeout"], naive_counts["crash"]],
        ["Algorithm 2", horn_counts["success"],  horn_counts["timeout"],  horn_counts["crash"]],
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
    LOGGER.info("[OK] Saved CDF to %s", out_path)

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

from matplotlib.lines import Line2D  # at top of file

def make_scatter_plot(df_times: pd.DataFrame, df_dep: pd.DataFrame, out_path: str = "rq4_scatter.pdf") -> None:
    HORN_DIR  = os.path.join("evaluation", "rq4")
    NAIVE_DIR = os.path.join("evaluation", "naive", "rq4")

    # Upper cap for y-axis
    Y_CAP = 650.0

    # ---- merge dependency counts ----
    if "crate_name" in df_dep.columns and "name" not in df_dep.columns:
        df_dep = df_dep.rename(columns={"crate_name": "name"})
    df_m = pd.merge(
        df_times,
        df_dep[["name", "version", "dependency_count"]],
        on=["name", "version"],
        how="left",
    )

    # numeric times
    df_m["time_naive_num"] = pd.to_numeric(df_m.get("time_naive"), errors="coerce")
    df_m["time_horn_num"]  = pd.to_numeric(df_m.get("time_horn"),  errors="coerce")

    # numeric return codes (0 = success, 1 = crash, NaN = timeout/unknown)
    df_m["rc_naive_num"] = pd.to_numeric(df_m.get("rc_naive"), errors="coerce")
    df_m["rc_horn_num"]  = pd.to_numeric(df_m.get("rc_horn"),  errors="coerce")

    # limit to "reasonable" dependency counts
    df_m = df_m[df_m["dependency_count"] <= 400].copy()

    # filters for "usable" outputs (for normal points only)
    df_m["keep_basic"] = df_m.apply(
        lambda r: _file_has_more_than_one_line(NAIVE_DIR, r["name"], r["version"]),
        axis=1,
    )
    df_m["keep_horn"] = df_m.apply(
        lambda r: _file_has_more_than_one_line(HORN_DIR, r["name"], r["version"]),
        axis=1,
    )

    # ---------- split into success / crash / timeout ----------

    # Naive successes (circles)
    df_plot_basic_ok = df_m.loc[
        df_m["keep_basic"]
        & df_m["time_naive_num"].notna()
        & (df_m["rc_naive_num"] == 0),
        ["name", "version", "dependency_count", "time_naive_num"],
    ].rename(columns={"time_naive_num": "time_basic_numeric"})

    # Naive crashes (crosses)
    df_plot_basic_crash = df_m.loc[
        (df_m["rc_naive_num"] == 1) & df_m["dependency_count"].notna(),
        ["name", "version", "dependency_count"],
    ]

    # Naive timeouts (squares)
    df_plot_basic_timeout = df_m.loc[
        df_m["rc_naive_num"].isna() & df_m["dependency_count"].notna(),
        ["name", "version", "dependency_count"],
    ]

    # Horn successes (circles)
    df_plot_horn_ok = df_m.loc[
        df_m["keep_horn"]
        & df_m["time_horn_num"].notna()
        & (df_m["rc_horn_num"] == 0),
        ["name", "version", "dependency_count", "time_horn_num"],
    ].rename(columns={"time_horn_num": "time_horn_numeric"})

    # Horn crashes (crosses)
    df_plot_horn_crash = df_m.loc[
        (df_m["rc_horn_num"] == 1) & df_m["dependency_count"].notna(),
        ["name", "version", "dependency_count"],
    ]

    # Horn timeouts (squares)
    df_plot_horn_timeout = df_m.loc[
        df_m["rc_horn_num"].isna() & df_m["dependency_count"].notna(),
        ["name", "version", "dependency_count"],
    ]

    # ---------- exponential fit (Horn successes only) ----------

    def f(x, A, B, C):
        return A * np.exp(B * x) + C

    xh = df_plot_horn_ok["dependency_count"].to_numpy(float)
    yh = df_plot_horn_ok["time_horn_numeric"].to_numpy(float)
    m_fit = np.isfinite(xh) & np.isfinite(yh) & (yh > 0)
    xh_fit, yh_fit = xh[m_fit], yh[m_fit]

    fit_ok = False
    R2 = np.nan
    x_seg = y_seg = None
    fit_label = None

    if yh_fit.size >= 3:
        order = np.argsort(xh_fit)
        xh_fit, yh_fit = xh_fit[order], yh_fit[order]
        spread = np.ptp(yh_fit) if yh_fit.size else 1.0
        ymin, ymax = float(yh_fit.min()), float(yh_fit.max())
        p0 = [max(1.0, ymax), 0.01, max(0.0, ymin - 0.1 * spread)]
        bounds = ([0.0, -np.inf, -np.inf], [np.inf, np.inf, np.inf])

        try:
            popt, _ = curve_fit(f, xh_fit, yh_fit, p0=p0, bounds=bounds, maxfev=30000)
            x_line = np.linspace(xh_fit.min(), xh_fit.max(), 700)
            y_line = f(x_line, *popt)

            residuals = yh_fit - f(xh_fit, *popt)
            ss_res = float(np.sum(residuals**2))
            ss_tot = float(np.sum((yh_fit - yh_fit.mean())**2))
            R2 = 1 - ss_res / ss_tot if ss_tot > 0 else np.nan

            under = y_line <= Y_CAP
            if not under.all():
                idx = np.argmax(~under)
                x_seg, y_seg = x_line[:idx], y_line[:idx]
            else:
                x_seg, y_seg = x_line, y_line

            fit_ok = True
            fit_label = f"Exponential fit"
        except Exception:
            fit_ok = False

    sns.set_style("whitegrid")
    mpl.rcParams.update({
        "figure.dpi": 170, "savefig.dpi": 300,
        "font.size": 16, "axes.labelsize": 16, "axes.titlesize": 118,
        "legend.fontsize": 16,
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "axes.spines.top": False, "axes.spines.right": False,
    })

    fig, ax = plt.subplots(figsize=(12.0, 6.8))

    # successes: circles
    ax.scatter(
        df_plot_basic_ok["dependency_count"], df_plot_basic_ok["time_basic_numeric"],
        color="#d62728", alpha=0.75, marker="o",
        edgecolors="black", linewidths=0.9, s=46, label="_nolegend_",
    )
    ax.scatter(
        df_plot_horn_ok["dependency_count"], df_plot_horn_ok["time_horn_numeric"],
        color="#1f77b4", alpha=0.85, marker="o",
        edgecolors="black", linewidths=0.9, s=46, label="_nolegend_",
    )

    # fit line
    if fit_ok:
        ax.plot(x_seg, y_seg, linestyle="--", linewidth=2.2, color="#1f77b4")

    # timeout line (uses module-level TIMEOUT_SECS)
    ax.axhline(
        TIMEOUT_SECS,
        linestyle="--",
        linewidth=1.0,
        color="#555555",
        alpha=0.7,
        zorder=1,
    )
    # caption BELOW the line
    ax.annotate(
        f"Timeout ({TIMEOUT_SECS} s)",
        xy=(0.01, TIMEOUT_SECS), xycoords=("axes fraction", "data"),
        xytext=(6, -6), textcoords="offset points",
        fontsize=14, color="#555555",
        ha="left", va="top",
        bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="none", alpha=0.9),
    )

    # y limits from successes
    LOWER_PAD_FRAC = 0.06
    LOWER_FLOOR = -10.0
    y_all = np.concatenate([
        df_plot_basic_ok["time_basic_numeric"].to_numpy(float),
        df_plot_horn_ok["time_horn_numeric"].to_numpy(float),
    ]) if (len(df_plot_basic_ok) or len(df_plot_horn_ok)) else np.array([0.0])
    y_all = y_all[np.isfinite(y_all) & (y_all >= 0)]
    y_lo = np.percentile(y_all, 0.5) if y_all.size else 0.0
    margin = LOWER_PAD_FRAC * (Y_CAP - y_lo)
    y_min = max(LOWER_FLOOR, y_lo - margin)
    ax.set_ylim(y_min, Y_CAP)

    # x limits from successes
    x_all = np.concatenate([
        df_plot_basic_ok["dependency_count"].to_numpy(float),
        df_plot_horn_ok["dependency_count"].to_numpy(float),
    ]) if (len(df_plot_basic_ok) or len(df_plot_horn_ok)) else np.array([0.0, 1.0])
    x_all = x_all[np.isfinite(x_all)]
    x_min, x_max = (x_all.min(), x_all.max()) if x_all.size else (0.0, 1.0)
    x_pad = 0.02 * (x_max - x_min if x_max > x_min else 1.0)
    ax.set_xlim(x_min - x_pad, x_max + x_pad)

    # timeouts and crashes  
    # Put timeouts a bit above the line, crashes even higher
    TIMEOUT_Y = min(TIMEOUT_SECS + 18.0, Y_CAP - 10.0)
    CRASH_Y   = min(TIMEOUT_SECS + 36.0, Y_CAP - 5.0)

    # crashes: crosses above line
    if not df_plot_basic_crash.empty:
        ax.scatter(
            df_plot_basic_crash["dependency_count"],
            np.full(len(df_plot_basic_crash), CRASH_Y),
            color="#d62728",
            marker="x",
            linewidths=1.8,
            s=70,
            zorder=6,
            label="_nolegend_",
        )
    if not df_plot_horn_crash.empty:
        ax.scatter(
            df_plot_horn_crash["dependency_count"],
            np.full(len(df_plot_horn_crash), CRASH_Y),
            color="#1f77b4",
            marker="x",
            linewidths=1.8,
            s=70,
            zorder=6,
            label="_nolegend_",
        )

    # timeouts: hollow squares above line (but below crashes)
    if not df_plot_basic_timeout.empty:
        ax.scatter(
            df_plot_basic_timeout["dependency_count"],
            np.full(len(df_plot_basic_timeout), TIMEOUT_Y),
            facecolors="none",
            edgecolors="#d62728",
            marker="s",
            linewidths=1.8,
            s=80,
            zorder=6,
            label="_nolegend_",
        )
    if not df_plot_horn_timeout.empty:
        ax.scatter(
            df_plot_horn_timeout["dependency_count"],
            np.full(len(df_plot_horn_timeout), TIMEOUT_Y),
            facecolors="none",
            edgecolors="#1f77b4",
            marker="s",
            linewidths=1.8,
            s=80,
            zorder=6,
            label="_nolegend_",
        )

    ax.grid(True, which="both", linewidth=0.6, alpha=0.28)

    # 2×3 table (Naive/Horn × success/timeout/crash)
    table_handles = [
        # col 1: success
        Line2D([0], [0], marker="o", linestyle="none",
               markerfacecolor="#d62728", markeredgecolor="black",
               label="Algorithm 1: success"),
        Line2D([0], [0], marker="o", linestyle="none",
               markerfacecolor="#1f77b4", markeredgecolor="black",
               label="Algorithm 2: success"),

        # col 2: timeout
        Line2D([0], [0], marker="s", linestyle="none",
               markerfacecolor="none", markeredgecolor="#d62728",
               label="Algorithm 1: timeout"),
        Line2D([0], [0], marker="s", linestyle="none",
               markerfacecolor="none", markeredgecolor="#1f77b4",
               label="Algorithm 2: timeout"),
        
        # col 3: crash
        Line2D([0], [0], marker="x", linestyle="none",
               color="#d62728", markeredgewidth=1.8,
               label="Algorithm 1: crash"),
        Line2D([0], [0], marker="x", linestyle="none",
               color="#1f77b4", markeredgewidth=1.8,
               label="Algorithm 2: crash"),
    ]

    legend_table = ax.legend(
        handles=table_handles,
        ncol=3,
        loc="lower right",
        bbox_to_anchor=(1.0, 0.06),   # slightly above bottom
        frameon=True,
        fancybox=True,
        framealpha=0.95,
        columnspacing=1.5,
        handletextpad=0.8,
        borderpad=0.8,
        labelspacing=0.4,
        fontsize=14,
    )

    # fit label, drawn just below the table, without its own frame,
    # so it visually appears inside the same box
    if fit_ok and fit_label is not None:
        fit_handle = Line2D(
            [0], [0],
            linestyle="--",
            color="#1f77b4",
            linewidth=2.0,
            label=fit_label,
        )
        legend_fit = ax.legend(
            handles=[fit_handle],
            loc="lower right",
            bbox_to_anchor=(1.0, 0.013),  # a little below the table, same x
            frameon=False,
            handlelength=3.0,
            fontsize=14,
        )
        ax.add_artist(legend_table)

    ax.set_xlabel("Number of Dependencies")
    ax.set_ylabel("Time Taken (seconds)")

    plt.tight_layout()
    plt.savefig(out_path, bbox_inches="tight")
    LOGGER.info("[OK] Saved scatter (with crashes + timeouts + table+fit legend) to %s", out_path)


def main():

    parser = argparse.ArgumentParser(
        prog="eval_rq4.py",
        description="Evaluate RQ4: Naive vs Horn Clause Optimized Solver Performance",
        formatter_class=argparse.RawTextHelpFormatter,
        epilog=textwrap.dedent("""\
            Examples:
              # Full experiment: run Cargo-Sherlock on random 1000 crates in both Naive and Horn modes - make a CDF of time taken and a scatter plot of time vs dependency count
              python3 eval_rq4.py -m full

              # Partial: reuse existing time measurements, and generate the CDF and scatter plot only
              python3 eval_rq4.py -m cached
        """),
    )

    parser.add_argument(
        "-m", "--mode",
        choices=["full", "cached"],
        default="cached",
        metavar="MODE",
        help=textwrap.dedent("""\
            Choose how much work to do:

              full
                • Run Cargo-Sherlock on Random 1000 crates with Naive Algorithm
                • Run Cargo-Sherlock on Random 1000 crates with Horn Clause Optimized Algorithm
                • Get Dependency counts for all crates
                • Make a CDF plot of time taken
                • Make a scatter plot of time vs dependency count

              cached  (default)
                • Skip all runs
                • Get Dependency counts for all crates
                • Make a CDF plot of time taken
                • Make a scatter plot of time vs dependency count
        """),
    )

    parsed_args = parser.parse_args()
    mode = parsed_args.mode

    if mode == "full":
        print("Running in full mode:")

        print("1) Running Horn Clause Optimized Algorithm on top crates...")
        run_top_crates_horn()
        print("2) Running Naive Algorithm on top crates...")
        run_top_crates_naive()
        print("3) Getting dependency counts...")
        df_dep = get_dependency_counts(cache_dir=CACHE_DIR, input_crates_csv=CSV_FILE, output_dep_csv=DEP_COUNT_CSV)
        print("4) Analyzing the time taken by both algorithms...")
        df_times = _load_times(OUTPUT_HORN_CSV, OUTPUT_NAIVE_CSV)
        print("5) Making a CDF plot comparing both algorithms for time taken (stored rq4_cdf.pdf)...")
        make_cdf_plot(df_times, out_path="rq4_cdf.pdf")
        print("6) Making a scatter plot of time vs dependency count (stored rq4_scatter.pdf)...")
        make_scatter_plot(df_times, df_dep, out_path="rq4_scatter.pdf")

    elif mode == "cached":
        print("Running in cached mode:")

        print("1) Getting dependency counts...")
        df_dep = get_dependency_counts(cache_dir=CACHE_DIR, input_crates_csv=CSV_FILE, output_dep_csv=DEP_COUNT_CSV)
        print("2) Analyzing the time taken by both algorithms...")
        df_times = _load_times(OUTPUT_HORN_CSV, OUTPUT_NAIVE_CSV)
        print("3) Making a CDF plot comparing both algorithms for time taken (stored rq4_cdf.pdf)...")
        make_cdf_plot(df_times, out_path="rq4_cdf.pdf")
        print("4) Making a scatter plot of time vs dependency count (stored rq4_scatter.pdf)...")
        make_scatter_plot(df_times, df_dep, out_path="rq4_scatter.pdf")

if __name__ == "__main__":
    main()
