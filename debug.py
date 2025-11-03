import os
import pandas as pd

HORN_CSV = "random_horn_results.csv"
HORN_DIR = os.path.join("evaluation", "rq4")

def crashed_on_horn_names():
    df = pd.read_csv(HORN_CSV, dtype=str)
    # split "crate-version" -> name, version
    parts = df["crate-version"].astype(str).str.rsplit("-", n=1, expand=True)
    parts.columns = ["name", "version"]
    df = pd.concat([parts, df.drop(columns=["crate-version"])], axis=1)

    # normalize return_code to numeric
    rc = pd.to_numeric(df["return_code"], errors="coerce")

    # keep only rows that have a horn file present (i.e., actually ran)
    def horn_file_exists(row):
        return os.path.exists(os.path.join(HORN_DIR, f"{row['name']}-{row['version']}"))

    ran_mask = df.apply(horn_file_exists, axis=1)

    # crash = rc == 1, among ran-only
    crashed = df[ran_mask & (rc == 1)].copy()

    # return as a list of "name-version" strings (or DataFrame if you prefer)
    return crashed.assign(crate_version=crashed["name"] + "-" + crashed["version"])["crate_version"].tolist()

# Example usage:
crashed_list = crashed_on_horn_names()
print(f"{len(crashed_list)} crashed on Horn:")
for cv in crashed_list:
    print(cv)
