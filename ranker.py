import os
import re
import pandas as pd

directory = "evaluation"

data = []

assumptions_pattern = re.compile(r"'assumptions':\s*\[(.*?)\]", re.DOTALL)
trust_score_pattern = re.compile(r"'trust_score':\s*(\d+)")

for filename in os.listdir(directory):
    if filename.endswith(".json"):
        name, version = filename.rsplit("_", 1)
        version = version.replace(".json", "")
        file_path = os.path.join(directory, filename)
        with open(file_path, 'r') as file:
            content = file.read()
        
        assumptions_match = assumptions_pattern.search(content)
        if assumptions_match:
            assumptions = assumptions_match.group(1)
        else:
            assumptions = None
        
        trust_score_match = trust_score_pattern.search(content)
        if trust_score_match:
            trust_score = int(trust_score_match.group(1))
        else:
            trust_score = 0  # Default value if trust_score not found
        
        data.append({"name": name, "version": version, "score": trust_score})


df = pd.DataFrame(data)
df_sorted = df.sort_values(by="score", ascending=False)
output_file = "trust_score_ranking.csv"
df_sorted.to_csv(output_file, index=False)

print(f"Ranking saved to {output_file}")
