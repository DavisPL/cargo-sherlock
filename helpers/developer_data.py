import os
import requests
import time

TRUSTED_RUST_DEVELOPERS = ('dtolnay', 'alexcrichton')

def get_developer_metadata(developer: str) -> dict:
    """
    Returns the metadata for a given developer (ex. the number of stars and forks on their GitHub repository,
    if they are in a list of trusted Rust developers, etc).
    
    For furture the documentation of Github API can be found here 
    https://docs.github.com/en/rest/repos/repos?apiVersion=2022-11-28#list-repositories-for-a-user

    """
    if developer == "Anonymous":
        # this is for our typosquatted example crates, where the developer is unknown - skip API call to GitHub, as it will 404
        return {"stars": 0, "forks": 0, "in_trusted_list": False}

    username = developer
    # Read token from token.txt
    token_file = "helpers/token.txt"
    if not os.path.exists(token_file):
        print(f"Error: Token file '{token_file}' not found. Please generate a GitHub token and save it to a file named 'token.txt'.")
        return {"stars": 0, "forks": 0, "in_trusted_list": False}
    token = ""
    try:
        with open(token_file, 'r') as file:
            token = file.read().strip()
    except Exception as e:
        print(f"Error reading token file: {e}")
        return {"stars": 0, "forks": 0, "in_trusted_list": False}

    headers = {
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
        "Authorization": f"Bearer {token}",
    }

    session = requests.Session()
    session.headers.update(headers)

    total_stars = 0
    total_forks = 0

    per_page = 100
    page = 1
    url = f"https://api.github.com/users/{username}/repos"

    while True:
        resp = session.get(
            url,
            params={"per_page": per_page, "page": page, "type": "owner"},
            timeout=20,
        )

        # Best-effort handling for rate limit exhaustion
        if resp.status_code == 403 and resp.headers.get("X-RateLimit-Remaining") == "0":
            reset = resp.headers.get("X-RateLimit-Reset")
            if reset and reset.isdigit():
                sleep_for = max(0, int(reset) - int(time.time()) + 1)
                time.sleep(min(sleep_for, 60))
                continue

        if resp.status_code == 404:
            return {"stars": 0, "forks": 0, "in_trusted_list": False}

        resp.raise_for_status()
        repos = resp.json()

        if not repos:
            break

        for repo in repos:
            if repo.get("fork"):
                continue
            total_stars += int(repo.get("stargazers_count", 0) or 0)
            total_forks += int(repo.get("forks_count", 0) or 0)

        page += 1

    return {"stars": total_stars, "forks": total_forks , "in_trusted_list": developer in TRUSTED_RUST_DEVELOPERS}