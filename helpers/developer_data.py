TRUSTED_RUST_DEVELOPERS = ('dtolnay', 'alexcrichton')

def get_developer_metadata(developer: str) -> dict:
    """
    Returns the metadata for a given developer (ex. the number of stars and forks on their GitHub repository,
    if they are in a list of trusted Rust developers, etc).
    """
    # TODO: Implement this function
    return {
        "in_trusted_list": developer in TRUSTED_RUST_DEVELOPERS,
    }