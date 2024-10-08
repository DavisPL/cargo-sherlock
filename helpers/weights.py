import math

def downloads_weight(downloads: int) -> int:
    """
    Assigns a weight to the assumption "the crate has a good enough number of downloads" 
    as a function of the number of downloads the crate actually has.
    """
    return round(1000*math.exp(-downloads/100000))

def repo_stats_weight(stars: int, forks: int) -> int:
    """
    Assigns a weight to the assumption "the crate repo has a good enough number of stars and forks" 
    as a function of the number of stars and forks the crate actually has.
    """
    return round(1000*math.exp(-stars/250) + 200*math.exp(-forks/20))

def user_stats_weight(stars: int, forks: int) -> int:
    """
    Assigns a weight to the assumption "the user has a good enough number of stars and forks on GitHub" 
    as a function of the number of stars and forks the user actually has.
    """
    return round(1000*math.exp(-stars/10000) + 300*math.exp(-forks/60))