import math
MAX_COST = 100
def downloads_cost(downloads: int) -> int:
    """
    Assigns a cost to the assumption "the crate has a good enough number of downloads" 
    as a function of the number of downloads the crate actually has.
    """
    if downloads == 0:
        return MAX_COST
    return round(200 * (1 - (1/9) * math.log10(downloads)) ** 3)

def repo_stats_cost(stars: int, forks: int) -> int:
    """
    Assigns a cost to the assumption "the crate repo has a good enough number of stars and forks" 
    as a function of the number of stars and forks the crate actually has.
    """
    return round(200*math.exp(-stars/250) + 40*math.exp(-forks/20))

def user_stats_cost(stars: int, forks: int) -> int:
    """
    Assigns a cost to the assumption "the user has a good enough number of stars and forks on GitHub" 
    as a function of the number of stars and forks the user actually has.
    """
    return round(200*math.exp(-stars/10000) + 60*math.exp(-forks/60))