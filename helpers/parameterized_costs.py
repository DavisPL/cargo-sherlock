import math
from helpers.assumption import MAX_COST

def downloads_cost(downloads: int) -> int:
    """
    Assigns a cost to the assumption "the crate has a good enough number of downloads" 
    as a function of the number of downloads the crate actually has.
    """
    if downloads == 0:
        return MAX_COST
    return max(round(200 * (1 - (1/9) * math.log10(downloads)) ** 3), 1)

def repo_stats_cost(stars: int, forks: int) -> int:
    """
    Assigns a cost to the assumption "the crate repo has a good enough number of stars and forks" 
    as a function of the number of stars and forks the crate actually has.
    """
    return max(round(200*math.exp(-stars/250) + 40*math.exp(-forks/20)), 1)

def side_effects_cost(num_side_effects: int) -> int:
    """
    Assigns a cost to the assumption "the crate has a many side effects" 
    as a function of the number of side effects the crate actually has.
    """
    if num_side_effects == 0:
        return MAX_COST
    return max(round(-10 * math.log10(2*num_side_effects + 0.2) + 33), 1)