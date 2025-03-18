import math
from enum import Enum
MAX_COST = 100

class CrateLabel(Enum):
    """
    Enum representing the labels that can be assigned to a crate.
    """
    SAFE = 0
    LOW_SEVERITY = 1
    MEDIUM_SEVERITY = 2
    HIGH_SEVERITY = 3
    CRITICAL = 4

def downloads_cost(downloads: int) -> int:
    """
    Assigns a cost to the assumption "the crate has a good enough number of downloads" 
    as a function of the number of downloads the crate actually has.
    """
    if downloads == 0:
        return MAX_COST
    return max(round(200 * (1 - (1/9) * math.log10(downloads)) ** 3), 0)

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

def side_effects_cost(num_side_effects: int) -> int:
    """
    Assigns a cost to the assumption "the crate has a many side effects" 
    as a function of the number of side effects the crate actually has.
    """
    if num_side_effects == 0:
        return MAX_COST
    return max(round(-10 * math.log10(2*num_side_effects + 0.2) + 33), 0)

def combine_costs(positive_cost: int, negative_cost: int) -> CrateLabel:
    """
    Combines the positive and negative costs into a single cost.
    """
    issue_score = MAX_COST - negative_cost
    for i in range(1, 5):
        if positive_cost <= -i/10 * issue_score + 20*i:
            return CrateLabel(i-1)
    return CrateLabel.CRITICAL