# This file contains the assumptions that are made about the safety of a crate.
import math
import z3
from sherlock import CrateVersion, User
import sherlock

MAX_WEIGHT = 500

def downloads_weight_function(downloads: int) -> int:
    """
    Assigns a weight to the assumption "the crate has a good enough number of downloads" 
    as a function of the number of downloads the crate actually has.
    """
    return round(1000*math.exp(-downloads/100000))

def repo_stats_weight_function(stars: int, forks: int) -> int:
    """
    Assigns a weight to the assumption "the crate repo has a good enough number of stars and forks" 
    as a function of the number of stars and forks the crate actually has.
    """
    return round(1000*math.exp(-stars/250) + 200*math.exp(-forks/20))

def user_stats_weight_function(stars: int, forks: int) -> int:
    """
    Assigns a weight to the assumption "the user has a good enough number of stars and forks on GitHub" 
    as a function of the number of stars and forks the user actually has.
    """
    return round(1000*math.exp(-stars/10000) + 300*math.exp(-forks/60))

class Assumption:
    def __init__(self, name: str, consequent: z3.BoolRef, weight: int):
        self.name = name
        self.variable = z3.Bool(name)
        self.consequent = consequent
        self.weight = weight
    def __repr__(self) -> str:
        return f"Assumption({self.name}, {self.consequent}, {self.weight})"
    def __eq__(self, other) -> bool:
        if isinstance(other, Assumption):
            return self.name == other.name and self.consequent == other.consequent and self.weight == other.weight
        return NotImplemented
    def __hash__(self) -> int:
        return hash((self.name, self.consequent, self.weight))
    def default_assignment(self) -> z3.BoolRef:
        """
        Returns the default assignment of the negative assumption. This is true for
        positive assumptions.
        """
        return z3.BoolVal(True)
    def single_assumption_weight(self) -> z3.ArithRef:
        """
        Returns the weight of a single assumption. Weight is incurred if the assumption is set to true.
        """
        return z3.If(self.variable, self.weight, 0)
    @staticmethod
    def assumptions_weight(assumptions: list['Assumption']) -> z3.ArithRef:
        """
        Returns the total weight of a set of assumptions.
        """
        return z3.Sum([a.single_assumption_weight() for a in assumptions])

class NegativeAssumption(Assumption):
    def __repr__(self) -> str:
        return f"Neg{super().__repr__()}"
    def default_assignment(self) -> z3.BoolRef:
        """
        Returns the default assignment of the negative assumption. This is false for
        negative assumptions.
        """
        return z3.BoolVal(False)
    def single_assumption_weight(self) -> z3.ArithRef:
        """
        Returns the weight of a single negative assumption. Weight is incurred if the assumption is 
        set to false.
        """
        return z3.If(self.variable, 0, self.weight)
    
def reputable_user(user: User, metadata: dict) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of variables and assumptions to prove a given user is safe.
    """
    # TODO (future work): Expand this function to include more assumptions about reputable users.
    # Unknown variables
    trusted = z3.Bool(f"{user}_safe")  # user is safe (i.e. trusted)

    return (
        [trusted], 
        [
            Assumption(f"ua0_{user}", trusted, 40),
        ]
    )

def assumptions_for(crate: CrateVersion, metadata: dict) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of variables and a list of assumptions to prove that a given crate is safe.
    """
    from solver import get_min_weight
    
    # Unknown variables
    safe = z3.Bool(f"{crate.name}-{crate.version}_safe")  # crate is safe
    good_downloads = z3.Bool(f"{crate.name}-{crate.version}_high_downloads")  # crate has a 'good enough' number of downloads
    good_repo_stats = z3.Bool(f"{crate.name}-{crate.version}_high_repo_stats")  # crate repo has a 'good enough' number of stars and forks
    unknown_vars = [safe, good_downloads, good_repo_stats]

    # Known variables
    passed_audit = z3.BoolVal(metadata["passed_audit"])  # crate passed audit
    no_side_effects = z3.BoolVal(metadata["num_side_effects"] == 0)  # crate has no side effects
    in_rust_sec = z3.BoolVal(metadata["in_rust_sec"])  # crate is in RustSec

    dependency_safety = [] # list constaining the Z3 variables representing the safety of dependencies
    user_safety = [] # list containing the Z3 variables representing the trustworthiness of users

    assumptions = [
        Assumption(f"a0_{crate}", safe, MAX_WEIGHT),
        Assumption(f"a1_{crate}", good_downloads, downloads_weight_function(metadata["downloads"])),
        Assumption(f"a2_{crate}", z3.Implies(good_downloads, safe), 10),
        Assumption(f"a3_{crate}", z3.Implies(passed_audit, safe), 30),
        Assumption(f"a4_{crate}", good_repo_stats, repo_stats_weight_function(metadata["stars"], metadata["forks"])),
        Assumption(f"a5_{crate}", z3.Implies(good_repo_stats, safe), 15),
        NegativeAssumption(f"na0_{crate}", z3.Implies(in_rust_sec, z3.Not(safe)), 50),
    ]
    d: CrateVersion
    for d in metadata["dependencies"]:
        # if the dependency is not already in the list of unknown variables (i.e. hasn't been processed yet)
        if z3.Bool(f"{d}_safe") not in unknown_vars:
            dep_metadata = sherlock.get_crate_metadata(d)
            dep_variables, dep_assumptions = assumptions_for(d, dep_metadata) # recursively add assumptions for dependencies
            dep_min_weight = get_min_weight(d, dep_variables, dep_assumptions) # get the minimum weight of assumptions for the dependency
            dependency_safety.append(z3.Bool(f"{d}_safe"))
            unknown_vars.append(z3.Bool(f"{d}_safe")) # dependency is safe
            assumptions.append(Assumption(f"dep_{d}", z3.Bool(f"{d}_safe"), dep_min_weight))
    u: User
    for u in metadata["developers"]:
        # if the user is not already in the list of unknown variables (i.e. hasn't been processed yet)
        if z3.Bool(f"{u}_safe") not in unknown_vars:
            user_metadata = sherlock.get_user_metadata(u)
            user_variables, user_assumptions = reputable_user(u, user_metadata)
            user_min_weight = get_min_weight(u, user_variables, user_assumptions)
            user_safety.append(z3.Bool(f"{u}_safe"))
            unknown_vars.append(z3.Bool(f"{u}_safe"))
            assumptions.append(Assumption(f"usr_{u}", z3.Bool(f"{u}_safe"), user_min_weight))
    assumptions.append(Assumption(f"a6_{crate}", z3.Implies(z3.And(no_side_effects, z3.And(dependency_safety)), safe), 1))
    assumptions.append(Assumption(f"a7_{crate}", z3.Implies(z3.And(user_safety), safe), 5))

    return (unknown_vars, assumptions)