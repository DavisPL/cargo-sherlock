import z3
import math
import csv
import os
import sys


def parser():
    csv.field_size_limit(sys.maxsize)
    directory_path = '/logs/Random500/'
    full_path = os.path.join(os.getcwd() + directory_path)
    # files = glob.glob(os.path.join(full_path, '*.csv'))
    files = ["anyhow-1.0.82.csv"]
    # print(files)
    result = []
    for file in files:
        temp = []
        with open(file, 'r') as f:
            contents = f.read()
            sections = contents.split('************************************')
            for section in sections:
                # Remove any leading/trailing whitespace
                section = section.strip()
                if not section:
                    continue
                # print(section)
                lines = section.splitlines()
                reader = csv.DictReader(lines)
                temp.append(reader)
        result.append(temp)
    return result

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
    return round(1000*math.exp(-stars/10000) + 1000*math.exp(-forks/10000))

def user_stats_weight_function(stars: int, forks: int) -> int:
    """
    Assigns a weight to the assumption "the user has a good enough number of stars and forks on GitHub" 
    as a function of the number of stars and forks the user actually has.
    """
    return round(1000*math.exp(-stars/10000) + 1000*math.exp(-forks/10000))

class Assumption:
    def __init__(self, name: str, consequent: z3.BoolRef, weight: int):
        self.name = name
        self.variable = z3.Bool(name)
        self.consequent = consequent
        self.weight = weight
    def single_assumption_weight(self) -> z3.ArithRef:
        """
        Returns the weight of a single assumption. Weight is incurred if the assumption
        is set to true.
        """
        return z3.If(self.variable, self.weight, 0)
    @staticmethod
    def assumptions_weight(assumptions: list['Assumption']) -> z3.ArithRef:
        """
        Returns the total weight of a set of assumptions.
        """
        return z3.Sum([a.single_assumption_weight() for a in assumptions])

class NegativeAssumption(Assumption):
    def single_assumption_weight(self) -> z3.ArithRef:
        """
        Returns the weight of a single negative assumption. Weight is incurred if the 
        assumption is set to false.
        """
        return z3.If(self.variable, 0, self.weight)

def assumptions_for(crate: str, metadata: dict) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of variables and a list of assumptions to prove that a given crate is safe.
    The first element in the returned list of assumptions is what is being proved (i.e. the crate is safe).
    """
    # Unknown variables
    safe = z3.Bool(f"{crate}_safe")  # crate is safe
    good_downloads = z3.Bool(f"{crate}_high_downloads")  # crate has a 'good enough' number of downloads
    good_repo_stats = z3.Bool(f"{crate}_high_repo_stats")  # crate repo has a 'good enough' number of stars and forks
    dependency_safety = []
    user_safety = []
    for d in metadata["dependencies"]:
        dependency_safety.append(z3.Bool(f"{d}_safe")) # dependency is safe
    for u in metadata["developers"]:
        user_safety.append(z3.Bool(f"{u}_trusted")) # user is trusted
    
    # Known variables
    passed_audit = z3.BoolVal(metadata["passed_audit"])  # crate passed audit
    no_side_effects = z3.BoolVal(metadata["num_side_effects"] == 0)  # crate has no side effects
    in_rust_sec = z3.BoolVal(metadata["in_rust_sec"])  # crate is in RustSec
    failed_rudra = z3.BoolVal(metadata["failed_rudra"])  # crate failed Rudra

    return (
        [safe, good_downloads, good_repo_stats], 
        [
            Assumption(f"a0_{crate}", safe, 1500),
            Assumption(f"a1_{crate}", good_downloads, downloads_weight_function(metadata["downloads"])),
            Assumption(f"a2_{crate}", z3.Implies(good_downloads, safe), 90),
            Assumption(f"a3_{crate}", z3.Implies(passed_audit, safe), 100),
            Assumption(f"a4_{crate}", z3.Implies(z3.And(no_side_effects, z3.And(dependency_safety)), safe), 8),
            Assumption(f"a5_{crate}", good_repo_stats, repo_stats_weight_function(metadata["stars"], metadata["forks"])),
            Assumption(f"a6_{crate}", z3.Implies(good_repo_stats, safe), 11),
            Assumption(f"a7_{crate}", z3.Implies(z3.And(user_safety), safe), 5),
            NegativeAssumption(f"na0_{crate}", z3.Implies(in_rust_sec, z3.Not(safe)), 1000),
            NegativeAssumption(f"na1_{crate}", z3.Implies(failed_rudra, z3.Not(safe)), 500)
        ]
    )

def reputable_user(user: str, metadata: dict) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of assumptions for a reputable user.
    """
    # TODO: Expand this function to include more assumptions about reputable users.
    # Unknown variables
    trusted = z3.Bool(f"{user}_trusted")  # user is trusted
    good_profile_stats = z3.Bool(f"{user}_high_profile_stats")  # user has a 'good enough' total number of stars and forks on GitHub

    return (
        [trusted, good_profile_stats], 
        [
            Assumption(f"ua0_{user}", trusted, 100),
            Assumption(f"ua1_{user}", good_profile_stats, user_stats_weight_function(metadata["stars"], metadata["forks"])),
            Assumption(f"ua2_{user}", z3.Implies(good_profile_stats, trusted), 10),
        ]
    )

def get_substituted_clauses(variables: list[z3.BoolRef], expression: z3.BoolRef) -> list[z3.BoolRef]:
    """
    Returns a list of clauses, composed of the substitution of all occurrences of the given variables 
    in the given expression with True and False. Each clause is a possible assignment of the boolean 
    variables.
    """
    clauses = []
    def sub(i=0, clause=expression):
        if i == len(variables):
            clauses.append(clause)
        else:
            sub(i+1, z3.substitute(clause, (variables[i], z3.BoolVal(False))))
            sub(i+1, z3.substitute(clause, (variables[i], z3.BoolVal(True))))
    sub()
    return clauses

def exists_bool_expr(variables: list[z3.BoolRef], expression: z3.BoolRef) -> z3.BoolRef:
    """
    Returns the existential quantification of the given expression with respect to the given boolean
    variables. This is equivalent to the disjunction of all possible substitutions of the variables.
    """
    clauses = get_substituted_clauses(variables, expression)
    return z3.Or(clauses)

def solve_assumptions(variables: list[z3.BoolRef], assumptions: list[Assumption]):
    """
    Finds the minimum weight of a set of assumptions that prove the crate is safe. This function
    requires that the first element in variables is the variable representing the crate being safe
    (i.e. the variable being proven).
    """
    solver = z3.Solver()
    min_weight = z3.Int('min_weight')
    assumption_implications = z3.And([z3.Implies(a.variable, a.consequent) for a in assumptions])
    implications_with_neg_conclusion = z3.And(assumption_implications, z3.Not(variables[0]))
    # Define the UNSAT predicate. This checks if implications_with_neg_conclusion is unsatisfiable. 
    # If it is, then the conclusion (i.e. the crate is safe) must be derivable from the assumptions.
    UNSAT = z3.Not(z3.Exists(variables, implications_with_neg_conclusion))
    # Define the CON predicate. This checks if the assumption_implications are consistent (i.e. satisfiable).
    CON = z3.Exists(variables, assumption_implications)
    solver.add(UNSAT)
    solver.add(CON)
    solver.add(min_weight == Assumption.assumptions_weight(assumptions))
    minimization_constraint = z3.ForAll(
        [a.variable for a in assumptions], 
        z3.Implies(z3.And(UNSAT, CON), min_weight <= Assumption.assumptions_weight(assumptions))
    )
    solver.add(minimization_constraint)
    # Check for satisfiability
    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        stats = solver.statistics()
        print(f"Minimum Weight: {model[min_weight]}")
        print(f"Z3 Solving Time: {stats.get_key_value('time')} sec") # time taken
        print(f"Z3 Num Conflicts: {stats.get_key_value('conflicts')}") # approx. number of branches explored by Z3
        print("==================================")
        print("Full Model:")
        print(model)
    elif result == z3.unsat:
        print("The formula is unsatisfiable.") # This should never happen
    else:
        print("The satisfiability of the formula could not be determined.") # Hopefully this never happens

def alt_solve_assumptions(variables: list[z3.BoolRef], assumptions: list[Assumption]):
    """
    Alternative encoding of the solve_assumptions function. This function uses Z3 Optimize
    and seems to be much more efficient than the original solve_assumptions function.
    """
    optimizer = z3.Optimize()
    min_weight = z3.Int('min_weight')
    assumption_implications = z3.And([z3.Implies(a.variable, a.consequent) for a in assumptions])
    implications_with_neg_conclusion = z3.And(assumption_implications, z3.Not(variables[0]))
    UNSAT = z3.Not(exists_bool_expr(variables, implications_with_neg_conclusion))
    CON = exists_bool_expr(variables, assumption_implications)
    optimizer.add(UNSAT)
    optimizer.add(CON)
    optimizer.add(min_weight == Assumption.assumptions_weight(assumptions))
    optimizer.minimize(min_weight)
    # Check for satisfiability
    result = optimizer.check()
    if result == z3.sat:
        model = optimizer.model()
        stats = optimizer.statistics()
        print(f"Minimum Weight: {model[min_weight]}")
        print(f"Z3 Solving Time: {stats.get_key_value('time')} sec") # time taken
        print(f"Z3 Num Conflicts: {stats.get_key_value('sat conflicts')}") # approx. number of branches explored by Z3
        print("==================================")
        print("Full Model:")
        print(model)
    elif result == z3.unsat:
        print("The formula is unsatisfiable.") # This should never happen
    else:
        print("The satisfiability of the formula could not be determined.") # Hopefully this never happens

def get_crate_metadata(crate: str) -> dict:
    """
    Returns the metadata for a given crate.
    """
    # TODO: Connect to Cargo Sherlock, implement this function
    if crate == "anyhow_v1.0.82":
        return {
            "passed_audit": True,
            "num_side_effects": 0,
            "downloads": 100,
            "in_rust_sec": False,
            "stars": 125,
            "forks": 3,
            "failed_rudra": False,
            "dependencies": ["backtrace_v0.3.63"],
            "developers": ["dtolnay"]
        }
    elif crate == "backtrace_v0.3.63":
        return {
            "passed_audit": True,
            "num_side_effects": 5,
            "downloads": 1_000_000,
            "in_rust_sec": False,
            "stars": 125,
            "forks": 3,
            "failed_rudra": False,
            "dependencies": [],
            "developers": ["alexcrichton"]
        }

def get_user_metadata(user: str) -> dict:
    """
    Returns the metadata for a given user.
    """
    # TODO: Connect to Cargo Sherlock, implement this function
    if user == "dtolnay":
        return {
            "stars": 100,
            "forks": 10
        }
    elif user == "alexcrichton":
        return {
            "stars": 125,
            "forks": 3
        }

def complete_analysis(crate: str):
    """
    Performs a complete analysis for a given crate.
    """
    metadata = get_crate_metadata(crate)
    # add main crate assumptions
    variables, assumptions = assumptions_for(crate, metadata)
    for u in metadata["developers"]:
        user_metadata = get_user_metadata(u)
        # add main crate developer assumptions
        user_variables, user_assumptions = reputable_user(u, user_metadata)
        variables.extend(user_variables)
        assumptions.extend(user_assumptions)
    for d in metadata["dependencies"]:
        dep_metadata = get_crate_metadata(d)
        # add dependency crate assumptions
        dep_variables, dep_assumptions = assumptions_for(d, dep_metadata) 
        variables.extend(dep_variables)
        assumptions.extend(dep_assumptions)
        for u in dep_metadata["developers"]:
            # add dependency crate developer assumptions
            user_metadata = get_user_metadata(u)
            user_variables, user_assumptions = reputable_user(u, user_metadata)
            variables.extend(user_variables)
            assumptions.extend(user_assumptions)
    # solve the assumptions, find the minimum weight
    alt_solve_assumptions(variables, assumptions)

def main():
    # result = parser()
    # first_crate = result[0]
    # for i in first_crate:
    #    print(*i)
    # print(dict(*first_crate[3])['downloads']) # downloads
    # downloads = int(dict(*first_crate[3])['downloads'])
    # print(dict(*first_crate[0])) # RustSec
    # print(first_crate[1] is not None) # Has a passed audit
    # passed_audit = first_crate[1] is not None
    complete_analysis("anyhow_v1.0.82")

if __name__ == "__main__":
    main()
