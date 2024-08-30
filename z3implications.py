raise DeprecationWarning("This file is deprecated. Use the new implementation in solver.py instead.")

import math
import csv
import sys
import argparse
from typing import NamedTuple, DefaultDict
from timeit import default_timer as timer
import z3
import logger
import ast

class CrateVersion(NamedTuple):
    name: str
    version: str

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

def assumptions_for(crate: CrateVersion, metadata: dict) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of variables and a list of assumptions to prove that a given crate is safe.
    """
    # Unknown variables
    safe = z3.Bool(f"{crate.name}-{crate.version}_safe")  # crate is safe
    good_downloads = z3.Bool(f"{crate.name}-{crate.version}_high_downloads")  # crate has a 'good enough' number of downloads
    good_repo_stats = z3.Bool(f"{crate.name}-{crate.version}_high_repo_stats")  # crate repo has a 'good enough' number of stars and forks
    dependency_safety = []
    user_safety = []
    d: CrateVersion # the dependencies are of type CrateVersion
    for d in metadata["dependencies"]:
        dependency_safety.append(z3.Bool(f"{d.name}-{d.version}_safe")) # dependency is safe
    for u in metadata["developers"]:
        user_safety.append(z3.Bool(f"{u}_trusted")) # user is trusted
    
    # Known variables
    passed_audit = z3.BoolVal(metadata["passed_audit"])  # crate passed audit
    no_side_effects = z3.BoolVal(metadata["num_side_effects"] == 0)  # crate has no side effects
    in_rust_sec = z3.BoolVal(metadata["in_rust_sec"])  # crate is in RustSec


    return (
        [safe, good_downloads, good_repo_stats], 
        [
            Assumption(f"a0_{crate.name}-{crate.version}", safe, 1500),
            Assumption(f"a1_{crate.name}-{crate.version}", good_downloads, downloads_weight_function(metadata["downloads"])),
            Assumption(f"a2_{crate.name}-{crate.version}", z3.Implies(good_downloads, safe), 90),
            Assumption(f"a3_{crate.name}-{crate.version}", z3.Implies(passed_audit, safe), 100),
            Assumption(f"a4_{crate.name}-{crate.version}", z3.Implies(z3.And(no_side_effects, z3.And(dependency_safety)), safe), 8),
            Assumption(f"a5_{crate.name}-{crate.version}", good_repo_stats, repo_stats_weight_function(metadata["stars"], metadata["forks"])),
            Assumption(f"a6_{crate.name}-{crate.version}", z3.Implies(good_repo_stats, safe), 11),
            Assumption(f"a7_{crate.name}-{crate.version}", z3.Implies(z3.And(user_safety), safe), 5),
            NegativeAssumption(f"na0_{crate.name}-{crate.version}", z3.Implies(in_rust_sec, z3.Not(safe)), 1000),
        ]
    )

def reputable_user(user: str, metadata: dict) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of assumptions for a reputable user.
    """
    # TODO: Expand this function to include more assumptions about reputable users.
    # Unknown variables
    trusted = z3.Bool(f"{user}_trusted")  # user is trusted

    return (
        [trusted], 
        [
            Assumption(f"ua0_{user}", trusted, 100),
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

def solve_assumptions(crate: CrateVersion, variables: list[z3.BoolRef], assumptions: list[Assumption]):
    """
    Finds the minimum weight of a set of assumptions that prove the given crate is safe.
    """
    raise DeprecationWarning("This function is deprecated. Use alt_solve_assumptions instead.")
    solver = z3.Solver()
    min_weight = z3.Int('min_weight')
    assumption_implications = z3.And([z3.Implies(a.variable, a.consequent) for a in assumptions])
    crate_is_safe = z3.Bool(f"{crate.name}-{crate.version}_safe")
    implications_with_neg_conclusion = z3.And(assumption_implications, z3.Not(crate_is_safe))
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
        assumptions_made = ((a.name, a.weight) for a in assumptions if model[a.variable] == a.default_assignment())
        print("Assumptions Made:")
        for pair in assumptions_made:
            print(f"{pair[0]}: {pair[1]} wt")
        print("==================================")
        print("Full Model:")
        print(model)
    elif result == z3.unsat:
        print("The formula is unsatisfiable.") # This should never happen
    else:
        print("The satisfiability of the formula could not be determined.") # Hopefully this never happens

def alt_solve_assumptions(crate: CrateVersion, variables: list[z3.BoolRef], assumptions: list[Assumption]):
    """
    Alternative encoding of the solve_assumptions function. This function uses Z3 Optimize
    and seems to be much more efficient than the original solve_assumptions function.
    """
    print(f"Number of Z3 Variables: {len(variables)}")
    optimizer = z3.Optimize()
    min_weight = z3.Int('min_weight')
    formula_construct_start = timer()
    assumption_implications = z3.And([z3.Implies(a.variable, a.consequent) for a in assumptions])
    crate_is_safe = z3.Bool(f"{crate.name}-{crate.version}_safe")
    implications_with_neg_conclusion = z3.And(assumption_implications, z3.Not(crate_is_safe))
    UNSAT = z3.Not(z3.Exists(variables, implications_with_neg_conclusion))
    CON = z3.Exists(variables, assumption_implications)
    optimizer.add(UNSAT)
    optimizer.add(CON)
    optimizer.add(min_weight == Assumption.assumptions_weight(assumptions))
    formula_construct_end = timer()
    print(f"Formula Construction Time: {formula_construct_end - formula_construct_start:.3f} sec")
    optimizer.minimize(min_weight)
    # Check for satisfiability
    result = optimizer.check()
    if result == z3.sat:
        model = optimizer.model()
        stats = optimizer.statistics()
        print(f"Minimum Weight: {model[min_weight]}")
        print(f"Z3 Solving Time: {stats.get_key_value('time')} sec") # time taken
        print(f"Z3 Num Conflicts: {stats.get_key_value('conflicts')}") # approx. number of branches explored by Z3
        print("==================================")
        assumptions_made = ((a.name, a.weight) for a in assumptions if model[a.variable] == a.default_assignment())
        print("Assumptions Made:")
        for pair in assumptions_made:
            print(f"{pair[0]}: {pair[1]} wt")
        print("==================================")
        print("Full Model:")
        print(model)
    elif result == z3.unsat:
        print("The formula is unsatisfiable.") # This should never happen
    else:
        print("The satisfiability of the formula could not be determined.") # Hopefully this never happens

def parse_single_file(file: str) -> list:
    csv.field_size_limit(sys.maxsize)
    with open(file, 'r') as f:
        contents = f.read()
        sections = contents.split('************************************')
        result = []
        for section in sections:
            # print(type(section), section)
            # if type(section) == dict():
            #     print("i have tree" , section)
            # Remove any leading/trailing whitespace
            section = section.strip()
            if not section:
                continue
            lines = section.splitlines()
            reader = csv.DictReader(lines)
            data = list(reader)
            result.append(data)
    return result

def create_audit_summary(crate_info: list[list[dict]]):
    # Initialize the audit summary dictionary using DefaultDict
    audit_summary = DefaultDict(list)
    # Iterate over the parsed data to update the dictionary
    section: list[dict]
    for section in crate_info:
        if not section:
            continue
        item: dict
        for item in section:
            if item.get('event') == 'RustSec':
                audit_summary['in_rust_sec'] = item.get('label') != 'Safe'
            
            elif item.get('event') == 'Author':
                audit_summary['developers'].append(item.get('username'))

            elif item.get('event') == 'github_stats':
                audit_summary['stars'] = int(item.get('stars', 0) or 0)
                audit_summary['forks'] = int(item.get('forks', 0) or 0)
            
            elif item.get('event') == 'Downloads':
                audit_summary['downloads'] = int(item.get('downloads', 0) or 0)
            
            elif item.get('event') == 'Side Effects':
                audit_summary['num_side_effects'] = int(item.get('total', 0) or 0)

            elif 'Rudra' in item:
                audit_summary['failed_rudra'] = True

            elif item.get('event') == 'audits':
                audit_summary['audits'].append({
                    'organization': item.get('organization', ''),
                    'criteria': item.get('criteria', ''),
                    'delta': item.get('delta', ''),
                    'notes': item.get('notes', '')
                })

            elif item.get('event') == 'dependency_tree':
                if 'dependency_tree' in item:
                    tree: dict = ast.literal_eval(item.get('dependency_tree'))
                    flat_tree: dict = {f"{key[0]}-{key[1]}": value for key, value in tree.items()}
                    dependencies = []
                    for key, _ in flat_tree.items():
                        name = "-".join(key.split("-")[:-1])
                        version = key.split("-")[-1]
                        cv = CrateVersion(name, version)
                        dependencies.append(cv)
                    audit_summary['dependencies'] = dependencies
                        # item.update({"dependency_tree": key})
                    
                    # print("tree is:",audit_summary['dependency_tree'])
                    # exit(1)

    # Set passed_audit to True if there are any audits
    if audit_summary['audits']:
        audit_summary['passed_audit'] = True
    
    return audit_summary

def get_crate_metadata(crate: CrateVersion) -> dict:
    """
    Returns the metadata for a given crate.
    """
    # Runs cargo sherlock
    logger.logger(crate.name, crate.version, "exp")
    crate_info = parse_single_file(f"logs/exp/{crate.name}-{crate.version}.csv")
    audit_summary = create_audit_summary(crate_info)

    import pprint
    pp = pprint.PrettyPrinter(indent=2)
    pp.pprint(audit_summary)

    return audit_summary

def get_user_metadata(user: str) -> dict:
    """
    Returns the metadata for a given user.
    """
    # TODO: Find a way to implement this function
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
    else:
        return {
            "stars": 0,
            "forks": 0
        }

def get_all_assumptions(
        crate: CrateVersion,
        max_depth: None | int = None,
        variables: list[z3.BoolRef] = [], 
        assumptions: list[Assumption] = []
    ) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns all variables and assumptions (including dependency and user variables/assumptions)
    for a given crate. If max_depth is not None, then the function will only return variables
    and assumptions for dependency crates up to the given depth.
    """
    metadata = get_crate_metadata(crate)
    # add main crate assumptions
    crate_variables, crate_assumptions = assumptions_for(crate, metadata)
    variables.extend(crate_variables)
    assumptions.extend(crate_assumptions)
    for u in metadata["developers"]:
        user_metadata = get_user_metadata(u)
        # add main crate developer assumptions
        user_variables, user_assumptions = reputable_user(u, user_metadata)
        variables.extend(user_variables)
        assumptions.extend(user_assumptions)
    d: CrateVersion # the dependencies are of type CrateVersion
    for d in metadata["dependencies"]:
        if max_depth is not None and max_depth == 0:
            break
        max_depth = max_depth - 1 if max_depth is not None else None
        get_all_assumptions(d, max_depth, variables, assumptions)
    return list(set(variables)), list(set(assumptions))

def complete_analysis(crate: CrateVersion):
    """
    Performs a complete analysis for a given crate. Prints results to stdout.
    """
    variables, assumptions = get_all_assumptions(crate)
    alt_solve_assumptions(crate, variables, assumptions)

def main():
    parser = argparse.ArgumentParser(description="Perform a complete analysis for a given crate.")
    parser.add_argument("crate_name", type=str, help="The name of the crate to analyze.")
    parser.add_argument("crate_version", type=str, help="The version of the crate to analyze.")
    args = parser.parse_args()
    crate = CrateVersion(args.crate_name, args.crate_version)
    complete_analysis(crate)

if __name__ == "__main__":
    main()
