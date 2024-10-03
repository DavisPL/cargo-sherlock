# This file contains the main functions for solving the minimum weight problem using Z3.
import argparse
import datetime
import logging
import sys
import z3
import helpers.weights as weights
import helpers.crate_data as crate_data
from helpers.assumption import Assumption, CrateAssumptionSummary, MadeAssumption, NegativeAssumption
from helpers.crate_data import CrateVersion
from pprint import pprint

MAX_MINUTES = 5 # timeout for each call to the solver
MAX_WEIGHT = 500

logfile_name = datetime.datetime.now().strftime('logs/solver/%Y-%m-%d_%H:%M:%S.log')
logging.basicConfig(
    filename=logfile_name,
    encoding="utf-8",
    filemode="w",
    format="%(asctime)s %(levelname)-8s %(message)s",
    level=logging.INFO,
    datefmt="%Y-%m-%d-%Y %H:%M:%S"
)
logger = logging.getLogger(__name__)

def get_crate_assumptions(crate: CrateVersion, metadata: dict) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of Z3 variables and possible assumptions for a given crate. Notably, one of the assumptions is that
    all dependencies of the crate are safe. The weight of this assumption is decided 
    """
    # Unknown variables
    safe = z3.Bool(f"{crate}_safe")  # crate is safe
    good_downloads = z3.Bool(f"{crate}_high_downloads")  # crate has a 'good enough' number of downloads
    good_repo_stats = z3.Bool(f"{crate}_high_repo_stats")  # crate repo has a 'good enough' number of stars and forks
    all_dependencies_safe = z3.Bool(f"{crate}_all_dependencies_safe")  # all crate dependencies are safe
    unknown_vars = [safe, good_downloads, good_repo_stats, all_dependencies_safe]

    # Known variables
    passed_audit = z3.BoolVal(metadata["passed_audit"])  # crate passed audit
    no_side_effects = z3.BoolVal(metadata["num_side_effects"] == 0)  # crate has no side effects
    in_rust_sec = z3.BoolVal(metadata["in_rust_sec"])  # crate is in RustSec

    # Assumptions necessary to prove all dependencies are safe. Each element CrateAssumptionSummary in the list
    # contains the assumptions necessary to prove that a single dependency is safe.
    assumptions_for_dependency_safety: list[CrateAssumptionSummary] = []
    d: CrateVersion
    for d in metadata["dependencies"]:
        assumptions_for_dependency_safety.append(memoized_crate_analysis(d))
    # Duplicate assumptions are removed to avoid double counting the weight of assumptions.
    assumptions_made_no_duplicates = set(a for s in assumptions_for_dependency_safety for a in s.assumptions_made)
    min_weight_for_dependency_safety = sum(a.weight for a in assumptions_made_no_duplicates)

    assumptions = [
        Assumption(f"{crate} is safe", safe, MAX_WEIGHT),
        Assumption(f"{crate} has many downloads", good_downloads, weights.downloads_weight(metadata["downloads"])),
        Assumption(f"{crate} having many downloads implies it is safe", z3.Implies(good_downloads, safe), 10),
        Assumption(f"{crate} having a passed audit implies it is safe", z3.Implies(passed_audit, safe), 30),
        Assumption(f"{crate} has many stars and forks", good_repo_stats, weights.repo_stats_weight(metadata["stars"], metadata["forks"])),
        Assumption(f"{crate} having many stars and forms implies it is safe", z3.Implies(good_repo_stats, safe), 15),
        Assumption(f"{crate} has all safe dependencies", all_dependencies_safe, min_weight_for_dependency_safety),
        Assumption(f"{crate} having no side effects and having all safe dependencies implies it is safe", z3.Implies(z3.And(no_side_effects, all_dependencies_safe), safe), 1),
        NegativeAssumption(f"{crate} appearing in RustSec implies it is less safe (score penalty)", z3.Implies(in_rust_sec, z3.Not(safe)), 50),
    ]

    return (unknown_vars, assumptions)

def memoized_crate_analysis(crate: CrateVersion, processed_crates: list[CrateAssumptionSummary] = []) -> CrateAssumptionSummary:
    """
    Returns the minimum weight of assumptions for a given crate, with the assumptions made for all crates
    stored in the processed_crates list.
    """
    # Check if the crate has already been processed. If it has, return its summary
    summary = next((c for c in processed_crates if c.crate == crate), None)
    if summary is not None:
        return summary
    metadata = crate_data.get_crate_metadata(crate)
    variables, assumptions = get_crate_assumptions(crate, metadata)
    summary = get_crate_assumption_summary(crate, variables, assumptions)
    processed_crates.append(summary)
    return summary

def get_crate_assumption_summary(crate: CrateVersion, variables: list[z3.BoolRef], assumptions: list[Assumption]) -> CrateAssumptionSummary:
    """
    Solves for the minimum weight assumptions necessary to prove a crate is safe. Returns a summary of the assumptions made.
    """
    logger.info(f"Solving for minimum weight of assumptions for {crate}...")
    logger.info(f"Number of Z3 Variables: {len(variables)}")
    optimizer = z3.Optimize()
    optimizer.set("timeout", MAX_MINUTES * 60_000)
    min_weight = z3.Int('min_weight')
    logger.info("Constructing Z3 formula...")
    assumption_implications = z3.And([z3.Implies(a.variable, a.consequent) for a in assumptions])
    crate_is_safe = z3.Bool(f"{crate}_safe")
    implications_with_neg_conclusion = z3.And(assumption_implications, z3.Not(crate_is_safe))
    UNSAT = z3.Not(exists_bool_expr(variables, implications_with_neg_conclusion))
    CON = exists_bool_expr(variables, assumption_implications)
    optimizer.add(UNSAT)
    optimizer.add(CON)
    optimizer.add(min_weight == Assumption.assumptions_weight(assumptions))
    logger.info("Finished constructing Z3 formula.")
    logger.info("Solving Z3 formula...")
    optimizer.minimize(min_weight)
    # Check for satisfiability
    result = optimizer.check()
    if result == z3.sat:
        model = optimizer.model()
        stats = optimizer.statistics()
        logger.info(f"Minimum weight of assumptions for {crate}: {model[min_weight]}")
        # for some reason, the time taken is not always recorded in the statistics (it seems to not be recorded when the
        # formula is determined to be satisfiable very quickly)
        z3_solving_time = stats.get_key_value('time') if "time" in stats.keys() else 0
        logger.info(f"Z3 Solving Time: {z3_solving_time} sec")
        if "conflicts" in stats.keys():
            logger.info(f"Z3 Num Conflicts: {stats.get_key_value('conflicts')}")
        elif "sat conflicts" in stats.keys():
            logger.info(f"Z3 Num Conflicts: {stats.get_key_value('sat conflicts')}")
        else:
            logger.info("Z3 Num Conflicts: N/A")
        assumptions_made = [MadeAssumption(a.name, a.weight) for a in assumptions if model[a.variable] == a.default_assignment()]
        logger.info("Assumptions Made:")
        for a in assumptions_made:
            logger.info(f"{a.name}: {a.weight} wt")
        return CrateAssumptionSummary(crate, assumptions_made)
    elif result == z3.unsat:
        logger.critical("The Z3 formula is unsatisfiable.") # This should never happen
        raise Exception
    else:
        logger.error("The satisfiability of the formula could not be determined.")
        logger.error(f"Z3 Reason: {optimizer.reason_unknown()}")
        return CrateAssumptionSummary(crate, [MadeAssumption(f"{crate.name}-{crate.version}_safe", MAX_WEIGHT)])

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

def complete_analysis(crate: CrateVersion, file = None):
    """
    Performs a complete analysis for a given crate. Prints results to the specified file (or stdout if
    no file is specified).
    """
    summary = memoized_crate_analysis(crate)
    trust_score = sum(a.weight for a in summary.assumptions_made)
    assumptions = []
    print(f"Trust Score for {crate}: {trust_score}", file=file)
    print("Assumptions Made:", file=file)
    for a in summary.assumptions_made:
        assumptions.append(f"{a.name}: {a.weight} wt")
        print(f"{a.name}: {a.weight} wt", file=file)

def main():
    parser = argparse.ArgumentParser(description="Perform a complete analysis for a given crate.")
    parser.add_argument("crate_name", type=str, help="The name of the crate to analyze.")
    parser.add_argument("crate_version", type=str, help="The version of the crate to analyze.")
    parser.add_argument("--output", default=None, type=str, help="Output file path to save crate information.")
    args = parser.parse_args()
    crate = CrateVersion(args.crate_name, args.crate_version)
    complete_analysis(crate, args.output)

if __name__ == "__main__":
    main()
