# This file contains the main functions for solving the minimum weight problem using Z3.
import argparse
import datetime
import logging
import z3
import helpers.weights as weights
import helpers.crate_data as crate_data
import helpers.developer_data as developer_data
from helpers.assumption import Assumption, CrateAssumptionSummary, NegativeAssumption
from helpers.crate_data import CrateVersion

MAX_MINUTES = 5 # timeout for the single solver call
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

def get_developer_assumptions(developer: str, metadata: dict) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of Z3 variables and possible assumptions for a given developer. 
    """
    # TODO: Expand this function to include more assumptions about developers

    # Unknown variables
    trusted = z3.Bool(f"{developer}_trusted")  # developer is trusted
    unknown_vars = [trusted]

    # Known variables
    in_trusted_list = z3.BoolVal(metadata["in_trusted_list"])  # developer is in the list of trusted developers

    assumptions = [
        Assumption(f"{developer} is trusted", trusted, 450),
        Assumption(f"{developer} being in the trusted list implies they are trusted", z3.Implies(in_trusted_list, trusted), 3)
    ]

    return (unknown_vars, assumptions)


def get_crate_assumptions(crate: CrateVersion, metadata: dict, processed_crates: set[CrateVersion] = set()) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of Z3 variables and possible assumptions for a given crate.
    """
    processed_crates.add(crate) # Mark the current crate as processed to avoid repeating calls

    # Unknown variables
    safe = z3.Bool(f"{crate}_safe")  # crate is safe
    good_downloads = z3.Bool(f"{crate}_high_downloads")  # crate has a 'good enough' number of downloads
    good_repo_stats = z3.Bool(f"{crate}_high_repo_stats")  # crate repo has a 'good enough' number of stars and forks
    unknown_vars = [safe, good_downloads, good_repo_stats]

    # Known variables
    passed_audit = z3.BoolVal(metadata["passed_audit"])  # crate passed audit
    no_side_effects = z3.BoolVal(metadata["num_side_effects"] == 0)  # crate has no side effects
    in_rust_sec = z3.BoolVal(metadata["in_rust_sec"])  # crate is in RustSec
        
    assumptions = [
        Assumption(f"{crate} is safe", safe, MAX_WEIGHT),
        Assumption(f"{crate} has many downloads", good_downloads, weights.downloads_weight(metadata["downloads"])),
        Assumption(f"{crate} having many downloads implies it is safe", z3.Implies(good_downloads, safe), 10),
        Assumption(f"{crate} having a passed audit implies it is safe", z3.Implies(passed_audit, safe), 30),
        Assumption(f"{crate} has many stars and forks", good_repo_stats, weights.repo_stats_weight(metadata["stars"], metadata["forks"])),
        Assumption(f"{crate} having many stars and forks implies it is safe", z3.Implies(good_repo_stats, safe), 15),
        NegativeAssumption(f"{crate} appearing in RustSec implies it is less safe (score penalty)", z3.Implies(in_rust_sec, z3.Not(safe)), 50),
    ]

    developers_trusted: list[z3.BoolRef] = []
    for developer in metadata["developers"]:
        developer_metadata = developer_data.get_developer_metadata(developer)
        developer_variables, developer_assumptions = get_developer_assumptions(developer, developer_metadata)
        unknown_vars += developer_variables
        developers_trusted.append(z3.Bool(f"{developer}_trusted"))
        assumptions.append(
            Assumption(
                f"{crate} having all trusted developers implies it is safe", 
                z3.Implies(z3.And(developers_trusted), safe), 2
            )
        )
        assumptions.extend(developer_assumptions)

    dependencies_safe: list[z3.BoolRef] = []
    dependency: CrateVersion
    for dependency in metadata["dependencies"]:
        dependency_metadata = crate_data.get_crate_metadata(dependency)
        dependency_variables, dependency_assumptions = get_crate_assumptions(dependency, dependency_metadata, processed_crates)
        dependencies_safe.append(z3.Bool(f"{dependency}_safe"))
        unknown_vars += dependency_variables
        assumptions.append(
            Assumption(
                f"{crate} having no side effects and having all safe dependencies implies it is safe", 
                z3.Implies(z3.And(no_side_effects, z3.And(dependencies_safe)), safe), 1
            )
        )
        assumptions.extend(dependency_assumptions)
    
    return (unknown_vars, assumptions)

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
        assumptions_made = [a for a in assumptions if model[a.variable] == a.default_assignment()]
        logger.info("Assumptions Made:")
        for a in assumptions_made:
            logger.info(a.__repr__())
        return CrateAssumptionSummary(crate, assumptions_made)
    elif result == z3.unsat:
        logger.critical("The Z3 formula is unsatisfiable.") # This should never happen
        raise Exception
    else:
        logger.error("The satisfiability of the formula could not be determined.")
        logger.error(f"Z3 Reason: {optimizer.reason_unknown()}")
        assumptions_made = [Assumption(f"{crate} is safe", crate_is_safe, MAX_WEIGHT)]
        return CrateAssumptionSummary(crate, assumptions_made)

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
    metadata = crate_data.get_crate_metadata(crate)
    variables, assumptions = get_crate_assumptions(crate, metadata)
    summary = get_crate_assumption_summary(crate, variables, assumptions)
    trust_score = sum(a.weight for a in summary.assumptions_made)
    print(f"Trust Score for {crate}: {trust_score}", file=file)
    print("Assumptions Made:", file=file)
    for a in summary.assumptions_made:
        print(a, file=file)

def main():
    parser = argparse.ArgumentParser(description="Perform a complete analysis for a given crate.")
    parser.add_argument("crate_name", type=str, help="The name of the crate to analyze.")
    parser.add_argument("crate_version", type=str, help="The version of the crate to analyze.")
    parser.add_argument("--output", default=None, type=str, help="Output file path to save crate information.")
    args = parser.parse_args()
    crate = CrateVersion(args.crate_name, args.crate_version)
    # crate = CrateVersion("anyhow", "1.0.91")
    complete_analysis(crate, args.output)
    # complete_analysis(crate)

if __name__ == "__main__":
    main()
