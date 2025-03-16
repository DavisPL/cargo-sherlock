# This file contains the main functions for solving the minimum cost problem using Z3.
import datetime
import logging
import z3
import helpers.costs as costs
import helpers.crate_data as crate_data
import helpers.developer_data as developer_data
from helpers.assumption import Assumption, CrateAssumptionSummary, MAX_COST
from helpers.crate_data import CrateVersion

MAX_MINUTES = 5 # timeout for the solver call

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

def get_crate_assumptions(
        crate: CrateVersion, 
        metadata: dict, 
        analyzed_crates: set[CrateVersion] = set(),
        analyzed_developers: set[str] = set()
    ) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of Z3 variables and possible assumptions for a given crate. Notably, one of the assumptions is that
    all dependencies of the crate are safe. The cost of this assumption is decided by recursively calling this function
    on the dependencies of the crate.
    """
    # Unknown variables
    safe = z3.Bool(f"{crate}_safe")  # crate is safe
    good_downloads = z3.Bool(f"{crate}_high_downloads")  # crate has a 'good enough' number of downloads
    good_repo_stats = z3.Bool(f"{crate}_high_repo_stats")  # crate repo has a 'good enough' number of stars and forks
    dependencies_safe: list[z3.BoolRef] = [z3.Bool(f"{dep}_safe") for dep in metadata["dependencies"]]
    developers_trusted: list[z3.BoolRef] = [z3.Bool(f"{dev}_trusted") for dev in metadata["developers"]]
    unknown_vars = [safe, good_downloads, good_repo_stats] + dependencies_safe

    # Known variables
    passed_audit = z3.BoolVal(metadata["passed_audit"])  # crate passed audit
    no_side_effects = z3.BoolVal(metadata["num_side_effects"] == 0)  # crate has no side effects

    assumptions_for_dependency_safety: list[Assumption] = []
    analyzed_crates.add(crate)
    dependency: CrateVersion
    for i, dependency in enumerate(metadata["dependencies"]):
        if dependency in analyzed_crates:
            logger.info(f"Dependency {dependency} has already been analyzed. Skipping.")
            continue
        logger.info(f"Analyzing dependency {dependency} ({i + 1}/{len(metadata['dependencies'])})...")
        analyzed_crates.add(dependency)
        dependency_metadata = crate_data.get_crate_metadata(dependency)
        dependency_vars, dependency_assumptions = get_crate_assumptions(dependency, dependency_metadata, analyzed_crates, analyzed_developers)
        unknown_vars.extend(dependency_vars)
        assumptions_for_dependency_safety.extend(dependency_assumptions)
    
    assumptions = [
        Assumption(f"{crate} is safe", safe, MAX_COST),
        Assumption(f"{crate} has many downloads", good_downloads, costs.downloads_cost(metadata["downloads"])),
        Assumption(f"{crate} having many downloads implies it is safe", z3.Implies(good_downloads, safe), 10),
        Assumption(f"{crate} having a passed audit implies it is safe", z3.Implies(passed_audit, safe), 30),
        Assumption(f"{crate} has many stars and forks", good_repo_stats, costs.repo_stats_cost(metadata["stars"], metadata["forks"])),
        Assumption(f"{crate} having many stars and forks implies it is safe", z3.Implies(good_repo_stats, safe), 15),
        Assumption(f"{crate} having no side effects and having all safe dependencies implies it is safe", z3.Implies(z3.And(no_side_effects, z3.And(dependencies_safe)), safe), 1),
        Assumption(f"{crate} having all trusted developers implies it is safe", z3.Implies(z3.And(developers_trusted), safe), 2),
    ]

    for developer in metadata["developers"]:
        if developer in analyzed_developers:
            logger.info(f"Developer {developer} has already been analyzed. Skipping.")
            continue
        logger.info(f"Analyzing developer {developer}...")
        analyzed_developers.add(developer)
        metadata = developer_data.get_developer_metadata(developer)
        developer_variables, developer_assumptions = get_developer_assumptions(developer, metadata)
        assumptions.extend(developer_assumptions)
        unknown_vars.extend(developer_variables)

    return (unknown_vars, assumptions)

def get_head(horn_clause: z3.BoolRef) -> z3.BoolRef | None:
    """
    Gets the head (unnegated literal) of a horn clause in disjunctive form. Returns None if no head is found.
    """
    literals = horn_clause.children() if z3.is_or(horn_clause) else [horn_clause]
    for literal in literals:
        if not z3.is_not(literal):
            return literal
    return None

def get_body(horn_clause: z3.BoolRef) -> z3.BoolRef:
    """
    Gets the body (conjunction of negated literals) of a horn clause in disjunctive form.
    """
    literals = horn_clause.children() if z3.is_or(horn_clause) else [horn_clause]
    body_literals = [z3.Not(literal) for literal in literals if z3.is_not(literal)]
    return z3.And(body_literals)

def propogate_heads(variables: list[z3.BoolRef], assumptions: list[Assumption], conclusion: z3.BoolRef) -> z3.BoolRef:
    """
    Propogates the heads of assumptions to create a Z3 formula that is satisfiable iff the conclusion is entailed by the assumptions.
    """
    assumption_implications = z3.And([z3.Implies(a.variable, a.consequent) for a in assumptions])
    horn_assumptions = z3.simplify(assumption_implications)
    clauses: list[z3.BoolRef] = horn_assumptions.children() if z3.is_and(horn_assumptions) else [horn_assumptions]
    conclusion_proving_bodies = []
    for clause in clauses:
        head = get_head(clause)
        if head == conclusion:
            body = get_body(clause)
            conclusion_proving_bodies.append(body)
    entails = z3.Or(conclusion_proving_bodies) # formula that is satisfiable iff the conclusion is entailed by the assumptions
    for var in variables:
        substitution_bodies = []
        for clause in clauses:
            head = get_head(clause)
            if head == var:
                body = get_body(clause)
                substitution_bodies.append(body)
        variable_substitution = z3.Or(substitution_bodies) # disjunction of bodies that imply the variable
        entails = z3.substitute(entails, (var, variable_substitution))
        for clause in clauses:
            clause = z3.substitute(clause, (var, variable_substitution)) # apply the substitution to the rest of the clauses
    return z3.simplify(entails)
            
def get_crate_assumption_summary(crate: CrateVersion, variables: list[z3.BoolRef], assumptions: list[Assumption]) -> CrateAssumptionSummary:
    """
    Solves for the minimum cost assumptions necessary to prove a crate is safe. Returns a summary of the assumptions made.
    """
    logger.info(f"Solving for minimum cost of assumptions for {crate}...")
    logger.info(f"Number of Z3 Variables: {len(variables)}")
    optimizer = z3.Optimize()
    optimizer.set("timeout", MAX_MINUTES * 60_000)
    min_cost = z3.Int('min_cost')
    logger.info("Constructing Z3 formula...")
    crate_is_safe = z3.Bool(f"{crate}_safe")
    entails = propogate_heads(variables, assumptions, crate_is_safe)
    logger.info(entails)
    optimizer.add(entails)
    optimizer.add(min_cost == Assumption.assumptions_cost(assumptions))
    logger.info("Finished constructing Z3 formula.")
    logger.info("Solving Z3 formula...")
    optimizer.minimize(min_cost)
    # Check for satisfiability
    result = optimizer.check()
    if result == z3.sat:
        model = optimizer.model()
        stats = optimizer.statistics()
        logger.info(f"Minimum cost of assumptions for {crate}: {model[min_cost]}")
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
        assumptions_made = [Assumption(f"{crate} is safe", crate_is_safe, MAX_COST)]
        return CrateAssumptionSummary(crate, assumptions_made)

def complete_analysis(crate: CrateVersion, file = None):
    """
    Performs a complete analysis for a given crate. Prints results to the specified file (or stdout if
    no file is specified).
    """
    logger.info(f"Performing complete analysis for {crate}")
    crate_metadata = crate_data.get_crate_metadata(crate)
    variables, assumptions = get_crate_assumptions(crate, crate_metadata)
    summary = get_crate_assumption_summary(crate, variables, assumptions)
    trust_cost = sum(a.cost for a in summary.assumptions_made)

    normalized_trust_cost = (trust_cost / MAX_COST) * 100
    # normalized_trust_cost = min(normalized_trust_cost, 1)


    print(f"Trust Cost for {crate} (lower cost is better): {normalized_trust_cost} cost", file=file)
    print("Assumptions Made:", file=file)
    for a in summary.assumptions_made:
        print(a, file=file)

def main():
    crate = CrateVersion("tokio", "1.44.1")
    crate = CrateVersion("anyhow", "1.0.97")
    complete_analysis(crate)

if __name__ == "__main__":
    main()