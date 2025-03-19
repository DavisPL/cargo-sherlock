# This file contains the main functions for solving the minimum cost problem using Z3.
import datetime
import logging
import z3
import helpers.costs as costs
import helpers.crate_data as crate_data
import helpers.developer_data as developer_data
from helpers.assumption import Assumption, CrateAssumptionSummary
from helpers.crate_data import CrateVersion
from helpers.rustsectry import worst_label

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
        Assumption(f"{developer} is trusted", trusted, 70),
        Assumption(f"{developer} being in the trusted list implies they are trusted", z3.Implies(in_trusted_list, trusted), 5)
    ]

    return (unknown_vars, assumptions)

def get_positive_assumptions(
        crate: CrateVersion, 
        metadata: dict, 
        analyzed_crates: set[CrateVersion] = set(),
        analyzed_developers: set[str] = set()
    ) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of Z3 variables and possible assumptions for a given crate.
    """
    # Unknown variables
    safe = z3.Bool(f"{crate}_safe")  # crate is safe
    good_downloads = z3.Bool(f"{crate}_high_downloads")  # crate has a 'good enough' number of downloads
    good_repo_stats = z3.Bool(f"{crate}_high_repo_stats")  # crate repo has a 'good enough' number of stars and forks
    dependencies_safe: list[z3.BoolRef] = [z3.Bool(f"{dep}_safe") for dep in metadata["dependencies"]]
    developers_trusted: list[z3.BoolRef] = [z3.Bool(f"{dev}_trusted") for dev in metadata["developers"]]
    unknown_vars = [safe, good_downloads, good_repo_stats] + dependencies_safe

    # Known variables
    current_audit = z3.BoolVal(metadata["passed_audit"])  # crate passed audit
    no_side_effects = z3.BoolVal(metadata["num_side_effects"] == 0)  # crate has no side effects
    past_audit = z3.BoolVal(metadata["past_audit"])  # crate passed audit in the past
    
    assumptions = [
        Assumption(f"{crate} is safe", safe, costs.MAX_COST),
        Assumption(f"{crate} has many downloads", good_downloads, costs.downloads_cost(metadata["downloads"])),
        Assumption(f"{crate} having many downloads implies it is safe", z3.Implies(good_downloads, safe), 25),
        Assumption(f"{crate} having a current audit implies it is safe", z3.Implies(current_audit, safe), 5),
        Assumption(f"{crate} has a past audit implies it is safe", z3.Implies(past_audit, safe), 20),
        Assumption(f"{crate} has many stars and forks", good_repo_stats, costs.repo_stats_cost(metadata["stars"], metadata["forks"])),
        Assumption(f"{crate} having many stars and forks implies it is safe", z3.Implies(good_repo_stats, safe), 20),
        Assumption(f"{crate} having no side effects and having all safe dependencies implies it is safe", z3.Implies(z3.And(no_side_effects, z3.And(dependencies_safe)), safe), 10),
        Assumption(f"{crate} having all trusted developers implies it is safe", z3.Implies(z3.And(developers_trusted), safe), 15),
    ]

    analyzed_crates.add(crate)
    dependency: CrateVersion
    for i, dependency in enumerate(metadata["dependencies"]):
        if dependency in analyzed_crates:
            logger.info(f"Dependency {dependency} has already been analyzed. Skipping.")
            continue
        logger.info(f"Analyzing dependency {dependency} ({i + 1}/{len(metadata['dependencies'])})...")
        analyzed_crates.add(dependency)
        dependency_metadata = crate_data.get_crate_metadata(dependency)
        dependency_vars, dependency_assumptions = get_positive_assumptions(dependency, dependency_metadata, analyzed_crates, analyzed_developers)
        unknown_vars.extend(dependency_vars)
        assumptions.extend(dependency_assumptions)

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

def get_negative_assumptions(
        crate: CrateVersion, 
        metadata: dict,
        analyzed_crates: set[CrateVersion] = set()
    ) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of Z3 variables and possible assumptions to prove a crate is unsafe.
    """
    # Unknown variables
    unsafe = z3.Bool(f"{crate}_unsafe") # crate is unsafe
    many_side_effects = z3.Bool(f"{crate}_many_side_effects") # crate has a high number of side effects
    dependencies_unsafe: list[z3.BoolRef] = [z3.Bool(f"{dep}_unsafe") for dep in metadata["dependencies"]]
    unknown_vars = [unsafe, many_side_effects] + dependencies_unsafe

    rustsec_label = worst_label(metadata["rustsec_label"]) # crate's worst label from RustSec
    # Known variables
    previously_in_rustsec = z3.BoolVal(rustsec_label == "patched") # crate was in the RustSec database in the past
    in_rustsec_info = z3.BoolVal(rustsec_label == "INFO") # crate has an info severity label
    low_severity = z3.BoolVal(rustsec_label == "LOW") # crate has a low severity label
    med_severity = z3.BoolVal(rustsec_label == "MEDIUM") # crate has a medium severity label
    high_severity = z3.BoolVal(rustsec_label == "HIGH") # crate has a high severity label
    critical_severity = z3.BoolVal(rustsec_label == "CRITICAL") # crate has a critical severity label
    fails_miri = z3.BoolVal(metadata["miri_details"]['failed'] != 0) # crate fails Miri tests

    assumptions = [
        Assumption(f"{crate} is unsafe", unsafe, costs.MAX_COST),
        Assumption(f"{crate} previously being in RustSec implies it is unsafe", z3.Implies(previously_in_rustsec, unsafe), 90),
        Assumption(f"{crate} having an info label in RustSec implies it is unsafe", z3.Implies(in_rustsec_info, unsafe), 60),
        Assumption(f"{crate} having a low severity label in RustSec implies it is unsafe", z3.Implies(low_severity, unsafe), 20),
        Assumption(f"{crate} having a medium severity label in RustSec implies it is unsafe", z3.Implies(med_severity, unsafe), 15),
        Assumption(f"{crate} having a high severity label in RustSec implies it is unsafe", z3.Implies(high_severity, unsafe), 10),
        Assumption(f"{crate} having a critical severity label in RustSec implies it is unsafe", z3.Implies(critical_severity, unsafe), 5),
        Assumption(f"{crate} has an unsafe dependency implies it is unsafe", z3.Implies(z3.Or(dependencies_unsafe), unsafe), 70),
        Assumption(f"{crate} has many side effects", many_side_effects, costs.side_effects_cost(metadata["num_side_effects"])),
        Assumption(f"{crate} has many side effects implies it is unsafe", z3.Implies(many_side_effects, unsafe), 60),
        Assumption(f"{crate} failing a Miri test implies it is unsafe", z3.Implies(fails_miri, unsafe), 50),
    ]

    if metadata["rustsec_tag"] is not None:
        uncategorized = z3.BoolVal(rustsec_label == "Uncategorized") # crate has an uncategorized label
        vulnerability_tag = z3.BoolVal("Vulnerability" in metadata["rustsec_tag"]) # crate has a vulnerability tag
        info_unmaintained_tag = z3.BoolVal("INFOUnmaintained" in metadata["rustsec_tag"]) # crate has an info unmaintained tag
        info_unsound_tag = z3.BoolVal("INFOUnsound" in metadata["rustsec_tag"]) # crate has an info unsound tag
        info_notice_tag = z3.BoolVal("INFONotice" in metadata["rustsec_tag"]) # crate has an info notice tag
        assumptions.append(Assumption(f"{crate} being uncategorized and having a vulnerability tag in RustSec implies it is unsafe", z3.Implies(z3.And(uncategorized, vulnerability_tag), unsafe), 10))
        assumptions.append(Assumption(f"{crate} being uncategorized and having a unsound tag in RustSec implies it is unsafe", z3.Implies(z3.And(uncategorized, info_unsound_tag), unsafe), 12))
        assumptions.append(Assumption(f"{crate} being uncategorized and having a notice tag in RustSec implies it is unsafe", z3.Implies(z3.And(uncategorized, info_notice_tag), unsafe), 60))
        assumptions.append(Assumption(f"{crate} being uncategorized and having a unmaintained tag in RustSec implies it is unsafe", z3.Implies(z3.And(uncategorized, info_unmaintained_tag), unsafe), 50))

    analyzed_crates.add(crate)
    dependency: CrateVersion
    for i, dependency in enumerate(metadata["dependencies"]):
        if dependency in analyzed_crates:
            logger.info(f"Dependency {dependency} has already been analyzed. Skipping.")
            continue
        logger.info(f"Analyzing dependency {dependency} ({i + 1}/{len(metadata['dependencies'])})...")
        analyzed_crates.add(dependency)
        dependency_metadata = crate_data.get_crate_metadata(dependency)
        dependency_vars, dependency_assumptions = get_negative_assumptions(dependency, dependency_metadata, analyzed_crates)
        unknown_vars.extend(dependency_vars)
        assumptions.extend(dependency_assumptions)

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
    Propogates the heads of assumptions to create a Z3 formula that is true iff the conclusion is entailed by the assumptions.
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
            
def solve_mintrust(crate: CrateVersion, variables: list[z3.BoolRef], assumptions: list[Assumption], conclusion: z3.BoolRef) -> CrateAssumptionSummary:
    """
    Solves for the minimum cost assumptions necessary to prove a crate is safe. Returns a summary of the assumptions made.
    """
    logger.info(f"Solving for minimum cost of assumptions for {crate}...")
    logger.info(f"Number of Z3 Variables: {len(variables)}")
    optimizer = z3.Optimize()
    optimizer.set("timeout", MAX_MINUTES * 60_000)
    min_cost = z3.Int('min_cost')
    logger.info("Constructing Z3 formula...")
    entails = propogate_heads(variables, assumptions, conclusion)
    logger.info(entails)
    optimizer.add(entails)
    optimizer.add(min_cost == Assumption.assumptions_cost(assumptions))
    logger.info("Finished constructing Z3 formula.")
    logger.info("Solving Z3 formula...")
    optimizer.minimize(min_cost)
    # Check for satisfiability
    result = optimizer.check()
    match result:
        case z3.sat:
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
        case z3.unsat:
            logger.critical("The Z3 formula is unsatisfiable.") # This should never happen
            raise Exception
        case z3.unknown:
            logger.critical("The satisfiability of the formula could not be determined.")
            logger.critical(f"Z3 Reason: {optimizer.reason_unknown()}")
            raise Exception

def solve_positive_mintrust(crate: CrateVersion, metadata: dict) -> CrateAssumptionSummary:
    """
    Solves for the minimum cost assumptions necessary to prove a crate is safe. Returns a summary of the assumptions made.
    """
    logger.info(f"Solving positive mintrust for {crate}")
    variables, assumptions = get_positive_assumptions(crate, metadata)
    conclusion = z3.Bool(f"{crate}_safe")
    solution = solve_mintrust(crate, variables, assumptions, conclusion)
    return solution

def solve_negative_mintrust(crate: CrateVersion, metadata: dict) -> CrateAssumptionSummary:
    """
    Solves for the minimum cost assumptions necessary to prove a crate is unsafe. Returns a summary of the assumptions made.
    """
    logger.info(f"Solving negative mintrust for {crate}")
    variables, assumptions = get_negative_assumptions(crate, metadata)
    conclusion = z3.Bool(f"{crate}_unsafe")
    solution = solve_mintrust(crate, variables, assumptions, conclusion)
    return solution


def complete_analysis(crate: CrateVersion, file = None):
    """
    Performs a complete analysis for a given crate. Prints results to the specified file (or stdout if
    no file is specified).
    """
    # logger.info(f"Performing complete analysis for {crate}")
    # crate_metadata = crate_data.get_crate_metadata(crate)
    # pos_model_result = solve_positive_mintrust(crate, crate_metadata)
    # neg_model_result = solve_negative_mintrust(crate, crate_metadata)
    # trust_cost = sum(a.cost for a in pos_model_result.assumptions_made)
    # distrust_cost = sum(a.cost for a in neg_model_result.assumptions_made)
    # label = costs.combine_costs(trust_cost, distrust_cost)
    # print(f"Trust Cost for {crate} (lower cost is better): {trust_cost} cost", file=file)
    # print("Assumptions made for trusting:", file=file)
    # for a in pos_model_result.assumptions_made:
    #     print(a, file=file)
    # print(f"Distrust Cost for {crate} (higher cost is better): {distrust_cost} cost", file=file)
    # print("Assumptions made for distrusting:", file=file)
    # for a in neg_model_result.assumptions_made:
    #     print(a, file=file)
    # print(f"Severity label for {crate}: {label.name}", file=file)

    logger.info(f"Performing complete analysis for {crate}")

    crate_metadata = crate_data.get_crate_metadata(crate)
    pos_model_result = solve_positive_mintrust(crate, crate_metadata)
    neg_model_result = solve_negative_mintrust(crate, crate_metadata)
    trust_cost = sum(a.cost for a in pos_model_result.assumptions_made)
    distrust_cost = sum(a.cost for a in neg_model_result.assumptions_made)
    label = costs.combine_costs(trust_cost, distrust_cost)

    border = "+" + "-" * 60 + "+"
    header = f"|{'Analysis Report for ' + str(crate):^60}|"

    report_lines = []
    report_lines.append(border)
    report_lines.append(header)
    report_lines.append(border)
    report_lines.append("")
    report_lines.append("Assumptions Summary:")
    report_lines.append("Score Range: 0 (Min) - 100 (Max)")
    report_lines.append("")
    report_lines.append(f"Trust Cost (lower is better): {trust_cost} cost")
    report_lines.append("Assumptions for Trusting:")
    if pos_model_result.assumptions_made:
        for a in pos_model_result.assumptions_made:
            report_lines.append(f"  • {a}")
    else:
        report_lines.append("  (None)")

    report_lines.append("")
    report_lines.append(f"Distrust Cost (higher is better): {distrust_cost} cost")
    report_lines.append("Assumptions for Distrusting:")
    if neg_model_result.assumptions_made:
        for a in neg_model_result.assumptions_made:
            report_lines.append(f"  • {a}")
    else:
        report_lines.append("  (None)")

    report_lines.append("")
    report_lines.append(f"Severity Label: {label.name}")
    report_lines.append("")
    report_lines.append(f"Full details about the crate can be found at: /logs/cache/{crate.name}-{crate.version}.json")
    report_lines.append(border)
    report_lines.append("")

    final_report = "\n".join(report_lines)
    print(final_report, file=file)



def main():
    crate = CrateVersion("anyhow", "1.0.97")
    crate = CrateVersion("tokio", "1.44.1")
    crate = CrateVersion("zlib-rs", "0.3.0")
    complete_analysis(crate)

if __name__ == "__main__":
    main()