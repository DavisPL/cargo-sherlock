# This file contains the main functions for solving the minimum weight problem using Z3.
import argparse
from timeit import default_timer as timer
import z3
from helpers.assumption import Assumption, assumptions_for
from helpers.assumption import CrateVersion, User, MAX_WEIGHT
import helpers.crate_data as crate_data

MAX_MINUTES = 5 # timeout for each call to the solver

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

def get_min_weight(objective: CrateVersion | User, variables: list[z3.BoolRef], assumptions: list[Assumption]) -> int:
    """
    Returns the minimum weight of the assumptions that need to be made in order to prove that the objective
    (either a crate or a user) is safe.
    """
    print(f"Solving for minimum weight of assumptions for {objective}...")
    print(f"Number of Z3 Variables: {len(variables)}")
    optimizer = z3.Optimize()
    optimizer.set("timeout", MAX_MINUTES * 60_000) 
    min_weight = z3.Int('min_weight')
    formula_construct_start = timer()
    assumption_implications = z3.And([z3.Implies(a.variable, a.consequent) for a in assumptions])
    crate_is_safe = z3.Bool(f"{objective}_safe")
    implications_with_neg_conclusion = z3.And(assumption_implications, z3.Not(crate_is_safe))
    UNSAT = z3.Not(exists_bool_expr(variables, implications_with_neg_conclusion))
    CON = exists_bool_expr(variables, assumption_implications)
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
        print(f"Minimum weight of assumptions for {objective}: {model[min_weight]}")
        # for some reason, the time taken is not always recorded in the statistics (it seems to not be recorded when the
        # formula is determined to be satisfiable very quickly)
        z3_solving_time = stats.get_key_value('time') if "time" in stats.keys() else 0
        print(f"Z3 Solving Time: {z3_solving_time} sec") # time taken
        if "conflicts" in stats.keys():
            print(f"Z3 Num Conflicts: {stats.get_key_value('conflicts')}") # approx. number of branches explored by Z3
        elif "sat conflicts" in stats.keys():
            print(f"Z3 Num Conflicts: {stats.get_key_value('sat conflicts')}")
        else:
            print("Z3 Num Conflicts: N/A")
        print("==================================")
        assumptions_made = (a for a in assumptions if model[a.variable] == a.default_assignment())
        print("Assumptions Made:")
        for a in assumptions_made:
            print(f"{a.name}: {a.weight} wt")
        print("==================================")
        min_weight_int: z3.IntNumRef = model[min_weight]
        return min_weight_int.as_long()
    elif result == z3.unsat:
        raise Exception("The Z3 formula is unsatisfiable.") # This should never happen
    else:
        print("The satisfiability of the formula could not be determined.") # Hopefully this never happens
        print(f"Z3 Reason: {optimizer.reason_unknown()}")
        return MAX_WEIGHT

def complete_analysis(crate: CrateVersion):
    """
    Performs a complete analysis for a given crate. Prints results to stdout.
    """
    metadata = crate_data.get_crate_metadata(crate)
    variables, assumptions = assumptions_for(crate, metadata)
    trust_score = get_min_weight(crate, variables, assumptions)
    print(f"Trust Score for {crate}: {trust_score}")

def main():
    parser = argparse.ArgumentParser(description="Perform a complete analysis for a given crate.")
    parser.add_argument("crate_name", type=str, help="The name of the crate to analyze.")
    parser.add_argument("crate_version", type=str, help="The version of the crate to analyze.")
    args = parser.parse_args()
    crate = CrateVersion(args.crate_name, args.crate_version)
    complete_analysis(crate)

if __name__ == "__main__":
    main()
