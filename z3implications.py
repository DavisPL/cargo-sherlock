import z3
import math
import csv
import glob
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

# def weight(
#         assumptions: list[z3.BoolRef], 
#         weights: list[int], 
#         negative_cond: list[z3.BoolRef] = None, 
#         negative_cond_weights: list[int] = None
#     ) -> z3.IntNumRef:
#     """
#     Assigns a weight to a set of assumptions and negative conditions. Weight is incurred 
#     if an assumption is made or if a negative condition is met. The weights of the assumptions
#     are stored in weights, while the weights of the negative conditions are stored in 
#     negative_cond_weights.
#     """
#     if (negative_cond is not None) and (negative_cond_weights is not None):
#         return z3.Sum(
#             z3.Sum([z3.If(a, wt, 0) for a, wt in zip(assumptions, weights)]),
#             z3.Sum([z3.If(neg_cond, neg_wt, 0) for neg_cond, neg_wt in zip(negative_cond, negative_cond_weights)])
#         )
#     else:
#         return z3.Sum([z3.If(a, wt, 0) for a, wt in zip(assumptions, weights)])

# def assumptions_for(passed_audit: bool, num_side_effects: int, downloads: int):
#     # Create a solver instance
#     solver = z3.Solver()
#     c = z3.Bool('c')  # crate is safe
#     d = z3.Bool('d')  # crate has a good enough number of downloads
#     a = z3.BoolVal(passed_audit)  # crate passed audit
#     s = z3.BoolVal(num_side_effects == 0)  # crate has no side effects
#     assumptions = z3.Bools('a0 a1 a2 a3 a4')
#     variables = (c, d)
#     weights = (
#         1700,
#         downloads_weight_function(downloads),
#         170,
#         100,
#         17
#     )
#     min_weight = z3.Int('min_weight')
#     assumption_implications = z3.And(
#         z3.Implies(assumptions[0], c),
#         z3.Implies(assumptions[1], d),
#         z3.Implies(assumptions[2], z3.Implies(d, c)),
#         z3.Implies(assumptions[3], z3.Implies(a, c)),
#         z3.Implies(assumptions[4], z3.Implies(s, c)),
#     )
#     F = z3.And(assumption_implications, z3.Not(c))
#     UNSAT = z3.Not(z3.Exists([c, d], F))
#     solver.add(UNSAT)
#     solver.add(min_weight == weight(assumptions, weights))
#     minimization_constraint = z3.ForAll(assumptions, z3.Implies(UNSAT, min_weight <= weight(assumptions, weights)))
#     solver.add(minimization_constraint)
#     # Check for satisfiability
#     if solver.check() == z3.sat:
#         print("The formula is satisfiable.")
#         model = solver.model()
#         print("Model:")
#         print(model)
#     else:
#         print("The formula is not satisfiable.")

def downloads_weight_function(downloads: int) -> int:
    """
    Assigns a weight to the assumption "the crate has a good enough number of downloads" 
    as a function of the number of downloads the crate actually has.
    """
    return round(1000*math.exp(-downloads/100000))

def github_stats_weight_function(stars: int, forks: int) -> int:
    """
    Assigns a weight to the assumption "the crate has a good enough number of stars and forks on GitHub" 
    as a function of the number of stars and forks the crate actually has.
    """
    return round(1000*math.exp(-stars/10000) + 1000*math.exp(-forks/10000))

class Assumption:
    def __init__(self, name: str, consequent: z3.BoolRef, weight: int):
        self.name = name
        self.variable = z3.Bool(name)
        self.consequent = consequent
        self.weight = weight
    @staticmethod
    def assumptions_weight(assumptions: list['Assumption']) -> z3.ArithRef:
        """
        Returns the total weight of a set of assumptions.
        """
        return z3.Sum([z3.If(a.variable, a.weight, 0) for a in assumptions])

def assumptions_for(crate: str, metadata: dict) -> tuple[list[z3.BoolRef], list[Assumption]]:
    """
    Returns a list of variables and a list of assumptions for a given crate. The first element
    in the returned list of assumptions is what is being proved (i.e. the crate is safe).
    """
    c = z3.Bool(f"{crate}_safe")  # crate is safe
    d = z3.Bool(f"{crate}_high_downloads")  # crate has a 'good enough' number of downloads
    a = z3.BoolVal(metadata["passed_audit"])  # crate passed audit
    s = z3.BoolVal(metadata["num_side_effects"] == 0)  # crate has no side effects
    g = z3.Bool(f"{crate}_high_github_stats")  # crate has a 'good enough' number of stars and forks on GitHub
    return (
        [c, d, g], 
        [
            Assumption("a0_{crate}", c, 1700 + (10000 if metadata["in_rust_sec"] else 0)),
            Assumption("a1_{crate}", d, downloads_weight_function(metadata["downloads"]) + (10000 if metadata["in_rust_sec"] else 0)),
            Assumption("a2_{crate}", z3.Implies(d, c), 170 + (10000 if metadata["in_rust_sec"] else 0)),
            Assumption("a3_{crate}", z3.Implies(a, c), 100 + (10000 if metadata["in_rust_sec"] else 0)),
            Assumption("a4_{crate}", z3.Implies(s, c), 17 + (10000 if metadata["in_rust_sec"] else 0)),
            Assumption("a5_{crate}", g, github_stats_weight_function(metadata["stars"], metadata["forks"]) + (10000 if metadata["in_rust_sec"] else 0)),
            Assumption("a6_{crate}", z3.Implies(g, c), 11 + (10000 if metadata["in_rust_sec"] else 0))
        ]
    )


def solve_assumptions(variables: list[z3.BoolRef], assumptions: list[Assumption]):
    """
    Finds the minimum weight of a set of assumptions that prove the crate is safe. This function
    requires that the first element in variables is the variable representing the crate being safe
    (i.e. the variable being proven).
    """
    solver = z3.Solver()
    min_weight = z3.Int('min_weight')
    assumption_implications = z3.And([z3.Implies(a.variable, a.consequent) for a in assumptions])
    F = z3.And(assumption_implications, z3.Not(variables[0]))
    UNSAT = z3.Not(z3.Exists(variables, F))
    solver.add(UNSAT)
    solver.add(min_weight == Assumption.assumptions_weight(assumptions))
    minimization_constraint = z3.ForAll(
        [a.variable for a in assumptions], 
        z3.Implies(UNSAT, min_weight <= Assumption.assumptions_weight(assumptions))
    )
    solver.add(minimization_constraint)
    # Check for satisfiability
    if solver.check() == z3.sat:
        print("The formula is satisfiable.")
        model = solver.model()
        print("Model:")
        print(model)
    else:
        print("The formula is not satisfiable.")

def main():
    result = parser()
    first_crate = result[0]
    # for i in first_crate:
    #    print(*i)
    # print(dict(*first_crate[3])['downloads']) # downloads
    downloads = int(dict(*first_crate[3])['downloads'])
    # print(dict(*first_crate[0])) # RustSec
    # print(first_crate[1] is not None) # Has a passed audit
    passed_audit = first_crate[1] is not None
    variables, assumptions = assumptions_for("anyhow", {
        "passed_audit": passed_audit,
        "num_side_effects": 0,
        "downloads": downloads,
        "in_rust_sec": False,
        "stars": 1000000000,
        "forks": 1000000000
    })
    # assumptions_for(passed_audit, 0, downloads)
    solve_assumptions(variables, assumptions)

if __name__ == "__main__":
    main()
