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


# Create a solver instance
solver = z3.Solver()

def downloads_weight_function(downloads: int) -> int:
    """
    Assigns a weight to the assumption "the crate has a good enough number of downloads" 
    as a function of the number of downloads the crate actually has.
    """
    return round(1000*math.exp(-downloads/100000))

def weight(
        assumptions: list[z3.BoolRef], 
        weights: list[int], 
        negative_cond: list[z3.BoolRef] = None, 
        negative_cond_weights: list[int] = None
    ) -> z3.IntNumRef:
    """
    Assigns a weight to a set of assumptions and negative conditions. Weight is incurred 
    if an assumption is made or if a negative condition is met. The weights of the assumptions
    are stored in weights, while the weights of the negative conditions are stored in 
    negative_cond_weights.
    """
    if (negative_cond is not None) and (negative_cond_weights is not None):
        return z3.Sum(
            z3.Sum([z3.If(a, wt, 0) for a, wt in zip(assumptions, weights)]),
            z3.Sum([z3.If(neg_cond, neg_wt, 0) for neg_cond, neg_wt in zip(negative_cond, negative_cond_weights)])
        )
    else:
        return z3.Sum([z3.If(a, wt, 0) for a, wt in zip(assumptions, weights)])

def assumptions_for(passed_audit: bool, num_side_effects: int, downloads: int):
    c = z3.Bool('c')  # crate is safe
    d = z3.Bool('d')  # crate has a good enough number of downloads
    a = z3.BoolVal(passed_audit)  # crate passed audit
    s = z3.BoolVal(num_side_effects == 0)  # crate has no side effects
    assumptions = z3.Bools('a0 a1 a2 a3 a4')
    variables = (c, d)
    weights = (
        1700,
        downloads_weight_function(downloads),
        170,
        100,
        17
    )
    min_weight = z3.Int('min_weight')
    assumption_implications = z3.And(
        z3.Implies(assumptions[0], c),
        z3.Implies(assumptions[1], d),
        z3.Implies(assumptions[2], z3.Implies(d, c)),
        z3.Implies(assumptions[3], z3.Implies(a, c)),
        z3.Implies(assumptions[4], z3.Implies(s, c)),
    )
    F = z3.And(assumption_implications, z3.Not(c))
    UNSAT = z3.Not(z3.Exists([c, d], F))
    solver.add(UNSAT)
    solver.add(min_weight == weight(assumptions, weights))
    minimization_constraint = z3.ForAll(assumptions, z3.Implies(UNSAT, min_weight <= weight(assumptions, weights)))
    solver.add(minimization_constraint)
    # Check for satisfiability
    if solver.check() == z3.sat:
        print("The formula is satisfiable.")
        model = solver.model()
        print("Model:")
        print(model)
    else:
        print("The formula is not satisfiable.")

class Assumption:
    def __init__(self, name: str, weight: int, consequent: z3.BoolRef):
        self.name = name
        self.weight = weight
        self.consequent = consequent
        self.variable = z3.Bool(name)
    
def assumptions_for_single(crate: str, metadata: dict) -> list[Assumption]:
    c = z3.Bool('c')  # crate is safe
    d = z3.Bool('d')  # crate has a 'good enough' number of downloads
    a = z3.BoolVal(metadata["passed_audit"])  # crate passed audit
    s = z3.BoolVal(metadata["num_side_effects"] == 0)  # crate has no side effects
    return [
        Assumption("a0", 1700, c),
        Assumption("a1", downloads_weight_function(metadata["downloads"]), d),
        Assumption("a2", 170, z3.Implies(d, c)),
        Assumption("a3", 100, z3.Implies(a, c)),
        Assumption("a4", 17, z3.Implies(s, c))
    ]


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
    assumptions_for(passed_audit, 0, downloads)


main()
