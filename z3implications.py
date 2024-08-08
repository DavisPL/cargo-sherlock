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

def downloads_weight_function(downloads):
    return round(1000*math.exp(-downloads/100000))

def weight(*args, weights):
    return z3.Sum([z3.If(arg, weight, 0) for arg, weight in zip(args, weights)])

def assumptions_for(passed_audit: bool, num_side_effects: int, downloads: int):
    c = z3.Bool('c') # crate is safe
    d = z3.Bool('d') # crate has a good enough number of downloads
    a = z3.BoolVal(passed_audit) # crate passed audit
    s = z3.BoolVal(num_side_effects == 0) # number of side effects in the crate
    a0, a1, a2, a3, a4 = z3.Bools('a0 a1 a2 a3 a4')
    assumptions = (a0, a1, a2, a3, a4)
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
        z3.Implies(a0, c),
        z3.Implies(a1, d),
        z3.Implies(a2, z3.Implies(d, c)),
        z3.Implies(a3, z3.Implies(a, c)),
        z3.Implies(a4, z3.Implies(s, c)),
    )
    F = z3.And(assumption_implications, z3.Not(c))
    UNSAT = z3.Not(z3.Exists([c, d], F))
    solver.add(UNSAT)
    print(weights)
    solver.add(min_weight == weight(*assumptions, weights = weights))
    minimization_constraint = z3.ForAll(assumptions, z3.Implies(UNSAT, min_weight <= weight(*assumptions, weights = weights)))
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
    #for i in first_crate:
    #    print(*i)
    # print(dict(*first_crate[3])['downloads']) # downloads
    downloads = int(dict(*first_crate[3])['downloads'])
    # print(dict(*first_crate[0])) # RustSec
    print(first_crate[1] is not None) # Has a passed audit
    passed_audit = first_crate[1] is not None
    assumptions_for(passed_audit, 0, downloads)

main()