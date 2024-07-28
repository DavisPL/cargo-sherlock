import z3

# Create a solver instance
solver = z3.Solver()

# Define variables
d, a, s, r = z3.Bools('d a s r')
a0, a1, a2, a3, a4, a5 = z3.Bools('a0 a1 a2 a3 a4 a5')
assumptions = (a0, a1, a2, a3, a4, a5)
weights = (4, 2, 1, 3, 5, 10)
min_weight = z3.Int('min_weight')

# Define the formula we are checking for unsatisfiability / provability of r
assumption_implications = z3.And(
    z3.Implies(a0, d),
    z3.Implies(a1, z3.Implies(d, r)),
    z3.Implies(a2, z3.Implies(z3.And(a, s), r)),
    z3.Implies(a3, a),
    z3.Implies(a4, s),
    z3.Implies(a5, r),
)
F = z3.And(assumption_implications, z3.Not(r))

# Define UNSAT and Weight functions
UNSAT = z3.Not(z3.Exists([d, a, s, r], F))
def Weight(*args, weights = None):
    if weights is not None:
        return z3.Sum([z3.If(arg, weight, 0) for arg, weight in zip(args, weights)])
    else:
        return z3.Sum([z3.If(arg, 1, 0) for arg in args])

solver.add(UNSAT)
solver.add(min_weight == Weight(*assumptions, weights))
minimization_constraint = z3.ForAll(assumptions, z3.Implies(UNSAT, min_weight <= Weight(*assumptions, weights)))
solver.add(minimization_constraint)

# Check for satisfiability
if solver.check() == z3.sat:
    print("The formula is satisfiable.")
    model = solver.model()
    print("Model:")
    print(model)
else:
    print("The formula is not satisfiable.")