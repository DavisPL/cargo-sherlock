import z3

# Create a solver instance
solver = z3.Solver()

# Define variables
# c and d are the propositional variables in the formula.
c, d = z3.Bools('c d')

# a0, a1, and a2 are the assumptions we are making.
a0, a1, a2 = z3.Bools('a0 a1 a2')

# Define a minimum weight variable to track the minimum weight of the assumptions that make c provable.
min_weight = z3.Int('min_weight')

# Define the formula we are checking for unsatisfiability / provability of C under assumptions a0, a1, and a2
F = z3.And(
    z3.Implies(a0, c),
    z3.Implies(a1, d),
    z3.Implies(a2, z3.Implies(d, c)),
    z3.Not(c)
)

# Define the UNSAT predicate. This checks whether or not the set of assumptions a0, a1, and a2 make the formula F unsatisfiable.
UNSAT = lambda a0, a1, a2: z3.Not(z3.Exists([c, d], F))

# Define the weight function. This function assigns a weight to each assumption based on whether or not it is true.
W = lambda a0, a1, a2: z3.If(a0, 10, 0) + z3.If(a1, 5, 0) + z3.If(a2, 1, 0)

# Add the constraint that the assumptions a0, a1, and a2 make c provable.
solver.add(UNSAT(a0, a1, a2))

# Add the constraint that the weight of the set of assumptions made is equal to the min_weight variable.
solver.add(min_weight == W(a0, a1, a2))

# Add the constraint that for all sets of assumptions that make c provable, the weight of the current set of assumptions 
# is less than or equal to the weight of the other set of assumptions.
minimization_constraint = z3.ForAll([a0, a1, a2], z3.Implies(UNSAT(a0, a1, a2), min_weight <= W(a0, a1, a2)))
solver.add(minimization_constraint)

# Is this needed? (probably not)
solver.add(z3.Implies(a0, c))
solver.add(z3.Implies(a1, d))
solver.add(z3.Implies(a2, z3.Implies(d, c)))

# Check for satisfiability
if solver.check() == z3.sat:
    print("The formula is satisfiable.")
    model = solver.model()
    print("Model:")
    print(model)
else:
    print("The formula is not satisfiable.")