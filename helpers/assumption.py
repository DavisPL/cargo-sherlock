# This file contains the assumption classes.
from typing import NamedTuple
import z3
from helpers.crate_data import CrateVersion
from helpers.costs import MAX_COST
class Assumption:
    """
    Class representing an assumption that can be made by the solver.
    """
    def __init__(self, name: str, consequent: z3.BoolRef, cost: int):
        self.name = name
        self.variable = z3.Bool(name)
        self.consequent = consequent
        self.cost = cost
    def __repr__(self) -> str:
        return f"Assumption({self.name}, {self.consequent}, {self.cost})"
    def __str__(self) -> str:
        return f"{self.name}: {self.cost} cost"
    def __eq__(self, other) -> bool:
        if isinstance(other, Assumption):
            return self.name == other.name and self.consequent == other.consequent and self.cost == other.cost
        return NotImplemented
    def __hash__(self) -> int:
        return hash((self.name, self.consequent, self.cost))
    def default_assignment(self) -> z3.BoolRef:
        """
        Returns the default assignment of the assumption. This is true for
        positive assumptions.
        """
        return z3.BoolVal(True)
    def single_assumption_cost(self) -> z3.ArithRef:
        """
        Returns the cost of a single assumption. Cost is incurred if the assumption is set to true.
        """
        return z3.If(self.variable, self.cost, 0)
    @staticmethod
    def assumptions_cost(assumptions: list['Assumption']) -> z3.ArithRef:
        """
        Returns the total cost of a set of assumptions.
        """
        return z3.Sum([a.single_assumption_cost() for a in assumptions])
    @staticmethod
    def cost_consistency_check(assumptions: list['Assumption']):
        """
        Conducts a consistency check on the costs for a list of assumptions. Prints a warning message to 
        stdout if costs are found to be inconsistent.
        """
        for assumption in assumptions:
            if assumption.cost > MAX_COST or assumption.cost < 0:
                print(f"WARNING: The cost {assumption.cost} on {assumption.name} is not consistent with the other assumptions.")

class CrateAssumptionSummary(NamedTuple):
    """
    Tuple containing the name of a crate and the assumptions that have been made about it.
    """
    crate: CrateVersion
    assumptions_made: list[Assumption]