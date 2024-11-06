# This file contains the assumption classes.
from typing import NamedTuple
import z3
from helpers.crate_data import CrateVersion
MAX_WEIGHT = 500

class Assumption:
    """
    Class representing an assumption that can be made by the solver.
    """
    def __init__(self, name: str, consequent: z3.BoolRef, weight: int):
        self.name = name
        self.variable = z3.Bool(name)
        self.consequent = consequent
        self.weight = weight
    def __repr__(self) -> str:
        return f"Assumption({self.name}, {self.consequent}, {self.weight})"
    def __str__(self) -> str:
        return f"{self.name}: {self.weight} wt"
    def __eq__(self, other) -> bool:
        if isinstance(other, Assumption):
            return self.name == other.name and self.consequent == other.consequent and self.weight == other.weight
        return NotImplemented
    def __hash__(self) -> int:
        return hash((self.name, self.consequent, self.weight))
    def default_assignment(self) -> z3.BoolRef:
        """
        Returns the default assignment of the negative assumption. This is true for
        positive assumptions.
        """
        return z3.BoolVal(True)
    def single_assumption_weight(self) -> z3.ArithRef:
        """
        Returns the weight of a single assumption. Weight is incurred if the assumption is set to true.
        """
        return z3.If(self.variable, self.weight, 0)
    @staticmethod
    def assumptions_weight(assumptions: list['Assumption']) -> z3.ArithRef:
        """
        Returns the total weight of a set of assumptions.
        """
        return z3.Sum([a.single_assumption_weight() for a in assumptions])
    @staticmethod
    def weight_consistency_check(assumptions: list['Assumption']):
        """
        Conducts a consistency check on the weights for a list of assumptions. Prints a warning message to 
        stdout if weights are found to be inconsistent.
        """
        for assumption in assumptions:
            if assumption.weight > MAX_WEIGHT or assumption.weight < 0:
                print(f"WARNING: The weight {assumption.weight} on {assumption.name} is not consistent with the other assumptions.")
        

class NegativeAssumption(Assumption):
    """
    Class representing a negative assumption that can be made by the solver. A negative assumption is an assumption
    that incurs weight if it is set to false.
    """
    def __repr__(self) -> str:
        return f"Negative{super().__repr__()}"
    def default_assignment(self) -> z3.BoolRef:
        """
        Returns the default assignment of the negative assumption. This is false for
        negative assumptions.
        """
        return z3.BoolVal(False)
    def single_assumption_weight(self) -> z3.ArithRef:
        """
        Returns the weight of a single negative assumption. Weight is incurred if the assumption is 
        set to false.
        """
        return z3.If(self.variable, 0, self.weight)

class CrateAssumptionSummary(NamedTuple):
    """
    Tuple containing the name of a crate and the assumptions that have been made about it.
    """
    crate: CrateVersion
    assumptions_made: list[Assumption]