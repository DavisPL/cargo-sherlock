# This file contains the assumption classes.
from typing import NamedTuple
import z3
from helpers.crate_data import CrateVersion

class Assumption:
    """
    Class representing an assumption that can be made by the solver.
    """
    def __init__(self, id: int, crate: CrateVersion, consequent: z3.BoolRef, weight: int):
        """
        Creates an assumption with the given id for the given crate. The assumption is that the consequent is true, 
        and the weight is the weight of the assumption.
        """
        self.id = id
        self.crate = crate
        self.variable = z3.Bool(f"a{id}_{crate}")
        self.consequent = consequent
        self.weight = weight
    def __repr__(self) -> str:
        return f"Assumption({self.id}, {self.crate}, {self.consequent}, {self.weight})"
    def __str__(self) -> str:
        match self.id:
            case 0:
                return f"{self.crate} is safe: {self.weight} wt"
            case 1:
                return f"{self.crate} has many downloads: {self.weight} wt"
            case 2:
                return f"{self.crate} having many downloads implies it is safe: {self.weight} wt"
            case 3:
                return f"{self.crate} having a passed audit implies it is safe: {self.weight} wt"
            case 4:
                return f"{self.crate} has many stars and forks: {self.weight} wt"
            case 5:
                return f"{self.crate} having many stars and forks implies it is safe: {self.weight} wt"
            case 6:
                return f"{self.crate} has all safe dependencies: {self.weight} wt"
            case 7:
                return f"{self.crate} having no side effects and having all safe dependencies implies it is safe: {self.weight} wt"
            case _:
                return Assumption.__repr__(self)
    def __eq__(self, other) -> bool:
        if isinstance(other, Assumption):
            return self.id == other.id and self.crate == other.crate and self.consequent == other.consequent and self.weight == other.weight
        return NotImplemented
    def __hash__(self) -> int:
        return hash((self.id, self.crate, self.consequent, self.weight))
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

class NegativeAssumption(Assumption):
    """
    Class representing a negative assumption that can be made by the solver. A negative assumption is an assumption
    that incurs weight if it is set to false.
    """
    def __repr__(self) -> str:
        return f"Negative{super().__repr__()}"
    def __str__(self) -> str:
        match self.id:
            case 8:
                return f"{self.crate} appearing in RustSec implies it is less safe (score penalty): {self.weight} weight"
            case _:
                return super().__str__(self)
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