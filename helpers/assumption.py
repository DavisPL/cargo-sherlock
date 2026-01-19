# This file contains the assumption classes.
from enum import Enum
from typing import NamedTuple
import json
import z3
from helpers.crate_data import CrateVersion
MAX_COST = 100
class Assumption:
    """
    Class representing an assumption that can be made by the solver.
    """
    user_costs: list[dict] | None = None
    def __init__(self, id: int, name: str, consequent: z3.BoolRef, cost: int | None = None):
        self.id = id
        self.name = name
        self.variable = z3.Bool(name)
        self.consequent = consequent
        if cost is not None:
            if cost < 0 or cost > MAX_COST:
                print(f"WARNING: The cost {cost} on {name} is not consistent with the other assumptions.")
            self.cost = cost
            return
        if Assumption.user_costs is None:
            with open('helpers/costs.json', 'r') as f:
                Assumption.user_costs = json.load(f)
        try:
            self.cost = next((x for x in Assumption.user_costs if x.get('id') == id))['cost']
            if self.cost < 0 or self.cost > MAX_COST:
                print(f"WARNING: The cost {self.cost} on {name} is not consistent with the other assumptions.")
        except StopIteration:
            print(f"WARNING: No cost found for assumption {name} with id {id}. Defaulting to MAX_COST.")
            self.cost = MAX_COST
        except Exception as e:
            print(f"WARNING: Error loading cost for assumption {name} with id {id}: {e}. Defaulting to MAX_COST.")
            self.cost = MAX_COST
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

class CrateLabel(Enum):
    """
    Enum representing the labels that can be assigned to a crate.
    """
    SAFE = 0
    LOW_SEVERITY = 1
    MEDIUM_SEVERITY = 2
    HIGH_SEVERITY = 3
    CRITICAL = 4

def combine_costs(positive_cost: int, negative_cost: int) -> CrateLabel:
    """
    Combines the positive and negative costs into a single cost.
    """
    issue_score = MAX_COST - negative_cost
    for i in range(1, 5):
        if positive_cost <= -i/10 * issue_score + 20*i:
            return CrateLabel(i-1)
    return CrateLabel.CRITICAL