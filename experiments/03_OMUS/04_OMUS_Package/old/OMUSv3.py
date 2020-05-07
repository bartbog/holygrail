#!/usr/bin/env python
# coding: utf-8

# standard libraries
from enum import Enum
from collections import Counter
from datetime import datetime

# pysat library
from pysat.solvers import Solver, SolverNames
from pysat.formula import CNF, WCNF
from pysat.examples.rc2 import RC2, RC2Stratified

# gurobi library
import gurobipy as gp
from gurobipy import GRB

# or-tools library
from ortools.linear_solver import pywraplp
from OMUS_utils import *

# configs
import pprint


class OMUS_EXTENSION(Enum):
    DEFAULT = 0
    UNIT_PROPAGATION = 1
    EXTENSIVE_PROPAGATION = 2
    GREEDY = 3
    MAXSAT = 4

class OMUS_SOLVER(Enum):
    OR_TOOLS = 0
    GUROBI = 1

# utilities
class OMUS(object):
    def __init__(self, clauses = [], f = clause_length, f_ext = None, extension = OMUS_EXTENSION.GREEDY, solver= OMUS_SOLVER.GUROBI):
        pass


    @staticmethod
    def clause_length(clause):
        return len(clause)
def main():
    print("mu main")

if __name__ == "__main__":
    main()
