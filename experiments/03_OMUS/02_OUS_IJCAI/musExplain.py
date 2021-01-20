from bestStep import BestStepMUSComputer
from explain import add_assumptions, cost, cost_puzzle, get_user_vars, optimalPropagate
import itertools
import time
import json
from pathlib import Path
# import random
from itertools import chain, combinations
import signal

from datetime import datetime

# pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
from pysat.examples.musx import MUSX


# Testing samples
from frietkot import originProblem, simpleProblem, frietKotProblem


def print_expl(matching_table, Ibest):
    if matching_table is None:
        return

    for i in Ibest:
        if(i in matching_table['Transitivity constraint']):
            print("trans", i)
        elif(i in matching_table['Bijectivity']):
            print("bij", i)
        elif(i in matching_table['clues']):
            print("clues n°", matching_table['clues'][i])
        else:
            print("Fact:", i)



def explainMUS(C: CNF, U: set, f, I0: set, ExplSeq=None):
    """
    ExplainCSP uses hard clauses supplied in CNF format to explain user
    variables with associated weights users_vars_cost based on the
    initial interpretation.

    => hyp: cost is linear

    Args:

        cnf (list): CNF C over a vocabulary V.

        U (set): User vocabulary U subset of V.

        f (list): f is a mapping of user vars to real cost.

        I0 (list): Initial interpretation subset of U.
    """
    # check literals of I are all user vocabulary
    assert all(True if abs(lit) in U else False for lit in I0), f"Part of supplied literals not in U (user variables): {lits for lit in I if lit not in U}"

    # Initialise the sat solver with the cnf
    sat = Solver(bootstrap_with=C.clauses)
    assert sat.solve(assumptions=I0), f"CNF is unsatisfiable with given assumptions {I}."

    # Explanation sequence
    E = []

    # Most precise intersection of all models of C project on U, not including the constraints.
    Iend = optimalPropagate(U=U, I=I0, sat=sat) - I0

    # print(Iend)
    c = BestStepMUSComputer(f=f, cnf=C, sat=sat, U=U, Iend=Iend, I=I0)

    I = set()
    C = set(I0) # copy

    while(len(Iend - I) > 0):
        timedout = False
        costExpl = 0
        # Compute optimal explanation explanation assignment to subset of U.
        costExpl, (Ei, Ci) = c.naive_min_explanation(I, C)

        # facts used
        Ibest = I & Ei
        Cbest = C & Ci

        # New information derived "focused" on
        Nbest = optimalPropagate(U=U, I=Ibest | Cbest, sat=sat) - (I|C)
        assert len(Nbest - Iend) == 0

        E.append({
            "constraints": list(Ibest | Cbest),
            "derived": list(Nbest),
            "cost": costExpl
        })

        print(f"\nOptimal explanation \t\t {Ibest} /\ {Cbest} => {Nbest}\n")


    sat.delete()
    return E


def frietkotMUS():
    f_cnf, f_user_vars = frietKotProblem()
    f_cnf_ass, assumptions = add_assumptions(f_cnf)

    # transform list cnf into CNF object
    frietkot_cnf = CNF(from_clauses=f_cnf_ass)
    U = f_user_vars | set(abs(l) for l in assumptions)
    I = set(assumptions)
    f = cost(U, I)
    explainMUS(C=frietkot_cnf, U=U, f=f, I0=I)


def simpleMUS():
    s_cnf = simpleProblem()
    s_cnf_ass, assumptions = add_assumptions(s_cnf)
    # transform list cnf into CNF object
    simple_cnf = CNF(from_clauses=s_cnf_ass)
    U = get_user_vars(simple_cnf)
    I = set(assumptions)
    f = cost(U, I)
    explainMUS(C=simple_cnf, U=U, f=f, I0=I)


def puzzleMUS():
    o_clauses, o_assumptions, o_weights, o_user_vars, _ = originProblem()

    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explainMUS(C=o_cnf, U=U, f=f, I0=I)

if __name__ == "__main__":
    # Translating the explanation sequence generated to website visualisation
    # Execution parameters
    simpleMUS()
    frietkotMUS()