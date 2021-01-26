from utils import get_user_vars
from explain import test_puzzle
from bestStep import BestStepOUSComputer, optimalPropagate
from params import OusParams
from cost import cost, cost_puzzle
# pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

# Testing samples
from frietkot import *


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

def explainGreedy(C: CNF, U: set, f, I0: set, params: OusParams, verbose=False, matching_table=None):
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
    params.checkParams()

    if verbose:
        print("Expl:")
        print("\tcnf:", len(C.clauses), C.nv)
        print("\tU:", len(U))
        print("\tf:", f)
        print("\tI0:", len(I0))

    # check literals of I are all user vocabulary
    assert all(True if abs(lit) in U else False for lit in I0), f"Part of supplied literals not in U (user variables): {lits for lit in I if lit not in U}"

    # Initialise the sat solver with the cnf
    sat = Solver(bootstrap_with=C.clauses)
    assert sat.solve(assumptions=I0), f"CNF is unsatisfiable with given assumptions {I}."

    # Explanation sequence
    E = []

    # Most precise intersection of all models of C project on U
    Iend = optimalPropagate(U=U, I=I0, sat=sat)

    c = BestStepOUSComputer(f=f, cnf=C, sat=sat, Iend=Iend, I=I0, params=params)
    # only handling timeout error!
    I = set(I0) # copy
    while(len(Iend - I) > 0):
        expl = c.bestStep(f, Iend, I)

        Ibest = I & expl

        # New information derived "focused" on
        Nbest = optimalPropagate(U=U, I=Ibest, sat=sat) - I
        assert len(Nbest - Iend) == 0

        E.append({
            "constraints": list(Ibest),
            "derived": list(Nbest)
        })

        if verbose:
            print_expl(matching_table, Ibest)
            print(f"\nOptimal explanation \t\t {Ibest} => {Nbest}\n")

        I |= Nbest

    try: 
        c.optHSComputer.dispose()
        c.__del__()
    except:
        print("disposing not working")

    sat.delete()
    if verbose:
        print(E)
    return E


def frietkotGreedy(params):
    f_cnf, f_user_vars = frietKotProblem()
    f_cnf_ass, assumptions = add_assumptions(f_cnf)

    # transform list cnf into CNF object
    frietkot_cnf = CNF(from_clauses=f_cnf_ass)
    U = f_user_vars | set(abs(l) for l in assumptions)
    I = set(assumptions)
    f = cost(U, I)
    explainGreedy(C=frietkot_cnf, U=U, f=f, I0=I, params=params, verbose=True)


def simpleGreedy(params):
    s_cnf = simpleProblem()
    s_cnf_ass, assumptions = add_assumptions(s_cnf)
    # transform list cnf into CNF object
    simple_cnf = CNF(from_clauses=s_cnf_ass)
    U = get_user_vars(simple_cnf)
    I = set(assumptions)
    f = cost(U, I)
    explainGreedy(C=simple_cnf, U=U, f=f, I0=I, params=params, verbose=True)


def puzzleGreedy(params):
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = originProblem()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = test_puzzle(U, I, o_weights)
    explainGreedy(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


if __name__ == "__main__":
    # Translating the explanation sequence generated to website visualisation
    # Execution parameters
    params = OusParams()
    params.polarity = True
    params.reuse_SSes = True
    params.sort_literals = True

    params.grow = True
    params.grow_maxsat = True
    params.grow_maxsat_actual_unif = True

    # INSTANCES
    simpleGreedy(params)
    frietkotGreedy(params)
