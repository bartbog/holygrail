
import ray
from explain import COusParams, cost_puzzle, cost, explain
from explain import add_assumptions, get_user_vars
from gen_params import *

# Testing samples
from frietkot import simpleProblem, originProblem, frietKotProblem

from pysat.formula import CNF


@ray.remote
def r_frietkotProblem(params):
    params.instance = "frietkot"
    f_cnf, f_user_vars = frietKotProblem()
    f_cnf_ass, assumptions = add_assumptions(f_cnf)
    frietkot_cnf = CNF(from_clauses=f_cnf_ass)
    U = f_user_vars | set(abs(l) for l in assumptions)
    I = set(assumptions)
    f = cost(U, I)
    explain(C=frietkot_cnf, U=U, f=f, I0=I, params=params, verbose=True)


@ray.remote
def r_originProblem(params):
    params.instance = "origin-problem"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = originProblem()

    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


@ray.remote
def r_simpleProblem(params):
    params.instance = "simple"
    s_cnf = simpleProblem()
    s_cnf_ass, assumptions = add_assumptions(s_cnf)
    # transform list cnf into CNF object
    simple_cnf = CNF(from_clauses=s_cnf_ass)
    U = get_user_vars(simple_cnf)
    I = set(assumptions)
    f = cost(U, I)
    explain(C=simple_cnf, U=U, f=f, I0=I, params=params, verbose=False)


def rq1():
    ray.init(address='auto')
    # EXAMPLE 1: write a greeting to stdout
    all_params = effectOfPreseeding()
    futures = [r_originProblem.remote(params) for params in all_params]
    ray.get(futures)


if __name__ == "__main__":
    rq1()
