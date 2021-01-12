import multiprocessing

from explain import COusParams, cost_puzzle, cost, explain
from explain import add_assumptions, get_user_vars
from explain import runParallel

from gen_params import *

# Testing samples
from frietkot import simpleProblem, originProblem, frietKotProblem

from pysat.formula import CNF


def r_frietkotProblem(params):
    params.instance = "frietkot"
    f_cnf, f_user_vars = frietKotProblem()
    f_cnf_ass, assumptions = add_assumptions(f_cnf)
    frietkot_cnf = CNF(from_clauses=f_cnf_ass)
    U = f_user_vars | set(abs(l) for l in assumptions)
    I = set(assumptions)
    f = cost(U, I)
    explain(C=frietkot_cnf, U=U, f=f, I0=I, params=params, verbose=True)


def r_originProblem(params):
    params.instance = "origin-problem"
    o_clauses, o_assumptions, o_weights, o_user_vars, _ = originProblem()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, verbose=False)


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


def rq1_args_pool(func, start, taskspernode, maxTaskspernode):
    params = effectOfPreseeding()[start:start+taskspernode * maxTaskspernode]
    p = multiprocessing.Pool(taskspernode)
    p.map(func, params)


def rq1_args(func, start, numTasks):
    params = effectOfPreseeding()[start:start+numTasks]
    runParallel([func], params)


if __name__ == "__main__":
    if len(sys.argv) == 3:
        rq1_args(r_originProblem, int(sys.argv[1]), int(sys.argv[2]))
    elif len(sys.argv) == 4:
        rq1_args_pool(r_originProblem, int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
    else:
        print ('Number of arguments:', len(sys.argv), 'arguments.')
        print ('Argument List:', str(sys.argv))
        print(len(effectOfPreseeding()))