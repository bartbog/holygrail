import sys
sys.path.append('/data/brussel/101/vsc10143/miniconda3/envs/ousExp37/lib/python3.7/site-packages')
import itertools

# import ray
from explain import COusParams, cost_puzzle, cost, explain
from explain import add_assumptions, get_user_vars
from explain import runParallel
from explain import HOURS, MINUTES, SECONDS
from multiprocessing import Process, Pool
from datetime import datetime

# Testing samples
from frietkot import simpleProblem, originProblem, frietKotProblem

from pysat.formula import CNF


# @ray.remote
def r_frietkotProblem(params):
    params.instance = "frietkot"
    f_cnf, f_user_vars = frietKotProblem()
    f_cnf_ass, assumptions = add_assumptions(f_cnf)
    frietkot_cnf = CNF(from_clauses=f_cnf_ass)
    U = f_user_vars | set(abs(l) for l in assumptions)
    I = set(assumptions)
    f = cost(U, I)
    explain(C=frietkot_cnf, U=U, f=f, I0=I, params=params, verbose=True)


# @ray.remote
def r_originProblem(params):
    params.instance = "origin-problem"
    o_clauses, o_assumptions, o_weights, o_user_vars, _ = originProblem()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, verbose=False)


# @ray.remote
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


def rq1_maxsat_grow():
    all_exec_params = []
    polarity = True
    preseeding = True
    preseeding_grow = True

    # grow
    grow = True
    grow_maxsat = True

    grow_maxsat_perms = []
    for c in [list(per) for per in itertools.permutations([True, False, False, False])]:
        if c not in grow_maxsat_perms:
            grow_maxsat_perms.append(c)

    postponeOpt_perms = [
        [False, False, False],
        [True, False, True],
        [True, True, False],
        [True, True, True]
    ]

    for postOpt, postIncr, postGreedy in postponeOpt_perms:
        for neg_cost, pos_cost, max_cost_neg, unit in grow_maxsat_perms:
            p = COusParams()

            # intialisation: pre-seeding
            p.pre_seeding = preseeding
            p.pre_seeding_grow = preseeding_grow

            # hitting set computation
            p.postpone_opt = postOpt
            p.postpone_opt_incr = postIncr
            p.postpone_opt_greedy = postGreedy

            # polarity of sat solver
            p.polarity = polarity

            # sat - grow
            p.grow = grow
            p.grow_maxsat = grow_maxsat

            p.grow_maxsat_neg_cost = neg_cost
            p.grow_maxsat_pos_cost = pos_cost
            p.grow_maxsat_max_cost_neg = max_cost_neg
            p.grow_maxsat_unit = unit

            # timeout
            p.timeout = 2 * HOURS

            p.output_folder = "/user/brussel/101/vsc10143/holygrail/experiments/03_OMUS/02_OUS/results/maxsat/" + datetime.now().strftime("%Y%m%d%H") + "/"
            all_exec_params.append(p)

    runParallel([r_originProblem], all_exec_params)


def rq1_all_params():
    # checking the effect on preseeding with grow
    polarity = True
    preseeding = True
    preseedingGrow = True
    TF = [True, False]
    all_params_test = []

    # pre_grow_perms = []
    # for c in [list(per) for per in itertools.permutations([True, False])]:
    #     if c not in pre_grow_perms:
    #         pre_grow_perms.append(c)

    grow_perms = []
    for c in [[True] + list(per) for per in itertools.permutations([True, False, False])] + [[False] * 4]:
        if c not in grow_perms:
            grow_perms.append(c)

    grow_maxsat_perms = []
    for c in [list(per) for per in itertools.permutations([True, False, False, False])]:
        if c not in grow_maxsat_perms:
            grow_maxsat_perms.append(c)

    postponeOpt_perms = [
        [False, False, False],
        [True, False, True],
        [True, True, False],
        [True, True, True]
    ]

    for postopt, postponeIncr, postponeGreedy in postponeOpt_perms:
        for grow, growSat, growSubset, growMaxsat in grow_perms:
            if growMaxsat:
                for maxsatNegCost, maxsatPosCost, maxsatMaxNegCost, maxsatUnit in grow_maxsat_perms:
                    p = COusParams()

                    # polarity
                    p.polarity = polarity

                    # pre-seeding
                    p.pre_seeding = preseeding
                    p.pre_seeding_grow = preseedingGrow

                    # hitting set computation
                    p.postpone_opt = postopt
                    p.postpone_opt_incr = postponeIncr
                    p.postpone_opt_greedy = postponeGreedy

                    # grow
                    p.grow = grow
                    p.grow_sat = growSat
                    p.grow_subset_maximal = growSubset
                    p.grow_maxsat = growMaxsat

                    p.grow_maxsat_neg_cost = maxsatNegCost
                    p.grow_maxsat_pos_cost = maxsatPosCost
                    p.grow_maxsat_max_cost_neg = maxsatMaxNegCost
                    p.grow_maxsat_unit = maxsatUnit

                    p.timeout = 4 * HOURS
                    p.output_folder = "/user/brussel/101/vsc10143/holygrail/experiments/03_OMUS/02_OUS/results/rq1_6/" + datetime.now().strftime("%Y%m%d%H") + "/"
                    all_params_test.append(p)
            else:
                p = COusParams()

                # polarity
                p.polarity = polarity

                # pre-seeding
                p.pre_seeding = preseeding
                p.pre_seeding_grow = preseedingGrow

                # hitting set computation
                p.postpone_opt = postopt
                p.postpone_opt_incr = postponeIncr
                p.postpone_opt_greedy = postponeGreedy

                # grow
                p.grow = grow
                p.grow_sat = growSat
                p.grow_subset_maximal = growSubset
                p.grow_maxsat = growMaxsat

                p.grow_maxsat_neg_cost = False
                p.grow_maxsat_pos_cost = False
                p.grow_maxsat_max_cost_neg = False
                p.grow_maxsat_unit = False

                p.timeout = 4 * HOURS
                p.output_folder = "/user/brussel/101/vsc10143/holygrail/experiments/03_OMUS/02_OUS/results/rq1_6/" + datetime.now().strftime("%Y%m%d%H") + "/"
                all_params_test.append(p)

    return all_params_test


def rq2_params():
    pass

# def rq1():
#     ray.init(address='auto')
#     # EXAMPLE 1: write a greeting to stdout
#     all_params = rq1_all_params()
#     futures = [r_originProblem.remote(params) for params in all_params]
#     ray.get(futures)


def rq1_args(func, num_node, cores_per_node):
    offset = (num_node-1)*cores_per_node
    params = rq1_all_params()[offset:]
    runParallel([func], params)


if __name__ == "__main__":
    if len(sys.argv) == 3:
        rq1_args(r_originProblem, int(sys.argv[1]), int(sys.argv[2]))
    else:
        print ('Number of arguments:', len(sys.argv), 'arguments.')
        print ('Argument List:', str(sys.argv))
        print(len(rq1_all_params()))