from explain import COusParams, MINUTES, cost_puzzle, cost, explain, add_assumptions, get_user_vars, runParallel, runPool
from explain import HOURS
from multiprocessing import Process, Pool
from datetime import datetime

# Testing samples
from frietkot import simpleProblem, originProblem, frietKotProblem
from pysat.formula import CNF

import itertools


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


def rq1_params():

    # checking the effect on preseeding with grow
    TF = [True, False]
    all_params_test = []

    pre_grow_perms = []
    for c in [list(per) for per in itertools.permutations([True, False, False])]:
        if c not in pre_grow_perms:
            pre_grow_perms.append(c)
    grow_perms = []
    for c in [[True] + list(per) for per in itertools.permutations([True, False, False])] + [[False] * 4]:
        if c not in grow_perms:
            grow_perms.append(c)

    grow_maxsat_perms = []
    for c in [list(per) for per in itertools.permutations([True, False, False, False])]:
        if c not in grow_maxsat_perms:
            grow_maxsat_perms.append(c)

    for pre_grow, pre_subset, pre_maxsat in pre_grow_perms:
        for postopt, post_opt_greedy in itertools.product(TF, repeat=2):
            for grow, grow_sat, grow_subset, grow_maxsat in grow_perms:
                grow_maxsat_neg_cost, grow_maxsat_pos_cost, grow_maxsat_max_cost_neg, grow_maxsat_unit = False, False, False, False
                if grow_maxsat:
                    for grow_maxsat_neg_cost, grow_maxsat_pos_cost, grow_maxsat_max_cost_neg, grow_maxsat_unit in grow_maxsat_perms:
                        p = COusParams()

                        # polarity
                        p.polarity = True

                        # pre-seeding
                        p.pre_seeding = True
                        p.pre_seeding_grow = pre_subset
                        p.pre_seeding_subset_minimal = pre_grow
                        p.pre_seeding_grow_maxsat = pre_maxsat

                        # hitting set computation
                        p.postpone_opt = (postopt or post_opt_greedy)
                        p.postpone_opt_incr = postopt
                        p.postpone_opt_greedy = post_opt_greedy

                        # grow
                        p.grow = grow
                        p.grow_sat = grow_sat
                        p.grow_subset_maximal = grow_subset
                        p.grow_maxsat = grow_maxsat


                        p.grow_maxsat_neg_cost = grow_maxsat_neg_cost
                        p.grow_maxsat_pos_cost = grow_maxsat_pos_cost
                        p.grow_maxsat_max_cost_neg = grow_maxsat_max_cost_neg
                        p.grow_maxsat_unit = grow_maxsat_unit

                        p.timeout = 4 * HOURS
                        p.output_folder = "results/rq1_4/" + datetime.now().strftime("%Y%m%d/")
                        all_params_test.append(p)
                else:
                    p = COusParams()

                    # polarity
                    p.polarity = True

                    # pre-seeding
                    p.pre_seeding = True
                    p.pre_seeding_grow = pre_subset
                    p.pre_seeding_subset_minimal = pre_grow
                    p.pre_seeding_grow_maxsat = pre_maxsat

                    # hitting set computation
                    p.postpone_opt = (postopt or post_opt_greedy)
                    p.postpone_opt_incr = postopt
                    p.postpone_opt_greedy = post_opt_greedy

                    # grow
                    p.grow = grow
                    p.grow_sat = grow_sat
                    p.grow_subset_maximal = grow_subset
                    p.grow_maxsat = grow_maxsat


                    p.grow_maxsat_neg_cost = grow_maxsat_neg_cost
                    p.grow_maxsat_pos_cost = grow_maxsat_pos_cost
                    p.grow_maxsat_max_cost_neg = grow_maxsat_max_cost_neg
                    p.grow_maxsat_unit = grow_maxsat_unit

                    p.timeout = 4 * HOURS
                    p.output_folder = "results/rq1_4/" + datetime.now().strftime("%Y%m%d/")
                    all_params_test.append(p)

    return all_params_test


def rq2_params():
    pass


def rq1():
    all_params = rq1_params()
    all_funs = [r_simpleProblem, r_frietkotProblem, r_originProblem]
    print(len(all_params) * len(all_funs))
    runPool(all_funs, all_params)


def rq2():
    all_params = rq2_params()
    # all_funs = [r_simpleProblem, r_frietkotProblem, r_originProblem]
    # runParallel(all_funs, all_params)

if __name__ == "__main__":
    rq1()