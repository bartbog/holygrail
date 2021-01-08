import sys
sys.path.append('/data/brussel/101/vsc10143/miniconda3/envs/ousExp37/lib/python3.7/site-packages')
import itertools

import getpass

from explain import COusParams
from datetime import datetime
from explain import HOURS, MINUTES, SECONDS


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


def effectOfPostPoningOpt():
    all_exec_params = []

    return all_exec_params


def effectOfGrow():
    all_exec_params = []

    return all_exec_params


def effectOfPreseeding():
    all_exec_params = []
    timeout = 2 * HOURS
    usr = getpass.getuser()

    # ensure we can write results on HPC
    if usr == "vsc10143":
        resultsFolder = "/data/brussel/101/vsc10143/OUSResults/"
    else:
        resultsFolder = "results/"

    outputFolder = resultsFolder + "effectPreseeding/" + datetime.now().strftime("%Y%m%d%H") + "/"

    # preseeding
    preseedPerms = [False, True]

    # polarity sat solver
    satPolPerms = [[False] * 2] + list(itertools.permutations([True, False]))

    # postponing optimisation
    postOptPers = [
        [False, False, False],
        [True, False, True],
        [True, True, False],
        [True, True, True]
    ]

    # maxsat Perms
    maxsatPerms = []
    for p in itertools.permutations([True] + [False] * 8):
        if list(p) not in maxsatPerms:
            maxsatPerms.append(list(p))

    polmaxsatPerms = []
    for tf in [True, False]:
        for p in maxsatPerms:
            polmaxsatPerms.append([tf] + p)

    # grow procedure
    perms = [[False] * 5] # no grow

    # at least one grow/sat/subsetmax/subsetI0/maxsat
    for p in itertools.permutations([True] + [False] * 3):
        l = [True] + list(p)
        if l not in perms:
            perms.append(l)

    growPerms = []
    for perm in perms:
        # if maxsat we add all different permutations possible
        if perm[-1]:
            for m in polmaxsatPerms:
                growPerms.append({
                    "grow": list(perm),
                    "maxsat": m
                })
        else:
            growPerms.append({
                "grow": perm,
                "maxsat": [False] * 10
            })

    print("preseedPerms=", len(preseedPerms))
    print("satPolPerms=", len(satPolPerms))
    print("postOptPers=", len(postOptPers))
    print("growPerm=", len(growPerms))

    for pre_seeding in preseedPerms:
        for polarity, polarity_initial in satPolPerms:
            for postpone_opt, postpone_opt_incr, postpone_opt_greedy in postOptPers:
                for growPerm in growPerms:
                    g_grow, g_sat, g_subsetmax, g_subsetI0, g_maxsat = growPerm["grow"]
                    maxsatPolarities, m_full_pos, m_full_inv, m_full_unif, m_initial_inv, m_initial_unif, m_initial_pos, m_actual_pos, m_actual_inv, m_actual_unif = growPerm["maxsat"]
                    # Parameters
                    params = COusParams()
                    # intialisation: pre-seeding
                    params.pre_seeding = pre_seeding

                    # hitting set computation
                    params.postpone_opt = postpone_opt
                    params.postpone_opt_incr = postpone_opt_incr
                    params.postpone_opt_greedy = postpone_opt_greedy

                    # polarity of sat solver
                    params.polarity = polarity
                    params.polarity_initial = polarity_initial

                    # sat - grow
                    params.grow = g_grow
                    params.grow_sat = g_sat
                    params.grow_subset_maximal = g_subsetmax
                    params.subset_maximal_I0 = g_subsetI0
                    params.grow_maxsat = g_maxsat

                    # MAXSAT growing
                    params.maxsat_polarities = maxsatPolarities

                    # MAXSAT growing
                    #type of grow
                    params.grow_maxsat_full_pos = m_full_pos
                    params.grow_maxsat_full_inv = m_full_inv
                    params.grow_maxsat_full_unif = m_full_unif
                    params.grow_maxsat_initial_inv = m_initial_inv
                    params.grow_maxsat_initial_unif = m_initial_unif
                    params.grow_maxsat_initial_pos = m_initial_pos
                    params.grow_maxsat_actual_pos = m_actual_pos
                    params.grow_maxsat_actual_inv = m_actual_inv
                    params.grow_maxsat_actual_unif = m_actual_unif

                    # timeout
                    params.timeout = timeout

                    # output
                    params.output_folder = outputFolder

                    # instance
                    params.instance = "unnamed"
                    params.checkParams()

                    all_exec_params.append(params)

    return all_exec_params

if __name__ == "__main__":
    print("running checks")
    print(len(effectOfPreseeding()))