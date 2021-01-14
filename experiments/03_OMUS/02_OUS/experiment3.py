# pysat imports
import itertools
from pysat.formula import CNF, WCNF
from pysat.examples.musx import MUSX

from datetime import datetime
import getpass

import ray

# puzzle problems import
import frietkot

# explanations import
from explain import COusParams, OUSTimeoutError, cost_puzzle, explain

SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES
TIMEOUT_EXP1 = 1 * HOURS


def Experiment3():
    all_exec_params = []
    timeout = 2 * HOURS
    usr = getpass.getuser()

    # ensure we can write results on HPC
    if usr == "vsc10143":
        resultsFolder = "/data/brussel/101/vsc10143/OUSResults/"
    else:
        resultsFolder = "results/"

    outputFolder = resultsFolder + "experiment3/" + datetime.now().strftime("%Y%m%d%H") + "/"
    # maxsat Perms
    maxsatPerms = []
    for p in itertools.permutations([True] + [False] * 2):
        if list(p) not in maxsatPerms:
            maxsatPerms.append(list(p))

    polmaxsatPerms = []
    for tf in [True, False]:
        for p in maxsatPerms:
            polmaxsatPerms.append([tf] + p)

    # grow procedure grow/sat/subsetmax/maxsat
    perms = [[False] * 4] # no grow

    # at least one grow/sat/subsetmax/maxsat
    for p in itertools.permutations([True] + [False] * 2):
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
                "maxsat": [False] * 4
            })
    for p in growPerms:
        print(p)


    for growPerm in growPerms:

        assert len(growPerm["grow"]) == 4, f"Grow parameter: got {len(growPerm['grow'])} expected 4"
        assert len(growPerm["maxsat"]) == 4, f"maxsat parameter: got {len(growPerm['maxsat'])} expected 4"

        params = COusParams()
        g_grow, g_sat, g_subsetmax, g_maxsat = growPerm["grow"]
        maxsatPolarities, m_full_pos, m_full_inv, m_full_unif = growPerm["maxsat"]

        # poarlarity can be used
        params.polarity = True

        # grow strategies
        params.grow = g_grow
        params.grow_sat = g_sat
        params.grow_subset_maximal = g_subsetmax
        params.grow_maxsat = g_maxsat

        params.maxsat_polarities = maxsatPolarities

        params.grow_maxsat_full_inv = m_full_pos
        params.grow_maxsat_full_pos = m_full_inv
        params.grow_maxsat_full_unif = m_full_unif

        # timeout
        params.timeout = timeout

        # output
        params.output_folder = outputFolder

        # instance
        params.instance = "unnamed"
        params.checkParams()

        all_exec_params.append(params)
    return all_exec_params


def jobExperiment3():
    """
        \paragraph{RQ2}
        Select MUS instances and use the OUS call to check performance of the solver.

        Strategy:

        - Comparison with the SMUS solver
        - Unit costs for a configuration

    """
    

if __name__ == "__main__":
    jobExperiment1()
