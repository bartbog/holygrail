# pysat imports
from greedy_explain import OusParams, explainGreedy
import itertools
import multiprocessing
from pathlib import Path

from datetime import datetime
import getpass

import sys
# puzzle problems import
import frietkot

# pysat imports
from pysat.formula import CNF

# explanations import
from explain import COusParams, OUSTimeoutError, cost_puzzle, explain

SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES
TIMEOUT_EXP1 = 1 * HOURS


def puzzleToExplain(args):
    params, puzzleFun, puzzleName = args
    params.instance = puzzleName
    o_clauses, o_assumptions, o_weights, o_user_vars, _ = puzzleFun()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explainGreedy(C=o_cnf, U=U, f=f, I0=I, params=params)


def Experiment6GreedyParams():
    all_exec_params = []
    timeout = 2 * HOURS
    usr = getpass.getuser()

    # ensure we can write results on HPC
    if usr == "vsc10143":
        resultsFolder = "/data/brussel/101/vsc10143/OUSResults/"
    else:
        resultsFolder = "results/"

    outputFolder = resultsFolder + "experiment6_greedy/" + datetime.now().strftime("%Y%m%d%H") + "/"

    reuse_SSes = [True, False]
    sort_literals = [True, False]

    pre_seeding_perms = [False, True]

    postponeOpt_perms = [
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

    # at least one subsetmax/maxsat
    perms = [list(l) for l in itertools.permutations([True] + [False])]

    growPerms = []
    for perm in perms:
        # if maxsat we add all different permutations possible
        if perm[-1]:
            for m in maxsatPerms:
                growPerms.append({
                    "grow": list(perm),
                    "maxsat": m
                })
        else:
            growPerms.append({
                "grow": perm,
                "maxsat": [False] * 9
            })

    for reuse_ss in reuse_SSes:
        for sort_lits in sort_literals:
            for pre_seeding in pre_seeding_perms:
                for growPerm in growPerms:
                    g_subsetmax, g_maxsat = growPerm["grow"]
                    m_full_pos, m_full_inv, m_full_unif, m_initial_pos, m_initial_inv, m_initial_unif, m_actual_pos, m_actual_unif, m_actual_inv = growPerm["maxsat"]
                    if any([m_full_pos, m_full_inv, m_full_unif]):
                        continue
                    params = OusParams()

                    # intialisation: pre-seeding
                    params.reuse_SSes = reuse_ss
                    params.sort_literals = sort_lits

                    params.pre_seeding = pre_seeding

                    # hitting set computation
                    params.postpone_opt = False
                    params.postpone_opt_incr = False
                    params.postpone_opt_greedy = False

                    # MAXSAT growing
                    params.maxsat_polarities = True

                    # sat - grow
                    params.grow = True
                    params.grow_subset_maximal = g_subsetmax
                    params.grow_maxsat = g_maxsat

                    # MAXSAT growing
                    params.grow_maxsat_full_pos = m_full_pos
                    params.grow_maxsat_full_inv = m_full_inv
                    params.grow_maxsat_full_unif = m_full_unif
                    params.grow_maxsat_initial_pos = m_initial_pos
                    params.grow_maxsat_initial_inv = m_initial_inv
                    params.grow_maxsat_initial_unif = m_initial_unif
                    params.grow_maxsat_actual_pos = m_actual_pos
                    params.grow_maxsat_actual_unif = m_actual_unif
                    params.grow_maxsat_actual_inv = m_actual_inv
                    # timeout
                    params.timeout = timeout

                    # output
                    params.output_folder = outputFolder

                    # instance
                    params.instance = "unnamed"
                    params.checkParams()

                    all_exec_params.append(params)
    return all_exec_params


def runPuzzle(problemName, taskspernode):
    puzzle_funs = {
        "origin-problem": frietkot.originProblem,
        "pastaPuzzle": frietkot.pastaPuzzle,
        "p12": frietkot.p12,
        "p13": frietkot.p13,
        "p16": frietkot.p16,
        "p18": frietkot.p18,
        "p25": frietkot.p25,
        "p20": frietkot.p20,
        "p93": frietkot.p93,
        "p19": frietkot.p19
    }

    puzzleFunc = puzzle_funs[problemName]
    params = [(p, puzzleFunc, problemName) for p in Experiment6GreedyParams()]
    p = multiprocessing.Pool(taskspernode)
    p.map(puzzleToExplain, params)


def jobExperiment6greedy():
    """
        \paragraph{RQ3}
        Comparing the efficiency of explanation specific grows!

        Table:
            [row]: puzzle
            [col]: configuration
            [entry]: Time to first solution + total execution time

        Strategy:
        - Select the best not maxat strategy
        - Select the 2 best maxsat strategy from RQ1
        - Use I/I0 with maxsat unif/pos/maxneg cost
    """
    puzzle_funs = {
        "origin-problem": frietkot.originProblem,
        "pastaPuzzle": frietkot.pastaPuzzle,
        "p12": frietkot.p12,
        "p13": frietkot.p13,
        "p16": frietkot.p16,
        "p18": frietkot.p18,
        "p25": frietkot.p25,
        "p20": frietkot.p20,
        "p93": frietkot.p93,
        "p19": frietkot.p19,
    }
    genPBSjobExperiment6greedy(puzzle_funs, taskspernode=10)


def genPBSjobExperiment6greedy(puzzle_funs, taskspernode):
    hpcDir = "/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments"
    jobName = "experiment6_greedy"

    # creating the appropriate directories
    hpcPath = Path(hpcDir)
    jobPath = hpcPath / "jobs/"
    if not jobPath.exists():
        jobPath.mkdir()
    today = datetime.now().strftime("%Y%m%d%H") + "/"
    todaysJobPath = jobPath / today
    if not todaysJobPath.exists():
        todaysJobPath.mkdir()

    # generating the jobs
    for puzzleName, _ in puzzle_funs.items():
        fpath = todaysJobPath / f"{jobName}_{puzzleName}.pbs"
        baseScript = f"""#!/usr/bin/env bash

#PBS -N job_results/{jobName}_{puzzleName}
#PBS -l nodes=1:ppn={taskspernode}:skylake
#PBS -l walltime=16:00:00
#PBS -M emilio.gamba@vub.be
#PBS -m abe

module load Gurobi/9.0.1-GCCcore-9.3.0-Python-3.8.2
module load PySAT/0.1.6.dev11-GCC-9.3.0-Python-3.8.2
module load SciPy-bundle/2020.03-intel-2020a-Python-3.8.2

# own code
cd /data/brussel/101/vsc10143/holygrail/experiments/03_OMUS/02_OUS
python3 experiment6_greedy.py {puzzleName} {taskspernode}
"""
        with fpath.open('w+') as f:
            f.write(baseScript)

    # script for submission of the jobs
    allFpaths = [todaysJobPath / f"{jobName}_{puzzleName}.pbs" for puzzleName, _ in puzzle_funs.items()]

    allStrPaths = ['#!/usr/bin/env bash', '']
    allStrPaths += ["qsub "+ str(p).replace('/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments/', '') for p in allFpaths]
    allStrPaths += ['']

    scriptPath = hpcPath / f"job{jobName}.sh"

    with scriptPath.open('w+') as f:
        f.write('\n'.join(allStrPaths))


if __name__ == "__main__":
    print(len(Experiment6GreedyParams()))
    if len(sys.argv) == 3:
        problemname = sys.argv[1]
        tasksParallel = int(sys.argv[2])
        runPuzzle(problemname, tasksParallel)
    else:
        jobExperiment6greedy()
