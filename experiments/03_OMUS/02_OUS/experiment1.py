# pysat imports
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


def puzzleToExplain(execParams):
    params, puzzleFun, puzzleName = execParams
    params.instance = puzzleName
    o_clauses, o_assumptions, o_weights, o_user_vars, _ = puzzleFun()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params)


def Experiment1Params():
    all_exec_params = []
    timeout = 2 * HOURS
    usr = getpass.getuser()

    # ensure we can write results on HPC
    if usr == "vsc10143":
        resultsFolder = "/data/brussel/101/vsc10143/OUSResults/"
    else:
        resultsFolder = "results/"

    outputFolder = resultsFolder + "experiment1/" + datetime.now().strftime("%Y%m%d%H") + "/"
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
        "p93": frietkot.p93
    }
    params = Experiment1Params()
    p = multiprocessing.Pool(taskspernode)
    puzzleFunc = puzzle_funs[problemName]
    p.map(puzzleFunc, params)


def jobExperiment1():
    """
        \paragraph{RQ1}

            What is the importance of the grow strategy?

        Table:
            [row]: puzzle
            [col]: configuration
            [entry]: Time to first solution + total execution time

        Strategy: Comparison with puzzles to time-to-first solution vs total time
        Experiment 1 cannot use the distinction between initial and actual interpretation.
        In Experiment, also other implementations of grow that are not maxsat based (no grow, SS growing, ... -)
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
        "p93": frietkot.p93
    }
    genPBSjobExperiment1(puzzle_funs, taskspernode=10)


def genPBSjobExperiment1(puzzle_funs, taskspernode):
    hpcDir = "/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments"
    jobName = "Experiment1"

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

#PBS -N {jobName}_{puzzleName}
#PBS -l nodes=1:ppn={taskspernode}:skylake
#PBS -l walltime=04:00:00
#PBS -M emilio.gamba@vub.be
#PBS -m abe

module load Gurobi/9.0.1-GCCcore-9.3.0-Python-3.8.2
module load PySAT/0.1.6.dev11-GCC-9.3.0-Python-3.8.2
module load SciPy-bundle/2020.03-intel-2020a-Python-3.8.2

# own code
cd /user/brussel/101/vsc10143/holygrail/experiments/03_OMUS/02_OUS
python3 experiment1.py {puzzleName} {taskspernode}
"""
        with fpath.open('w+') as f:
            f.write(baseScript)

    # script for submission of the jobs
    allFpaths = [todaysJobPath / f"{jobName}_{puzzleName}.pbs" for puzzleName, _ in puzzle_funs.items()]

    allStrPaths = ['#!/usr/bin/env bash', '']
    allStrPaths += ["qsub "+ str(p).replace('/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments/', '') for p in allFpaths]
    allStrPaths += ['']

    scriptPath = hpcPath / "jobexperiment1.sh"

    with scriptPath.open('w+') as f:
        f.write('\n'.join(allStrPaths))


if __name__ == "__main__":
    if len(sys.argv) == 3:
        problemname = sys.argv[1]
        tasksParallel = int(sys.argv[2])
        runPuzzle(problemname, tasksParallel)
    else:
        jobExperiment1()
