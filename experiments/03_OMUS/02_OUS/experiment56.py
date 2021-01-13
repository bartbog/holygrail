# pysat imports
from greedy_explain import explainGreedy
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


def puzzleOptExplain(args):
    params, puzzleFun, mode, puzzleName = args
    params.instance = puzzleName
    o_clauses, o_assumptions, o_weights, o_user_vars, _ = puzzleFun()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    if mode == 'greedy':
        explainGreedy(C=o_cnf, U=U, f=f, I0=I, params=params)
    elif mode == 'opt':
        explain(C=o_cnf, U=U, f=f, I0=I, params=params)
    elif mode == 'mus':
        explainMUS(C=o_cnf, U=U, f=f, I0=I, params=params)


def runOptPuzzle(problemName, taskspernode):
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

    puzzleFunc = puzzle_funs[problemName]
    params = [(p, puzzleFunc, problemName) for p in Experiment4Params()]
    p = multiprocessing.Pool(taskspernode)
    p.map(puzzleOptExplain, params)


def jobExperiment56():
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
        "p93": frietkot.p93
    }
    genPBSjobExperiment4(puzzle_funs, taskspernode=40)


def genPBSjobExperiment4(puzzle_funs, taskspernode):
    hpcDir = "/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments"
    jobName = "Experiment4"

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
#PBS -l walltime=24:00:00
#PBS -M emilio.gamba@vub.be
#PBS -m abe

module load Gurobi/9.0.1-GCCcore-9.3.0-Python-3.8.2
module load PySAT/0.1.6.dev11-GCC-9.3.0-Python-3.8.2
module load SciPy-bundle/2020.03-intel-2020a-Python-3.8.2

# own code
cd /user/brussel/101/vsc10143/holygrail/experiments/03_OMUS/02_OUS
python3 experiment4.py {puzzleName} {taskspernode}
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
    # print(len(Experiment4Params()))
    if len(sys.argv) == 3:
        problemname = sys.argv[1]
        tasksParallel = int(sys.argv[2])
        runPuzzle(problemname, tasksParallel)
    else:
        jobExperiment4()
