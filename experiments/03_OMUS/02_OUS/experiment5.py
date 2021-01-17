# pysat imports
from musExplain import MUSParams, explainMUS
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
from pysat.examples.hitman import Hitman

# explanations import
from explain import COusParams, OUSTimeoutError, cost_puzzle, explain

SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES
TIMEOUT_EXP1 = 1 * HOURS


def Experiment5Params():
    timeout = 2 * HOURS
    usr = getpass.getuser()

    # ensure we can write results on HPC
    if usr == "vsc10143":
        resultsFolder = "/data/brussel/101/vsc10143/OUSResults/"
    else:
        resultsFolder = "results/"

    outputFolder = resultsFolder + "experiment5/" + datetime.now().strftime("%Y%m%d%H") + "/"
    param = MUSParams()
    param.output_folder = outputFolder
    param.timeout = timeout

    return param


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


def runMUSPuzzle(taskspernode):
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
    musParam = Experiment5Params()
    params = []
    for puzzleName, puzzleFunc in puzzle_funs.items():
        params.append((musParam, puzzleFunc, 'mus', puzzleName))

    p = multiprocessing.Pool(taskspernode)
    p.map(puzzleOptExplain, params)


def jobExperiment5():
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
    genPBSjobExperiment5(taskspernode=10)


def genPBSjobExperiment5(taskspernode):
    hpcDir = "/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments"
    jobName = "Experiment5"

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
    fpath = todaysJobPath / f"{jobName}.pbs"
    baseScript = f"""#!/usr/bin/env bash

#PBS -N {jobName}
#PBS -l nodes=1:ppn={taskspernode}:skylake
#PBS -l walltime=24:00:00
#PBS -M emilio.gamba@vub.be
#PBS -m abe

module load Gurobi/9.0.1-GCCcore-9.3.0-Python-3.8.2
module load PySAT/0.1.6.dev11-GCC-9.3.0-Python-3.8.2
module load SciPy-bundle/2020.03-intel-2020a-Python-3.8.2

# own code
cd /data/brussel/101/vsc10143/holygrail/experiments/03_OMUS/02_OUS
python3 experiment5.py {taskspernode}
"""
    with fpath.open('w+') as f:
        f.write(baseScript)

    # script for submission of the jobs
    allFpaths = [todaysJobPath / f"{jobName}.pbs"]

    allStrPaths = ['#!/usr/bin/env bash', '']
    allStrPaths += ["qsub "+ str(p).replace('/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments/', '') for p in allFpaths]
    allStrPaths += ['']

    scriptPath = hpcPath / f"job{jobName}.sh"

    with scriptPath.open('w+') as f:
        f.write('\n'.join(allStrPaths))


if __name__ == "__main__":
    # print(len(Experiment4Params()))
    if len(sys.argv) == 2:
        tasksParallel = int(sys.argv[1])
        print(tasksParallel)
        runMUSPuzzle(tasksParallel)
    else:
        jobExperiment5()
