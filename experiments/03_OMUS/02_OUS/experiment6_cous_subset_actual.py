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


def puzzleToExplainGreedy(args):
    params, puzzleFun, puzzleName = args
    params.instance = puzzleName
    o_clauses, o_assumptions, o_weights, o_user_vars, _ = puzzleFun()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explainGreedy(C=o_cnf, U=U, f=f, I0=I, params=params)


def puzzleToExplain(args):
    params, puzzleFun, puzzleName = args
    params.instance = puzzleName
    o_clauses, o_assumptions, o_weights, o_user_vars, _ = puzzleFun()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params)


def Experiment6cOUSParams():
    timeout = 2 * HOURS
    usr = getpass.getuser()

    # ensure we can write results on HPC
    if usr == "vsc10143":
        resultsFolder = "/data/brussel/101/vsc10143/OUSResults/"
    else:
        resultsFolder = "results/"

    outputFolder = resultsFolder + "experiment6_subset_actual/" + datetime.now().strftime("%Y%m%d%H") + "/"

    params = COusParams()

    params.disableConstrained = False

    # intialisation: pre-seeding
    params.pre_seeding = False

    # hitting set computation
    params.postpone_opt = False
    params.postpone_opt_incr = False
    params.postpone_opt_greedy = False

    # polarity of sat solver
    params.polarity = True


    # grow strategies
    params.grow = True
    params.grow_subset_maximal_actual = True

    # timeout
    params.timeout = timeout

    # output
    params.output_folder = outputFolder

    # instance
    params.instance = "unnamed"
    params.checkParams()

    return params


def Experiment6cOUSnonIncrParams():
    timeout = 2 * HOURS
    usr = getpass.getuser()

    # ensure we can write results on HPC
    if usr == "vsc10143":
        resultsFolder = "/data/brussel/101/vsc10143/OUSResults/"
    else:
        resultsFolder = "results/"

    outputFolder = resultsFolder + "experiment6_subset_actual_nonincr/" + datetime.now().strftime("%Y%m%d%H") + "/"

    params = COusParams()

    params.disableConstrained = True

    # intialisation: pre-seeding
    params.pre_seeding = False

    # hitting set computation
    params.postpone_opt = False
    params.postpone_opt_incr = False
    params.postpone_opt_greedy = False

    # polarity of sat solver
    params.polarity = True


    # grow strategies
    params.grow = True
    params.grow_subset_maximal_actual = True

    # timeout
    params.timeout = timeout

    # output
    params.output_folder = outputFolder

    # instance
    params.instance = "unnamed"
    params.checkParams()

    return params


def Experiment6GreedyNotIncrParams():
    timeout = 2 * HOURS
    usr = getpass.getuser()

    # ensure we can write results on HPC
    if usr == "vsc10143":
        resultsFolder = "/data/brussel/101/vsc10143/OUSResults/"
    else:
        resultsFolder = "results/"

    outputFolder = resultsFolder + "experiment6_greedy_subset_actual_nonincr/" + datetime.now().strftime("%Y%m%d%H") + "/"

    params = OusParams()

    # intialisation: pre-seeding
    params.reuse_SSes = False
    params.sort_literals = False

    params.pre_seeding = False

    # hitting set computation

    # sat - grow
    params.grow = True
    params.grow_subset_maximal_actual = True
    params.polarity = True

    # MAXSAT growing
    # timeout
    params.timeout = timeout

    # output
    params.output_folder = outputFolder

    # instance
    params.instance = "unnamed"
    params.checkParams()

    return params


def Experiment6GreedyParams():
    all_exec_params = []
    timeout = 2 * HOURS
    usr = getpass.getuser()

    # ensure we can write results on HPC
    if usr == "vsc10143":
        resultsFolder = "/data/brussel/101/vsc10143/OUSResults/"
    else:
        resultsFolder = "results/"

    outputFolder = resultsFolder + "experiment6_greedy_subset_actual/" + datetime.now().strftime("%Y%m%d%H") + "/"
    params = OusParams()

    # intialisation: pre-seeding
    params.reuse_SSes = True
    params.sort_literals = True

    params.pre_seeding = False

    # sat - grow
    params.grow = True
    params.grow_subset_maximal_actual = True
    params.polarity = True

    # MAXSAT growing
    # timeout
    params.timeout = timeout

    # output
    params.output_folder = outputFolder

    # instance
    params.instance = "unnamed"
    params.checkParams()

    return params


def runPuzzle(taskspernode):
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

    params = [(Experiment6cOUSParams(), puzzleFunc, problemName) for problemName, puzzleFunc in puzzle_funs.items()]
    p = multiprocessing.Pool(taskspernode)
    p.map(puzzleToExplain, params)


def runPuzzleWithSelected(taskspernode, i):
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

    puzzleExplainFuncs = {
        0: puzzleToExplain,
        1: puzzleToExplain,
        2: puzzleToExplainGreedy,
        3: puzzleToExplainGreedy
    }

    explainParams = {
        0: Experiment6cOUSParams,
        1: Experiment6cOUSnonIncrParams,
        2: Experiment6GreedyParams,
        3: Experiment6GreedyNotIncrParams
    }

    params = [(explainParams[i](), puzzleFunc, problemName) for problemName, puzzleFunc in puzzle_funs.items()]
    p = multiprocessing.Pool(taskspernode)
    p.map(puzzleExplainFuncs[i], params)


def jobExperiment6cOUS():
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
        "p19": frietkot.p19
    }
    genPBSjobExperiment6cOUS(puzzle_funs, taskspernode=10)


def genPBSjobExperiment6cOUS(puzzle_funs, taskspernode):
    hpcDir = "/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments"
    jobName = "experiment6_subset_actual"

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
    for i in range(1, 4):
        fpath = todaysJobPath / f"{jobName}_{i}.pbs"
        baseScript = f"""#!/usr/bin/env bash

#PBS -N {jobName}
#PBS -l nodes=1:ppn={taskspernode}:skylake
#PBS -l walltime=04:00:00
#PBS -M emilio.gamba@vub.be
#PBS -m abe

module load Gurobi/9.0.1-GCCcore-9.3.0-Python-3.8.2
module load PySAT/0.1.6.dev11-GCC-9.3.0-Python-3.8.2
module load SciPy-bundle/2020.03-intel-2020a-Python-3.8.2

# own code
cd /data/brussel/101/vsc10143/holygrail/experiments/03_OMUS/02_OUS
python3 experiment6_cous_subset_actual.py {taskspernode} {i}
"""
        with fpath.open('w+') as f:
            f.write(baseScript)

    # script for submission of the jobs
    allFpaths = [todaysJobPath / f"{jobName}_{i}.pbs" for i in range(1, 4)]

    allStrPaths = ['#!/usr/bin/env bash', '']
    allStrPaths += ["qsub "+ str(p).replace('/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments/', '') for p in allFpaths ]
    allStrPaths += ['']

    scriptPath = hpcPath / f"job{jobName}.sh"

    with scriptPath.open('w+') as f:
        f.write('\n'.join(allStrPaths))


if __name__ == "__main__":
    if len(sys.argv) == 2:
        tasksParallel = int(sys.argv[1])
        runPuzzle(tasksParallel)
    elif len(sys.argv) == 3:
        tasksParallel = int(sys.argv[1])
        paramType = int(sys.argv[2])
        runPuzzleWithSelected(tasksParallel, paramType)
    else:
        jobExperiment6cOUS()
