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


def ExperimentReRunParams():
    timeout = 2 * HOURS
    usr = getpass.getuser()

    # ensure we can write results on HPC
    if usr == "vsc10143":
        resultsFolder = "/data/brussel/101/vsc10143/OUSResults/"
    else:
        resultsFolder = "results/"

    outputFolder = resultsFolder + "experiment6_rerun/" + datetime.now().strftime("%Y%m%d%H") + "/"

    params = COusParams()

    # intialisation: pre-seeding
    params.pre_seeding = False

    # hitting set computation
    params.postpone_opt = False
    params.postpone_opt_incr = False
    params.postpone_opt_greedy = False

    # MAXSAT growing
    params.maxsat_polarities = True

    # sat - grow
    params.grow = True
    params.grow_subset_maximal = False
    params.grow_maxsat = True

    # MAXSAT growing
    params.grow_maxsat_full_pos = False
    params.grow_maxsat_full_inv = False
    params.grow_maxsat_full_unif = False
    params.grow_maxsat_initial_pos = False
    params.grow_maxsat_initial_inv = False
    params.grow_maxsat_initial_unif = False
    params.grow_maxsat_actual_pos = False
    params.grow_maxsat_actual_unif = True
    params.grow_maxsat_actual_inv = False
    # timeout
    params.timeout = timeout

    # output
    params.output_folder = outputFolder

    # instance
    params.instance = "unnamed"
    params.checkParams()

    return params


def genPBSjobexperiment_ReRun():
    hpcDir = "/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments"
    jobName = "experiment_ReRun"

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

#PBS -N job_results/{jobName}
#PBS -l nodes=1:ppn=1:skylake
#PBS -l walltime=03:00:00
#PBS -M emilio.gamba@vub.be
#PBS -m abe

module load Gurobi/9.0.1-GCCcore-9.3.0-Python-3.8.2
module load PySAT/0.1.6.dev11-GCC-9.3.0-Python-3.8.2
module load SciPy-bundle/2020.03-intel-2020a-Python-3.8.2

# own code
cd /data/brussel/101/vsc10143/holygrail/experiments/03_OMUS/02_OUS
python3 experiment_small.py
"""
    with fpath.open('w+') as f:
        f.write(baseScript)

    # script for submission of the jobs
    allFpaths = [todaysJobPath / f"{jobName}.pbs"]

    allStrPaths = ['#!/usr/bin/env bash', '']
    allStrPaths += ["qsub " + str(p).replace('/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments/', '') for p in allFpaths]
    allStrPaths += ['']

    scriptPath = hpcPath / f"job{jobName}.sh"

    with scriptPath.open('w+') as f:
        f.write('\n'.join(allStrPaths))


if __name__ == "__main__":
    genPBSjobexperiment_ReRun()
    # puzzle_funs = {
    #     "origin-problem": frietkot.originProblem,
    #     "pastaPuzzle": frietkot.pastaPuzzle,
    #     "p12": frietkot.p12,
    #     "p13": frietkot.p13,
    #     "p16": frietkot.p16,
    #     "p18": frietkot.p18,
    #     "p25": frietkot.p25,
    #     "p20": frietkot.p20,
    #     "p93": frietkot.p93,
    #     "p19": frietkot.p19,
    # }
    # params = ExperimentReRunParams()
    # args = (params, frietkot.pastaPuzzle, 'pastaPuzzle')
    # puzzleToExplain(args)
