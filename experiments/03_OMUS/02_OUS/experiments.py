from gen_params import effectOfPreseeding
import sys
import random
import time
from datetime import date, datetime
from pathlib import Path
from math import ceil

# pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

# omus imports
sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
sys.path.append('/home/emilio/Documents/cppy_src/')
sys.path.append('/home/emilio/documents/cppy_mysrc/')

from multiprocessing import Process

SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES
TIMEOUT_EXP1 = 1 * HOURS


def runParallel(fn, args):
    procs = []
    for arg in args:
        p = Process(target=fn, args=(arg,))
        p.start()
        procs.append(p)

    for p in procs:
        p.join()


def genPBSjobs(hpcDir, jobName, nodes, taskspernode):
    jobName = "effectOfPreseeding"

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
    for i in range(nodes):
        fpath = todaysJobPath / f"{jobName}_{i}.pbs"
        startpos = i * taskspernode
        baseScript = f"""#!/usr/bin/env bash

#PBS -N {jobName}
#PBS -l nodes=1:ppn={taskspernode}:skylake
#PBS -l walltime=04:00:00
#PBS -M emilio.gamba@vub.be
#PBS -m abe

module load Gurobi/9.0.1-GCCcore-8.3.0-Python-3.7.4

# own code
conda init bash
source .bashrc
conda activate ousExp37
cd /user/brussel/101/vsc10143/holygrail/experiments/03_OMUS/02_OUS
python3 experiment_rq1.py {startpos} {taskspernode}
"""
        with fpath.open('w+') as f:
            f.write(baseScript)

    # script for submission of the jobs
    allFpaths = [todaysJobPath / f"{jobName}_{i}.pbs" for i in range(nodes)]

    allStrPaths = ['#!/usr/bin/env bash', '']
    allStrPaths += ["qsub "+ str(p).replace('/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments/', '') for p in allFpaths]
    allStrPaths += ['']

    scriptPath = hpcPath / "launchJobs.sh"

    with scriptPath.open('w+') as f:
        f.write('\n'.join(allStrPaths))


def jobEffectOfPreseeding():
    jobName = "EffectOfpreseeding"
    hpcOutputFolder = "/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments"
    params = effectOfPreseeding()
    taskspernode = 40
    nodes = ceil(len(params)/taskspernode)
    print(nodes, taskspernode)
    genPBSjobs(hpcOutputFolder, jobName, nodes, taskspernode)

if __name__ == "__main__":
    jobEffectOfPreseeding()