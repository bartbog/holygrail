import itertools
import multiprocessing
import sys
from datetime import datetime
from pathlib import Path
from math import ceil
import signal
import shutil
import getpass
import ray

# pysat imports
from pysat.formula import CNF, WCNF
from pysat.examples.musx import MUSX

# puzzle problems import
import frietkot

# explanations import
from explain import COusParams, OUSTimeoutError, cost_puzzle, explain, timeoutHandler

# parameter testing imports
from gen_params import effectOfPreseeding

# cppy imports

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


def getMUSFiles(benchmarkDir, fileList):
    fileListPath = Path(benchmarkDir + fileList)
    allMUSfiles = []
    with fileListPath.open('r') as f:
        allMUSfiles = list(map(lambda fileName: fileName.replace('\n', '')[2:], f.readlines()))

    return allMUSfiles


def extractMUS(wcnf):
    with MUSX(wcnf) as m:
        mus = m.compute()
        return False if mus is None else True


def selectMUSFiles():
    """
        Select only cnfs where MUS extractor finds the MUS in less than 10 seconds.
        Because finding the SMUS or finding the OUS is more difficult than extracting a MUS.
    """
    # initialising the timeouthandler
    _ = signal.signal(signal.SIGALRM, timeoutHandler)

    # benchmark
    benchmarkDir = "/home/crunchmonster/Documents/VUB/01_SharedProjects/03_benchmarksOUS/"
    fileList = "file_list.txt"
    targetFolder = "data/mus_instances/"

    # sorting files on increasing file size
    MUSFiles = getMUSFiles(benchmarkDir, fileList)
    MUSPaths = list(map(lambda f: Path(benchmarkDir + f), MUSFiles))
    MUSPaths.sort(key=lambda f: f.stat().st_size)

    MUSExtractable = []

    # checking all files and copying them to target folder
    for f in MUSPaths:
        extractedMUS = False
        cnf = CNF(from_file=f)
        clauses = cnf.clauses
        wcnf = WCNF()
        wcnf.extend(clauses, [1] * len(clauses))
        signal.alarm(11)
        try:
            extractedMUS = extractMUS(wcnf)
        except OUSTimeoutError:
            extractedMUS = False
        finally:
            signal.alarm(0)

        print(extractedMUS, f)
        if extractedMUS:
            shutil.copy(f, targetFolder + f.name)

    return MUSExtractable


def genPBSjobs(hpcDir, jobName, nodes, taskspernode, maxTaskspernode):
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
        startpos = i * taskspernode * maxTaskspernode
        baseScript = f"""#!/usr/bin/env bash

#PBS -N {jobName}
#PBS -l nodes=1:ppn={taskspernode}:skylake
#PBS -l walltime=24:00:00
#PBS -M emilio.gamba@vub.be
#PBS -m abe

module load Gurobi/9.0.1-GCCcore-9.3.0-Python-3.8.2
module load PySAT/0.1.6.dev11-GCC-9.3.0-Python-3.8.2

# own code
cd /user/brussel/101/vsc10143/holygrail/experiments/03_OMUS/02_OUS
python3 experiment_rq1.py {startpos} {taskspernode} {maxTaskspernode}
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




def jobExperiment4():
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
    pass


def jobExperiment56():
    """
        \paragraph{RQ4}

        How does the explanation strategy compare between optimal and non-optimal explanation generation?

        Strategy:
        - Greedy explain reuse SSes (incremental)
        - Greedy explain not reuse SSes (non-incremental)
        - cOUS explain
        - MUS extraction for explanation generation
    """
    pass


def jobEffectOfPreseeding():
    jobName = "EffectOfpreseeding"
    hpcOutputFolder = "/home/crunchmonster/Documents/VUB/01_SharedProjects/03_hpc_experiments"
    params = effectOfPreseeding()
    taskspernode = 40
    maxTaskspernode = 6
    nodes = ceil(len(params)/(taskspernode * maxTaskspernode))
    print(nodes, taskspernode, maxTaskspernode)
    genPBSjobs(hpcOutputFolder, jobName, nodes, taskspernode, maxTaskspernode)

if __name__ == "__main__":
    # jobEffectOfPreseeding()
    print(len(Experiment1Params()))
    # selectMUSFiles()