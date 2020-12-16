import sys
import random
import time
from datetime import date, datetime
from pathlib import Path

# pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

# omus imports
sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
sys.path.append('/home/emilio/Documents/cppy_src/')
sys.path.append('/home/emilio/documents/cppy_mysrc/')

from multiprocessing import Process

from frietkot import simpleProblem
from explain import add_assumptions, get_user_vars, explain

SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES
TIMEOUT_EXP1 = 1 * HOURS


def runParallel(fn, args):
    procs = []
    for fn in fns:
        for arg in args:
            p = Process(target=fn, args=(arg,))
            p.start()
            procs.append(p)

    for p in procs:
        p.join()


if __name__ == "__main__":
    rq1()
