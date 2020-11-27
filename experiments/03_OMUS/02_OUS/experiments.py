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
    for arg in args:
        p = Process(target=fn, args=arg)
        p.start()
        procs.append(p)

    for p in procs:
        p.join()


def generate_weights(instance):
    clauses = CNF(from_file=instance).clauses
    weights = random.choices(list(range(5, 21)), k=len(clauses))
    return weights


def checkSatFile(instance):
    cnf = CNF(from_file=instance)
    with Solver(bootstrap_with=cnf.clauses) as s:
        solved = s.solve()
        return solved


def get_instances():
    p = Path('data/cnf_instances/')
    instances = [x for x in p.iterdir()]
    filenames = [(instance, instance.name) for instance in instances if '.cnf' in instance.name]
    sat_files = [(i, name) for i, name in filenames if checkSatFile(i)]
    sorted(sat_files, key=lambda path: path[0].stat().st_size)
    return sat_files


def exp1_instance(args):
    ousParam, fpath, fname, outputFile = args
    print("File:", fpath)
    print("File:", fname, outputFile)


def test_instance():
    # test on simple case
    s_cnf = simpleProblem()
    s_cnf_ass, assumptions = add_assumptions(s_cnf)

    # transform list cnf into CNF object
    simple_cnf = CNF(from_clauses=s_cnf_ass)
    U = get_user_vars(simple_cnf)
    f = lambda l: 1
    I = set(assumptions)
    explain(C=simple_cnf, U=U, f=f, I=I)


def main():
    f = lambda l: 1
    instances = get_instances()[:2]
    for i_path, i_name in instances:
        i_clauses, i_assumptions = add_assumptions(CNF(from_file=i_path).clauses)
        # print(i_clauses)
        # print(i_assumptions)
        i_cnf = CNF(from_clauses=i_clauses)
        U = get_user_vars(i_cnf)
        I = set(i_assumptions)
        explain(C=i_cnf, U=U, f=f, I=I)
    # print(instances)


if __name__ == "__main__":
    main()
