import json
import random
import time
from datetime import date, datetime
from pathlib import Path
import sys

# pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

# omus imports
from ous import OUS

from ous_utils import OusParams, Clauses

sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
sys.path.append('/home/emilio/Documents/cppy_src/')
sys.path.append('/home/emilio/documents/cppy_mysrc/')

# from cppy.solver_interfaces.pysat_tools import
from cppy.model_tools import to_cnf
from cppy import BoolVarImpl, Comparison, Model, Operator, cnf_to_pysat

from frietkot import frietKotProblem, simpleProblem


from multiprocessing import Process

SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES
TIMEOUT_EXP1 = 10 * MINUTES


def runParallel(fn, args):
    procs = []
    for arg in zip(args):
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
    return sat_files


def experiment1():
    today = date.today().strftime("%Y_%m_%d")
    outputDir = 'data/experiment1/results/'+today + '/'
    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    # setup experiments
    sat_instances = get_instances()
    print(sat_instances)

    # setup arguments
    incrs = [True, False]
    pre_seeds = [True, False]
    constraineds = [True, False]
    post_opts = [True, False]
    post_opt_incrs = [True, False]
    post_opt_greedys = [True, False]
    boundeds = [True, False]

    running_params = []
    for fpath, fname in sat_instances:
        cnt = 0
        for incr in incrs:
            for constrained in constraineds:
                for pre_seed in pre_seeds:
                    for post_opt in post_opts:
                        if post_opt:
                            for post_opt_incr in post_opt_incrs:
                                for post_opt_greedy in post_opt_greedys:
                                    for bounded in boundeds:
                                        outputFile = outputDir + fname.replace('.cnf','') + ".json"
                                        ousParam = OusParams()
                                        ousParam.pre_seed= pre_seed
                                        ousParam.constrained = constrained
                                        ousParam.incremental = incr
                                        ousParam.post_opt = post_opt
                                        ousParam.post_opt_incremental = post_opt_incr
                                        ousParam.post_opt_greedy = post_opt_greedy
                                        ousParam.bounded = bounded
                                        running_params.append((ousParam, fpath, fname, outputFile))
                                        cnt += 1
    # print(running_params)
    runParallel(exp1_instance, running_params)


def exp1_instance(args):
    ousParam, fpath, fname, outputFile = args
    print("File:", fpath)
    print("File:", fname, outputFile)


def main():
    # experiment1()
    cnf, facts = simpleProblem()
    print(cnf)
    # clauses = Clauses()
    o = OUS()
    o.add_hardClauses(cnf)
    o.add_IndicatorVars()
    print(o.hard_clauses)
    print(o.soft_clauses)
    # print(p)

if __name__ == "__main__":
    main()