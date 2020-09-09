
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
import pprint

from omus import OMUS, OMUSBase

from test_explain import originProblem

from csp_explain import omusExplain, maxPropagate, optimalPropagate, cost

sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
sys.path.append('/home/emilio/Documents/cppy_src/')
sys.path.append('/home/emilio/documents/cppy_mysrc/')
# from cppy.solver_interfaces.pysat_tools import
from cppy.model_tools.to_cnf import *
from cppy import BoolVarImpl, Comparison, Model, Operator, cnf_to_pysat

from multiprocessing import Process


SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES
TIMEOUT_EXP1 = 1 * MINUTES

def checksatCNF(instance):
    cnf = CNF(from_file=instance)
    with Solver() as s:
        s.append_formula(cnf.clauses)
        solved = s.solve()
        model = s.get_model()
        return solved, model


def get_literals(model, n_literals):
    return random.sample(model, n_literals)


def generate_weights(instance):
    clauses = CNF(from_file=instance).clauses
    weights = random.choices(list(range(1, 21)), k=len(clauses))
    return weights


def read_json(filepath):
    with open(filepath, "r") as read_file:
        return json.load(read_file)['weights']

def get_instances(n=10):
    p = Path('data/experiment1/SW100-8-0/')
    # print(p.exists())
    # for child in p.iterdir():
    #     print(child)
    instances = random.sample([x for x in p.iterdir()], n)
    filenames = [instance.name for instance in instances]
    return instances, filenames

def experiment1_OMUS(sd=20200918):
    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    outputDir = 'data/experiment1/results/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    # parameters
    timeout = TIMEOUT_EXP1
    n_literals = 10
    n_instances = 10

    results = {}
    instances, filenames = get_instances(n_instances)
    weights = {}
    instance_literals = {}

    for instance, filename in zip(instances, filenames):
        print(instance, filename)
        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)
        assert sat is True

        # select 5 literals to explain
        instance_literals[filename] = get_literals(model, n_literals)

        # generate some weights for each
        weights[filename] = read_json('data/experiment1/SW100-8-0_weights/' + instance.stem + ".json")

        # results dict
        results[filename] = {
            'parameters': {
                'seed': sd,
                'weights': weights[filename],
                'literals': instance_literals[filename]
            }
        }

        filepath = Path(outputDir)
        filepath.mkdir(parents=True, exist_ok=True)

        configs = ['Omus', 'OmusPost', 'OmusIncr', 'OmusIncrPost', 'OmusIncrWarm',
                   'OmusIncrPostWarm', 'OmusConstr', 'OmusConstrIncr', 'OmusConstrIncrWarm']

        for c in configs:

            filepath = Path(outputDir + c + '/')
            filepath.mkdir(parents=True, exist_ok=True)

            results[filename][c] = {
                'filename': filename.replace('.cnf', ''),
                'exec_times': [],
                'H_sizes': [],
                'greedy':[],
                'incr':[],
                'opt':[],
                't_opt':[],
                't_incr':[],
                't_greedy':[],
                't_sat':[],
                't_grow':[]
            }

        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)

        cnf = CNF(from_file=instance)
        # pprint.pprint(results, width=1)
        model = set(model)
        I = set()

        I_cnf = [frozenset({lit}) for lit in set()]

        o = OMUSBase(
            hard_clauses=list(),
            soft_clauses=[frozenset(clause) for clause in cnf.clauses],
            I=model,
            bv=None,
            soft_weights=weights[filename],
            reuse_mss=False,
            parameters={'extension': 'maxsat', 'output': instance.stem + '.json'},
            logging=True
        )

        # 'Omus'
        tstart_exp1 = time.time()

        I = set()
        I_cnf = [frozenset({lit}) for lit in I]

        w_I = [1 for _ in I] + [1]

        print(f'{filename}: Starting OMUS...\n')

        # existing facts + unit weight for negated literal
        w_I = [1 for _ in I] + [1]
        for id, i in enumerate(sorted(list(model - I))):
            if id > 9:
                break
            tstart_lit = time.time()
            remaining_time = timeout - (time.time() - tstart_exp1)

            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                        explained_literal=i,
                                        add_weights=w_I,
                                        timeout=remaining_time,
                                        postponed_omus=False
                                        )

            if hs is None:
                results[filename]['Omus']['exec_times'].append('timeout')
                results[filename]['Omus']['H_sizes'].append(o.hs_sizes[-1])
                results[filename]['Omus']['greedy'].append(o.greedy_steps[-1])
                results[filename]['Omus']['incr'].append(o.incremental_steps[-1])
                results[filename]['Omus']['opt'].append(o.optimal_steps[-1])
                results[filename]['Omus']['t_opt'].append(o.optimal_timing[-1])
                results[filename]['Omus']['t_incr'].append(o.incremental_timing[-1])
                results[filename]['Omus']['t_greedy'].append(o.greedy_timing[-1])
                results[filename]['Omus']['t_sat'].append(o.sat_timing[-1])
                results[filename]['Omus']['t_grow'].append(o.grow_timing[-1])
                break
            tend_lit = time.time()
            results[filename]['Omus']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['Omus']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['Omus']['greedy'].append(o.greedy_steps[-1])
            results[filename]['Omus']['incr'].append(o.incremental_steps[-1])
            results[filename]['Omus']['opt'].append(o.optimal_steps[-1])
            results[filename]['Omus']['t_opt'].append(o.optimal_timing[-1])
            results[filename]['Omus']['t_incr'].append(o.incremental_timing[-1])
            results[filename]['Omus']['t_greedy'].append(o.greedy_timing[-1])
            results[filename]['Omus']['t_sat'].append(o.sat_timing[-1])
            results[filename]['Omus']['t_grow'].append(o.grow_timing[-1])

            assert len(hs) > 0, "OMUS shoudl be non empty"


        print(f'{filename}: Writing Omus... to \n\t\t', outputDir + filename.replace('.cnf', '') + '_Omus_' + outputFile, '\n')
        with open(outputDir +'Omus/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
            json.dump(results[filename]['Omus'], fp)

        del o

def experiment1_OMUSIncr(sd=20200918):
    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    outputDir = 'data/experiment1/results/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    # parameters
    timeout = TIMEOUT_EXP1
    n_literals = 10
    n_instances = 10

    results = {}
    instances, filenames = get_instances(n_instances)
    weights = {}
    instance_literals = {}

    for instance, filename in zip(instances, filenames):
        print(instance, filename)
        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)
        assert sat is True

        # select 5 literals to explain
        instance_literals[filename] = get_literals(model, n_literals)

        # generate some weights for each
        weights[filename] = read_json('data/experiment1/SW100-8-0_weights/' + instance.stem + ".json")

        # results dict
        results[filename] = {
            'parameters': {
                'seed': sd,
                'weights': weights[filename],
                'literals': instance_literals[filename]
            }
        }

        filepath = Path(outputDir)
        filepath.mkdir(parents=True, exist_ok=True)

        configs = ['Omus', 'OmusPost', 'OmusIncr', 'OmusIncrPost', 'OmusIncrWarm',
                   'OmusIncrPostWarm', 'OmusConstr', 'OmusConstrIncr', 'OmusConstrIncrWarm']

        for c in configs:

            filepath = Path(outputDir + c + '/')
            filepath.mkdir(parents=True, exist_ok=True)

            results[filename][c] = {
                'filename': filename.replace('.cnf', ''),
                'exec_times': [],
                'H_sizes': [],
                'greedy':[],
                'incr':[],
                'opt':[],
                't_opt':[],
                't_incr':[],
                't_greedy':[],
                't_sat':[],
                't_grow':[]
            }

        print(instance, filename)
        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)

        cnf = CNF(from_file=instance)
        # pprint.pprint(results, width=1)
        model = set(model)
        I = set()

        I_cnf = [frozenset({lit}) for lit in set()]

        o = OMUSBase(
            hard_clauses=list(),
            soft_clauses=[frozenset(clause) for clause in cnf.clauses],
            I=model,
            bv=None,
            soft_weights=weights[filename],
            reuse_mss=False,
            parameters={'extension': 'maxsat', 'output': instance.stem + '.json'},
            logging=True
        )

        # 'OmusIncr'
        o.reuse_mss = True
        timedout = False
        o.MSSes= set()
        o.MSS_sizes = []

        print(f'{filename}: Starting OmusIncr...\n')
        I = set()
        I_cnf = [frozenset({lit}) for lit in I]
        w_I = [1 for _ in I] + [1]

        o.reuse_mss = True
        o.MSSes= set()
        o.MSS_sizes = []
        timedout = False
        tstart_exp1 = time.time()

        # existing facts + unit weight for negated literal
        w_I = [1 for _ in I] + [1]
        for id, i in enumerate(sorted(list(model - I))):
            if id > 9:
                break
            tstart_lit = time.time()
            remaining_time = timeout - (time.time() - tstart_exp1)

            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                        explained_literal=i,
                                        add_weights=w_I,
                                        timeout=remaining_time,
                                        postponed_omus=False
                                        )

            if hs is None:
                results[filename]['OmusIncr']['exec_times'].append('timeout')
                results[filename]['OmusIncr']['H_sizes'].append(o.hs_sizes[-1])
                results[filename]['OmusIncr']['greedy'].append(o.greedy_steps[-1])
                results[filename]['OmusIncr']['incr'].append(o.incremental_steps[-1])
                results[filename]['OmusIncr']['opt'].append(o.optimal_steps[-1])
                results[filename]['OmusIncr']['t_opt'].append(o.optimal_timing[-1])
                results[filename]['OmusIncr']['t_incr'].append(o.incremental_timing[-1])
                results[filename]['OmusIncr']['t_greedy'].append(o.greedy_timing[-1])
                results[filename]['OmusIncr']['t_sat'].append(o.sat_timing[-1])
                results[filename]['OmusIncr']['t_grow'].append(o.grow_timing[-1])
                break

            # post-processing the MSSes
            keep = set()
            for (m1, m1_model) in o.MSSes:
                keep_m1 = True
                for (m2, _) in o.MSSes:
                    if m1 != m2 and m1 < m2:
                        keep_m1 = False
                if keep_m1:
                    keep.add((m1, m1_model))
            o.MSSes = keep
      
            tend_lit = time.time()
            results[filename]['OmusIncr']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['OmusIncr']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['OmusIncr']['greedy'].append(o.greedy_steps[-1])
            results[filename]['OmusIncr']['incr'].append(o.incremental_steps[-1])
            results[filename]['OmusIncr']['opt'].append(o.optimal_steps[-1])
            results[filename]['OmusIncr']['t_opt'].append(o.optimal_timing[-1])
            results[filename]['OmusIncr']['t_incr'].append(o.incremental_timing[-1])
            results[filename]['OmusIncr']['t_greedy'].append(o.greedy_timing[-1])
            results[filename]['OmusIncr']['t_sat'].append(o.sat_timing[-1])
            results[filename]['OmusIncr']['t_grow'].append(o.grow_timing[-1])
      

        print(f'{filename}: Writing OmusIncr... to \n\t\t', outputDir + filename.replace('.cnf', '') + '_OmusIncr_' + outputFile, '\n')
        with open(outputDir + 'OmusIncr/' + filename.replace('.cnf', '')  + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusIncr'], fp)

        del o

def experiment1_OMUSPost(sd=20200918):
    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    outputDir = 'data/experiment1/results/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    # parameters
    timeout = TIMEOUT_EXP1
    n_literals = 10
    n_instances = 10

    results = {}
    instances, filenames = get_instances(n_instances)
    weights = {}
    instance_literals = {}

    for instance, filename in zip(instances, filenames):
        print(instance, filename)
        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)
        assert sat is True

        # select 5 literals to explain
        instance_literals[filename] = get_literals(model, n_literals)

        # generate some weights for each
        weights[filename] = read_json('data/experiment1/SW100-8-0_weights/' + instance.stem + ".json")

        # results dict
        results[filename] = {
            'parameters': {
                'seed': sd,
                'weights': weights[filename],
                'literals': instance_literals[filename]
            }
        }

        filepath = Path(outputDir)
        filepath.mkdir(parents=True, exist_ok=True)

        configs = ['Omus', 'OmusPost', 'OmusIncr', 'OmusIncrPost', 'OmusIncrWarm',
                   'OmusIncrPostWarm', 'OmusConstr', 'OmusConstrIncr', 'OmusConstrIncrWarm']

        for c in configs:

            filepath = Path(outputDir + c + '/')
            filepath.mkdir(parents=True, exist_ok=True)

            results[filename][c] = {
                'filename': filename.replace('.cnf', ''),
                'exec_times': [],
                'H_sizes': [],
                'greedy':[],
                'incr':[],
                'opt':[],
                't_opt':[],
                't_incr':[],
                't_greedy':[],
                't_sat':[],
                't_grow':[]
            }

        print(instance, filename)
        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)

        cnf = CNF(from_file=instance)
        # pprint.pprint(results, width=1)
        model = set(model)
        I = set()

        I_cnf = [frozenset({lit}) for lit in set()]

        o = OMUSBase(
            hard_clauses=list(),
            soft_clauses=[frozenset(clause) for clause in cnf.clauses],
            I=model,
            bv=None,
            soft_weights=weights[filename],
            reuse_mss=False,
            parameters={'extension': 'maxsat', 'output': instance.stem + '.json'},
            logging=True
        )

        # 'OmusPost'
        I = set()
        I_cnf = [frozenset({lit}) for lit in I]
        print(f'{filename}: Starting OmusPost...\n')
        o.reuse_mss = False
        timedout = False
        o.MSSes= set()
        o.MSS_sizes = []
        w_I = [1 for _ in I] + [1]

        tstart_exp1 = time.time()

        w_I = [1 for _ in I] + [1]
        for id, i in enumerate(sorted(list(model - I))):
            if id > 9:
                break
            tstart_lit = time.time()
            remaining_time = timeout - (time.time() - tstart_exp1)

            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                        explained_literal=i,
                                        add_weights=w_I,
                                        timeout=remaining_time,
                                        postponed_omus=True
                                        )

            if hs is None:
                results[filename]['OmusPost']['exec_times'].append('timeout')
                results[filename]['OmusPost']['H_sizes'].append(o.hs_sizes[-1])
                results[filename]['OmusPost']['greedy'].append(o.greedy_steps[-1])
                results[filename]['OmusPost']['incr'].append(o.incremental_steps[-1])
                results[filename]['OmusPost']['opt'].append(o.optimal_steps[-1])
                results[filename]['OmusPost']['t_opt'].append(o.optimal_timing[-1])
                results[filename]['OmusPost']['t_incr'].append(o.incremental_timing[-1])
                results[filename]['OmusPost']['t_greedy'].append(o.greedy_timing[-1])
                results[filename]['OmusPost']['t_sat'].append(o.sat_timing[-1])
                results[filename]['OmusPost']['t_grow'].append(o.grow_timing[-1])
                break

            tend_lit = time.time()
            results[filename]['OmusPost']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['OmusPost']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['OmusPost']['greedy'].append(o.greedy_steps[-1])
            results[filename]['OmusPost']['incr'].append(o.incremental_steps[-1])
            results[filename]['OmusPost']['opt'].append(o.optimal_steps[-1])
            results[filename]['OmusPost']['t_opt'].append(o.optimal_timing[-1])
            results[filename]['OmusPost']['t_incr'].append(o.incremental_timing[-1])
            results[filename]['OmusPost']['t_greedy'].append(o.greedy_timing[-1])
            results[filename]['OmusPost']['t_sat'].append(o.sat_timing[-1])
            results[filename]['OmusPost']['t_grow'].append(o.grow_timing[-1])

        print(f'{filename}: Writing _OmusPost_... to \n\t\t', outputDir + filename.replace('.cnf', '') + '_OmusPost_' + outputFile, '\n')
        with open(outputDir +  'OmusPost/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusPost'], fp)

        del o

def experiment1_OMUSIncrPost(sd=20200918):
    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    outputDir = 'data/experiment1/results/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    # parameters
    timeout = TIMEOUT_EXP1
    n_literals = 10
    n_instances = 10

    results = {}
    instances, filenames = get_instances(n_instances)
    weights = {}
    instance_literals = {}

    for instance, filename in zip(instances, filenames):
        print(instance, filename)
        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)
        assert sat is True

        # select 5 literals to explain
        instance_literals[filename] = get_literals(model, n_literals)

        # generate some weights for each
        weights[filename] = read_json('data/experiment1/SW100-8-0_weights/' + instance.stem + ".json")

        # results dict
        results[filename] = {
            'parameters': {
                'seed': sd,
                'weights': weights[filename],
                'literals': instance_literals[filename]
            }
        }

        filepath = Path(outputDir)
        filepath.mkdir(parents=True, exist_ok=True)

        configs = ['Omus', 'OmusPost', 'OmusIncr', 'OmusIncrPost', 'OmusIncrWarm',
                   'OmusIncrPostWarm', 'OmusConstr', 'OmusConstrIncr', 'OmusConstrIncrWarm']

        for c in configs:

            filepath = Path(outputDir + c + '/')
            filepath.mkdir(parents=True, exist_ok=True)

            results[filename][c] = {
                'filename': filename.replace('.cnf', ''),
                'exec_times': [],
                'H_sizes': [],
                'greedy':[],
                'incr':[],
                'opt':[],
                't_opt':[],
                't_incr':[],
                't_greedy':[],
                't_sat':[],
                't_grow':[]
            }
        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)

        cnf = CNF(from_file=instance)
        # pprint.pprint(results, width=1)
        model = set(model)
        I = set()

        I_cnf = [frozenset({lit}) for lit in set()]

        o = OMUSBase(
            hard_clauses=list(),
            soft_clauses=[frozenset(clause) for clause in cnf.clauses],
            I=model,
            bv=None,
            soft_weights=weights[filename],
            reuse_mss=False,
            parameters={'extension': 'maxsat', 'output': instance.stem + '.json'},
            logging=True
        )

        # 'OmusIncrPost'

        print(f'{filename}: Starting OmusIncrPost...\n')
        I = set()
        I_cnf = [frozenset({lit}) for lit in I]

        o.reuse_mss = True
        o.MSSes= set()
        o.MSS_sizes = []

        tstart_exp1 = time.time()

        # existing facts + unit weight for negated literal
        w_I = [1 for _ in I] + [1]
        for id, i in enumerate(sorted(list(model - I))):
            if id > 9:
                break
            tstart_lit = time.time()
            remaining_time = timeout - (time.time() - tstart_exp1)

            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                        explained_literal=i,
                                        add_weights=w_I,
                                        timeout=remaining_time,
                                        postponed_omus=True
                                        )

            if hs is None:
                results[filename]['OmusIncrPost']['exec_times'].append('timeout')
                results[filename]['OmusIncrPost']['H_sizes'].append(o.hs_sizes[-1])
                results[filename]['OmusIncrPost']['greedy'].append(o.greedy_steps[-1])
                results[filename]['OmusIncrPost']['incr'].append(o.incremental_steps[-1])
                results[filename]['OmusIncrPost']['opt'].append(o.optimal_steps[-1])
                results[filename]['OmusIncrPost']['t_opt'].append(o.optimal_timing[-1])
                results[filename]['OmusIncrPost']['t_incr'].append(o.incremental_timing[-1])
                results[filename]['OmusIncrPost']['t_greedy'].append(o.greedy_timing[-1])
                results[filename]['OmusIncrPost']['t_sat'].append(o.sat_timing[-1])
                results[filename]['OmusIncrPost']['t_grow'].append(o.grow_timing[-1])
                break

            # post-processing the MSSes
            keep = set()
            for (m1, m1_model) in o.MSSes:
                keep_m1 = True
                for (m2, _) in o.MSSes:
                    if m1 != m2 and m1 < m2:
                        keep_m1 = False
                if keep_m1:
                    keep.add((m1, m1_model))
            o.MSSes = keep

            tend_lit = time.time()
            results[filename]['OmusIncrPost']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['OmusIncrPost']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['OmusIncrPost']['greedy'].append(o.greedy_steps[-1])
            results[filename]['OmusIncrPost']['incr'].append(o.incremental_steps[-1])
            results[filename]['OmusIncrPost']['opt'].append(o.optimal_steps[-1])
            results[filename]['OmusIncrPost']['t_opt'].append(o.optimal_timing[-1])
            results[filename]['OmusIncrPost']['t_incr'].append(o.incremental_timing[-1])
            results[filename]['OmusIncrPost']['t_greedy'].append(o.greedy_timing[-1])
            results[filename]['OmusIncrPost']['t_sat'].append(o.sat_timing[-1])
            results[filename]['OmusIncrPost']['t_grow'].append(o.grow_timing[-1])
        # post-processing the MSSes

        print(f'{filename}: Writing _OmusIncrPost_... to \n\t\t', outputDir + filename.replace('.cnf', '') + '_OmusIncrPost_' + outputFile, '\n')
        with open(outputDir + 'OmusIncrPost/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusIncrPost'], fp)

        del o

def experiment1_OMUSIncrPostWarm(sd=20200918):
    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    outputDir = 'data/experiment1/results/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    # parameters
    timeout = TIMEOUT_EXP1
    n_literals = 10
    n_instances = 10

    results = {}
    instances, filenames = get_instances(n_instances)
    weights = {}
    instance_literals = {}

    for instance, filename in zip(instances, filenames):
        print(instance, filename)
        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)
        assert sat is True

        # select 5 literals to explain
        instance_literals[filename] = get_literals(model, n_literals)

        # generate some weights for each
        weights[filename] = read_json('data/experiment1/SW100-8-0_weights/' + instance.stem + ".json")

        # results dict
        results[filename] = {
            'parameters': {
                'seed': sd,
                'weights': weights[filename],
                'literals': instance_literals[filename]
            }
        }

        filepath = Path(outputDir)
        filepath.mkdir(parents=True, exist_ok=True)

        configs = ['Omus', 'OmusPost', 'OmusIncr', 'OmusIncrPost', 'OmusIncrWarm',
                   'OmusIncrPostWarm', 'OmusConstr', 'OmusConstrIncr', 'OmusConstrIncrWarm']

        for c in configs:

            filepath = Path(outputDir + c + '/')
            filepath.mkdir(parents=True, exist_ok=True)

            results[filename][c] = {
                'filename': filename.replace('.cnf', ''),
                'exec_times': [],
                'H_sizes': [],
                'greedy':[],
                'incr':[],
                'opt':[],
                't_opt':[],
                't_incr':[],
                't_greedy':[],
                't_sat':[],
                't_grow':[]
            }

        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)

        cnf = CNF(from_file=instance)
        # pprint.pprint(results, width=1)
        model = set(model)
        print(optimalPropagate(cnf.clauses) - model)
        I = set()

        I_cnf = [frozenset({lit}) for lit in set()]

        o = OMUSBase(
            hard_clauses=list(),
            soft_clauses=[frozenset(clause) for clause in cnf.clauses],
            I=model,
            bv=None,
            soft_weights=weights[filename],
            reuse_mss=False,
            parameters={'extension': 'maxsat', 'output': instance.stem + '.json'},
            logging=True
        )

        # 'OmusIncrPost warm start'
        print(f'{filename}: Starting OmusIncrPost warm start...\n')
        o.reuse_mss = True
        timedout = False
        o.MSSes= set()
        o.MSS_sizes = []

        tstart_exp1 = time.time()

        base_F = set(range(len(o.soft_clauses)))
        # F = base_F | set({o.softClauseIdxs[frozenset({-i})] for i in model - I})
        o.MSSes.add((o.fullMss, frozenset(model)))
        # print("Seeding")
        # for i in model - I:
        #     o.clauses = o.soft_clauses + [frozenset({-i})]
        #     o.weights = o.soft_weights + [1]
        #     F_prime = set({o.softClauseIdxs[frozenset({-i})]})

        #     MSS, MSS_Model = o.grow(F_prime, set())

        #     o.MSSes.add((frozenset(MSS), frozenset(MSS_Model)))


        I = set()
        I_cnf = [frozenset({lit}) for lit in I]

        # existing facts + unit weight for negated literal
        w_I = [1 for _ in I] + [1]
        for id, i in enumerate(sorted(list(model - I))):
            if id > 9:
                break
            tstart_lit = time.time()
            remaining_time = timeout - (time.time() - tstart_exp1)

            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                        explained_literal=i,
                                        add_weights=w_I,
                                        timeout=remaining_time,
                                        postponed_omus=True,
                                        )

            if hs is None:
                results[filename]['OmusIncrPostWarm']['exec_times'].append('timeout')
                results[filename]['OmusIncrPostWarm']['H_sizes'].append(o.hs_sizes[-1])
                results[filename]['OmusIncrPostWarm']['greedy'].append(o.greedy_steps[-1])
                results[filename]['OmusIncrPostWarm']['incr'].append(o.incremental_steps[-1])
                results[filename]['OmusIncrPostWarm']['opt'].append(o.optimal_steps[-1])
                results[filename]['OmusIncrPostWarm']['t_opt'].append(o.optimal_timing[-1])
                results[filename]['OmusIncrPostWarm']['t_incr'].append(o.incremental_timing[-1])
                results[filename]['OmusIncrPostWarm']['t_greedy'].append(o.greedy_timing[-1])
                results[filename]['OmusIncrPostWarm']['t_sat'].append(o.sat_timing[-1])
                results[filename]['OmusIncrPostWarm']['t_grow'].append(o.grow_timing[-1])
                break

            # post-processing the MSSes
            keep = set()
            for (m1, m1_model) in o.MSSes:
                keep_m1 = True
                for (m2, _) in o.MSSes:
                    if m1 != m2 and m1 < m2:
                        keep_m1 = False
                if keep_m1:
                    keep.add((m1, m1_model))
            o.MSSes = keep

            tend_lit = time.time()

            results[filename]['OmusIncrPostWarm']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['OmusIncrPostWarm']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['OmusIncrPostWarm']['greedy'].append(o.greedy_steps[-1])
            results[filename]['OmusIncrPostWarm']['incr'].append(o.incremental_steps[-1])
            results[filename]['OmusIncrPostWarm']['opt'].append(o.optimal_steps[-1])
            results[filename]['OmusIncrPostWarm']['t_opt'].append(o.optimal_timing[-1])
            results[filename]['OmusIncrPostWarm']['t_incr'].append(o.incremental_timing[-1])
            results[filename]['OmusIncrPostWarm']['t_greedy'].append(o.greedy_timing[-1])
            results[filename]['OmusIncrPostWarm']['t_sat'].append(o.sat_timing[-1])
            results[filename]['OmusIncrPostWarm']['t_grow'].append(o.grow_timing[-1])


        print(f'{filename}: Writing _OmusIncrPostWarm_... to \n\t\t', outputDir + filename.replace('.cnf', '') + '_OmusIncrPostWarm_' + outputFile, '\n')
        with open(outputDir +'OmusIncrPostWarm/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusIncrPostWarm'], fp)

        del o

def experiment1_OMUSIncrWarm(sd=20200918):
    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    outputDir = 'data/experiment1/results/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    # parameters
    timeout = TIMEOUT_EXP1
    n_literals = 10
    n_instances = 10

    results = {}
    instances, filenames = get_instances(n_instances)
    weights = {}
    instance_literals = {}

    for instance, filename in zip(instances, filenames):
        print(instance, filename)
        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)
        assert sat is True

        # select 5 literals to explain
        instance_literals[filename] = get_literals(model, n_literals)

        # generate some weights for each
        weights[filename] = read_json('data/experiment1/SW100-8-0_weights/' + instance.stem + ".json")

        # results dict
        results[filename] = {
            'parameters': {
                'seed': sd,
                'weights': weights[filename],
                'literals': instance_literals[filename]
            }
        }

        filepath = Path(outputDir)
        filepath.mkdir(parents=True, exist_ok=True)


        configs = ['Omus', 'OmusPost', 'OmusIncr', 'OmusIncrPost', 'OmusIncrWarm',
                   'OmusIncrPostWarm', 'OmusConstr', 'OmusConstrIncr', 'OmusConstrIncrWarm']


        for c in configs:

            filepath = Path(outputDir + c + '/')
            filepath.mkdir(parents=True, exist_ok=True)

            results[filename][c] = {
                'filename': filename.replace('.cnf', ''),
                'exec_times': [],
                'H_sizes': [],
                'greedy':[],
                'incr':[],
                'opt':[],
                't_opt':[],
                't_incr':[],
                't_greedy':[],
                't_sat':[],
                't_grow':[]
            }

        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)

        cnf = CNF(from_file=instance)
        # pprint.pprint(results, width=1)
        model = set(model)
        I = set()

        I_cnf = [frozenset({lit}) for lit in set()]

        o = OMUSBase(
            hard_clauses=list(),
            soft_clauses=[frozenset(clause) for clause in cnf.clauses],
            I=model,
            bv=None,
            soft_weights=weights[filename],
            reuse_mss=False,
            parameters={'extension': 'maxsat', 'output': instance.stem + '.json'},
            logging=True
        )

        # 'OmusIncrPost warm start'
        print(f'{filename}: Starting OmusIncr warm start...\n')
        o.reuse_mss = True
        timedout = False
        o.MSSes= set()
        o.MSS_sizes = []

        best_costs = dict({i: 9999999 for i in model - I})

        base_F = set(range(len(o.soft_clauses)))

        tstart_exp1 = time.time()
        print("Seeding")
        for i in model - I:
            o.clauses = o.soft_clauses + [frozenset({-i})]
            o.weights = o.soft_weights + [1]
            F_prime = set({o.softClauseIdxs[frozenset({-i})]})

            MSS, MSS_Model = o.grow(F_prime, set())

            o.MSSes.add((frozenset(MSS), frozenset(MSS_Model)))

            # -- precompute some hitting sets for a rough idea on the costs
            w_I = [1 for _ in I] + [1]

        I = set()
        I_cnf = [frozenset({lit}) for lit in I]

        # existing facts + unit weight for negated literal
        w_I = [1 for _ in I] + [1]
        for id, i in enumerate(sorted(list(model - I))):
            if id > 9:
                break
            tstart_lit = time.time()
            remaining_time = timeout - (time.time() - tstart_exp1)

            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                        explained_literal=i,
                                        add_weights=w_I,
                                        timeout=remaining_time,
                                        postponed_omus=False,
                                        best_cost=None
                                        )

            if hs is None:
                results[filename]['OmusIncrWarm']['exec_times'].append('timeout')
                results[filename]['OmusIncrWarm']['H_sizes'].append(o.hs_sizes[-1])
                results[filename]['OmusIncrWarm']['greedy'].append(o.greedy_steps[-1])
                results[filename]['OmusIncrWarm']['incr'].append(o.incremental_steps[-1])
                results[filename]['OmusIncrWarm']['opt'].append(o.optimal_steps[-1])
                results[filename]['OmusIncrWarm']['t_opt'].append(o.optimal_timing[-1])
                results[filename]['OmusIncrWarm']['t_incr'].append(o.incremental_timing[-1])
                results[filename]['OmusIncrWarm']['t_greedy'].append(o.greedy_timing[-1])
                results[filename]['OmusIncrWarm']['t_sat'].append(o.sat_timing[-1])
                results[filename]['OmusIncrWarm']['t_grow'].append(o.grow_timing[-1])
                break

            # post-processing the MSSes
            keep = set()
            for (m1, m1_model) in o.MSSes:
                keep_m1 = True
                for (m2, _) in o.MSSes:
                    if m1 != m2 and m1 < m2:
                        keep_m1 = False
                if keep_m1:
                    keep.add((m1, m1_model))
            o.MSSes = keep

            tend_lit = time.time()

            results[filename]['OmusIncrWarm']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['OmusIncrWarm']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['OmusIncrWarm']['greedy'].append(o.greedy_steps[-1])
            results[filename]['OmusIncrWarm']['incr'].append(o.incremental_steps[-1])
            results[filename]['OmusIncrWarm']['opt'].append(o.optimal_steps[-1])
            results[filename]['OmusIncrWarm']['t_opt'].append(o.optimal_timing[-1])
            results[filename]['OmusIncrWarm']['t_incr'].append(o.incremental_timing[-1])
            results[filename]['OmusIncrWarm']['t_greedy'].append(o.greedy_timing[-1])
            results[filename]['OmusIncrWarm']['t_sat'].append(o.sat_timing[-1])
            results[filename]['OmusIncrWarm']['t_grow'].append(o.grow_timing[-1])
            # post-processing the MSSes

        print(f'{filename}: Writing _OmusIncrWarm_... to \n\t\t', outputDir + filename.replace('.cnf', '') + 'OmusIncrWarm' + outputFile, '\n')
        with open(outputDir +'OmusIncrWarm/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusIncrWarm'], fp)

        del o

def experiment1(sd=20200918):
    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    outputDir = 'data/experiment1/results/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    # parameters
    timeout = 10 * MINUTES
    n_literals = 10
    n_instances = 10

    results = {}
    instances, filenames = get_instances(n_instances)
    weights = {}
    instance_literals = {}

    for instance, filename in zip(instances, filenames):
        print(instance, filename)
        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)
        assert sat is True

        # select 5 literals to explain
        instance_literals[filename] = get_literals(model, n_literals)

        # generate some weights for each
        weights[filename] = generate_weights(instance)

        # results dict
        results[filename] = {
            'parameters': {
                'seed': sd,
                'weights': weights[filename],
                'literals': instance_literals[filename]
            }
        }

        filepath = Path(outputDir)
        filepath.mkdir(parents=True, exist_ok=True)

        configs = ['Omus', 'OmusPost', 'OmusIncr', 'OmusIncrPost','OmusIncrWarm'
                   'OmusIncrPostWarm', 'OmusConstr', 'OmusConstrIncr', 'OmusConstrIncrWarm']

        for c in configs:

            filepath = Path(outputDir + c + '/')
            filepath.mkdir(parents=True, exist_ok=True)

            results[filename][c] = {
                'filename': filename.replace('.cnf', ''),
                'exec_times': [],
                'H_sizes': [],
                'greedy':[],
                'incr':[],
                'opt':[],
            }

    # for instance, filename in zip(instances, filenames):
    #     print(instance, filename)
    #     # Check satisfiability of the instance
    #     sat, model = checksatCNF(instance)

    #     cnf = CNF(from_file=instance)

    #     print(f'{filename}: Starting OMUSConstr...\n')

    #     o = OMUS(
    #         modelname='gp2',
    #         hard_clauses=list(),
    #         soft_clauses=[frozenset(clause) for clause in cnf.clauses],
    #         I=model,
    #         soft_weights=weights[filename],
    #         parameters={'extension': 'maxsat',
    #                     'output': instance.stem + '.json'},
    #     )

    #     I = set()
    #     I_cnf = []
    #     # derived_literals = []

    #     tstart_o1 = time.time()
    #     for i in range(n_literals):
    #         print(f'\t Explaining literal {i+1}/[{n_literals}]...\n')
    #         remaining_time = timeout - (time.time() - tstart_o1)
    #         print(remaining_time)
    #         # OMUS no improvements
    #         t_start = time.time()
    #         hs, explanation = o.omusConstr(timeout=remaining_time)
    #         if hs is None:
    #             results[filename]['OmusConstr']['exec_times'].append('timeout')
    #             results[filename]['OmusConstr']['H_sizes'].append(o.hs_sizes[-1])
    #             results[filename]['OmusConstr']['greedy'].append(o.greedy_steps[-1])
    #             results[filename]['OmusConstr']['incr'].append(o.incremental_steps[-1])
    #             results[filename]['OmusConstr']['opt'].append(o.optimal_steps[-1])
    #             # o.deleteModel()
    #             break
    #         t_end = time.time()
    #         literal = [clause for clause in explanation if len(clause) == 1 and clause in [frozenset({-lit}) for lit in model]]
    #         print(literal)

    #         # explaining facts
    #         E_best = [ci for ci in explanation if ci in I_cnf]

    #         # constraint used ('and not ci in E_i': dont repeat unit clauses)
    #         S_best = [ci for ci in explanation if ci in o.soft_clauses and ci not in E_best]

    #         New_info = optimalPropagate([] + E_best + S_best, I)
    #         N_best = New_info.intersection(model) - I

    #         # add new info
    #         I = I | N_best
    #         new_cnf = [frozenset({lit})
    #                    for lit in N_best if frozenset({lit}) not in I_cnf]
    #         I_cnf += new_cnf

    #         o.updateObjWeightsInterpret(I)

    #         results[filename]['OmusConstr']['exec_times'].append(round(t_end-t_start, 3))
    #         results[filename]['OmusConstr']['H_sizes'].append(o.hs_sizes[-1])
    #         results[filename]['OmusConstr']['greedy'].append(o.greedy_steps[-1])
    #         results[filename]['OmusConstr']['incr'].append(o.incremental_steps[-1])
    #         results[filename]['OmusConstr']['opt'].append(o.optimal_steps[-1])

    #     o.deleteModel()
    #     del o
    #     print(f'{filename}: Writing OMUSConstr... to \n\t\t',  outputDir + filename.replace('.cnf', '') + 'OmusConstr_' + outputFile,  '\n')

    #     with open(outputDir + 'OmusConstr/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
    #         json.dump(results[filename]['OmusConstr'], fp)

    #     print(f'{filename}: Starting OmusConstrIncr...\n')
    #     o2 = OMUS(
    #         modelname='gp1',
    #         hard_clauses=list(),
    #         soft_clauses=[frozenset(clause) for clause in cnf.clauses],
    #         I=model,
    #         soft_weights=weights[filename],
    #         parameters={'extension': 'maxsat',
    #                     'output': instance.stem + '.json'},
    #     )

    #     I = set()
    #     I_cnf = []
    #     tstart_o2 = time.time()
    #     for i in range(n_literals):
    #         print(f'\t Explaining literal {i+1}/[{n_literals}]...\n')
    #         remaining_time = timeout - (time.time() - tstart_o2)
    #         # OMUS no improvements
    #         t_start = time.time()
    #         hs, explanation = o2.omusConstr(do_incremental=True, greedy=True, timeout=remaining_time)
    #         if hs is None:
    #             results[filename]['OmusConstrIncr']['exec_times'].append('timeout')
    #             results[filename]['OmusConstrIncr']['H_sizes'].append(o2.hs_sizes[-1])
    #             results[filename]['OmusConstrIncr']['greedy'].append(o2.greedy_steps[-1])
    #             results[filename]['OmusConstrIncr']['incr'].append(o2.incremental_steps[-1])
    #             results[filename]['OmusConstrIncr']['opt'].append(o2.optimal_steps[-1])
    #             # o.deleteModel()
    #             break
    #         t_end = time.time()

    #         # explaining facts
    #         E_best = [ci for ci in explanation if ci in I_cnf]

    #         # constraint used ('and not ci in E_i': dont repeat unit clauses)
    #         S_best = [ci for ci in explanation if ci in o2.soft_clauses and ci not in E_best]

    #         New_info = optimalPropagate([] + E_best + S_best, I)
    #         N_best = New_info.intersection(model) - I

    #         # add new info
    #         I = I | N_best
    #         new_cnf = [frozenset({lit})
    #                 for lit in N_best if frozenset({lit}) not in I_cnf]
    #         I_cnf += new_cnf

    #         o2.updateObjWeightsInterpret(I)

    #         results[filename]['OmusConstrIncr']['exec_times'].append(round(t_end-t_start, 3))
    #         results[filename]['OmusConstrIncr']['H_sizes'].append(o2.hs_sizes[-1])
    #         results[filename]['OmusConstrIncr']['greedy'].append(o2.greedy_steps[-1])
    #         results[filename]['OmusConstrIncr']['incr'].append(o2.incremental_steps[-1])
    #         results[filename]['OmusConstrIncr']['opt'].append(o2.optimal_steps[-1])

    #     o2.deleteModel()
    #     del o2

    #     print(f'{filename}: Writing OMUSConstr... to \n\t\t',  outputDir + filename.replace('.cnf', '') + 'OmusConstrIncr_' + outputFile, '\n')

    #     with open(outputDir + 'OmusConstrIncr/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
    #         json.dump(results[filename]['OmusConstrIncr'], fp)

    #     print(f'{filename}: Starting OmusConstrIncr...\n')
    #     o3 = OMUS(
    #         modelname='gp3',
    #         hard_clauses=list(),
    #         soft_clauses=[frozenset(clause) for clause in cnf.clauses],
    #         I=model,
    #         soft_weights=weights[filename],
    #         parameters={'extension': 'maxsat',
    #                     'output': instance.stem + '.json'},
    #     )
    #     print(f'\t Seeding....\n')

    #     tstart_o3 = time.time()
    #     F = frozenset(range(o3.nClauses))
    #     seedable = set(-i for i in model)
    #     while len(seedable) > 0:
    #         i = next(iter(seedable))

    #         F_prime = set([o3.softClauseIdxs[frozenset({i})]])
    #         MSS, MSS_Model = o3.grow(F_prime, set()|{i})

    #         C = F - MSS
    #         o3.addSetGurobiOmusConstr(C)

    #         other_seeds = seedable&frozenset(MSS_Model)
    #         seedable -= other_seeds

    #     I = set()
    #     I_cnf = []
    #     for i in range(n_literals):
    #         print(f'\t Explaining literal {i+1}/[{n_literals}]...\n')
    #         # OMUS no improvements
    #         remaining_time = timeout - (time.time() - tstart_o3)
    #         t_start = time.time()
    #         hs, explanation = o3.omusConstr(do_incremental=True, greedy=True, timeout=remaining_time)
    #         t_end = time.time()
    #         if hs is None:
    #             results[filename]['OmusConstrIncrWarm']['exec_times'].append('timeout')
    #             results[filename]['OmusConstrIncrWarm']['H_sizes'].append(o3.hs_sizes[-1])
    #             results[filename]['OmusConstrIncrWarm']['greedy'].append(o3.greedy_steps[-1])
    #             results[filename]['OmusConstrIncrWarm']['incr'].append(o3.incremental_steps[-1])
    #             results[filename]['OmusConstrIncrWarm']['opt'].append(o3.optimal_steps[-1])
    #             # o.deleteModel()
    #             break

    #         # explaining facts
    #         E_best = [ci for ci in explanation if ci in I_cnf]

    #         # constraint used ('and not ci in E_i': dont repeat unit clauses)
    #         S_best = [ci for ci in explanation if ci in o3.soft_clauses and ci not in E_best]

    #         New_info = optimalPropagate([] + E_best + S_best, I)
    #         N_best = New_info.intersection(model) - I

    #         # add new info
    #         I = I | N_best
    #         new_cnf = [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]
    #         I_cnf += new_cnf

    #         o3.updateObjWeightsInterpret(I)

    #         results[filename]['OmusConstrIncrWarm']['exec_times'].append(round(t_end-t_start, 3))
    #         results[filename]['OmusConstrIncrWarm']['H_sizes'].append(o3.hs_sizes[-1])
    #         results[filename]['OmusConstrIncrWarm']['greedy'].append(o3.greedy_steps[-1])
    #         results[filename]['OmusConstrIncrWarm']['incr'].append(o3.incremental_steps[-1])
    #         results[filename]['OmusConstrIncrWarm']['opt'].append(o3.optimal_steps[-1])

    
    #     o3.deleteModel()
    #     del o3
    #     print(f'{filename}: Writing OMUSConstr... to \n\t\t', outputDir + filename.replace('.cnf', '') + 'OmusConstrIncrWarm_' + outputFile, '\n')

    #     with open(outputDir+ 'OmusConstrIncrWarm/' + filename.replace('.cnf', '')  + outputFile , 'w') as fp:
    #         json.dump(results[filename]['OmusConstrIncrWarm'], fp)

    for instance, filename in zip(instances, filenames):
        print(instance, filename)
        # Check satisfiability of the instance
        sat, model = checksatCNF(instance)

        cnf = CNF(from_file=instance)
        # pprint.pprint(results, width=1)
        model = set(model)
        I = set()

        I_cnf = [frozenset({lit}) for lit in set()]

        o = OMUSBase(
            hard_clauses=list(),
            soft_clauses=[frozenset(clause) for clause in cnf.clauses],
            I=model,
            bv=None,
            soft_weights=weights[filename],
            reuse_mss=False,
            parameters={'extension': 'maxsat', 'output': instance.stem + '.json'},
            logging=True
        )

        # 'Omus'
        tstart_exp1 = time.time()

        I = set()
        I_cnf = [frozenset({lit}) for lit in I]

        w_I = [1 for _ in I] + [1]

        timedout = False
        print(f'{filename}: Starting OMUS...\n')
        for j in range(n_literals):

            cost_best = None
            E_best, S_best, N_best = None, None, None

            # existing facts + unit weight for negated literal
            w_I = [1 for _ in I] + [1]
            tstart_lit = time.time()
            for i in model - I:
                remaining_time = timeout - (time.time() - tstart_exp1)

                hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                            explained_literal=i,
                                            add_weights=w_I,
                                            timeout=remaining_time
                                            )

                if hs is None:
                    print("Timedout")
                    timedout = True
                    break

                assert len(hs) > 0, "OMUS shoudl be non empty"

                # explaining facts
                E_i = [ci for ci in explanation if ci in I_cnf]

                # constraint used ('and not ci in E_i': dont repeat unit clauses)
                S_i = [ci for ci in explanation if ci in o.soft_clauses and ci not in E_i]
                S_hs = [o.soft_clauses.index(si) for si in S_i]

                N_i = {i}

                cost_explanation = cost((E_i, S_hs), o.soft_weights, None, None, None)
                # best_costs[i] = min([cost_explanation, best_costs[i]])

                if cost_best is None or cost_explanation < cost_best:
                    E_best, S_best, N_best = E_i, S_i, N_i
                    cost_best = cost_explanation
            if timedout:
                results[filename]['Omus']['exec_times'].append('timeout')
                break
            tend_lit = time.time()
            results[filename]['Omus']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['Omus']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['Omus']['greedy'].append(o.greedy_steps[-1])
            results[filename]['Omus']['incr'].append(o.incremental_steps[-1])
            results[filename]['Omus']['opt'].append(o.optimal_steps[-1])


            # post-processing the MSSes

            New_info = optimalPropagate(o.hard_clauses + E_best + S_best, I)
            N_best = New_info.intersection(model) - I

            # add new info
            I = I | N_best
            I_cnf += [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]

        print(f'{filename}: Writing Omus... to \n\t\t', outputDir + filename.replace('.cnf', '') + '_Omus_' + outputFile, '\n')
        with open(outputDir +'Omus/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
            json.dump(results[filename]['Omus'], fp)

        # 'OmusPost'
        I = set()
        I_cnf = [frozenset({lit}) for lit in I]
        print(f'{filename}: Starting OmusPost...\n')
        o.reuse_mss = False
        timedout = False
        o.MSSes= set()
        o.MSS_sizes = []
        w_I = [1 for _ in I] + [1]

        timedout = False
        tstart_exp1 = time.time()
        for j in range(n_literals):

            cost_best = None
            E_best, S_best, N_best = None, None, None

            # existing facts + unit weight for negated literal
            w_I = [1 for _ in I] + [1]
            tstart_lit = time.time()
            for i in model - I:
                remaining_time = timeout - (time.time() - tstart_exp1)

                hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                            explained_literal=i,
                                            add_weights=w_I,
                                            timeout=remaining_time,
                                            postponed_omus=True
                                            )

                if hs is None:
                    timedout = True
                    break

                assert len(hs) > 0, "OMUS shoudl be non empty"

                # explaining facts
                E_i = [ci for ci in explanation if ci in I_cnf]

                # constraint used ('and not ci in E_i': dont repeat unit clauses)
                S_i = [ci for ci in explanation if ci in o.soft_clauses and ci not in E_i]
                S_hs = [o.soft_clauses.index(si) for si in S_i]

                cost_explanation = cost((E_i, S_hs), o.soft_weights, None, None, None)

                N_i = {i}

                if cost_best is None or cost_explanation < cost_best:
                    E_best, S_best, N_best = E_i, S_i, N_i
                    cost_best = cost_explanation

            if timedout:
                results[filename]['OmusPost']['exec_times'].append('timeout')
                break

            tend_lit = time.time()
            results[filename]['OmusPost']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['OmusPost']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['OmusPost']['greedy'].append(o.greedy_steps[-1])
            results[filename]['OmusPost']['incr'].append(o.incremental_steps[-1])
            results[filename]['OmusPost']['opt'].append(o.optimal_steps[-1])
            # post-processing the MSSes

            New_info = optimalPropagate(o.hard_clauses + E_best + S_best, I)
            N_best = New_info.intersection(model) - I

            # add new info
            I = I | N_best
            I_cnf += [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]

        print(f'{filename}: Writing _OmusPost_... to \n\t\t', outputDir + filename.replace('.cnf', '') + '_OmusPost_' + outputFile, '\n')
        with open(outputDir +  'OmusPost/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusPost'], fp)


        # 'OmusIncr'
        o.reuse_mss = True
        timedout = False
        o.MSSes= set()
        o.MSS_sizes = []

        print(f'{filename}: Starting OmusIncr...\n')
        I = set()
        I_cnf = [frozenset({lit}) for lit in I]
        w_I = [1 for _ in I] + [1]

        o.reuse_mss = True
        o.MSSes= set()
        o.MSS_sizes = []
        timedout = False
        tstart_exp1 = time.time()
        for j in range(n_literals):

            cost_best = None
            E_best, S_best, N_best = None, None, None

            # existing facts + unit weight for negated literal
            w_I = [1 for _ in I] + [1]
            tstart_lit = time.time()
            for i in model - I:
                remaining_time = timeout - (time.time() - tstart_exp1)

                hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                            explained_literal=i,
                                            add_weights=w_I,
                                            timeout=remaining_time,
                                            postponed_omus=False
                                            )

                if hs is None:
                    timedout = True
                    break

                assert len(hs) > 0, "OMUS shoudl be non empty"

                # explaining facts
                E_i = [ci for ci in explanation if ci in I_cnf]

                # constraint used ('and not ci in E_i': dont repeat unit clauses)
                S_i = [ci for ci in explanation if ci in o.soft_clauses and ci not in E_i]
                S_hs = [o.soft_clauses.index(si) for si in S_i]
                N_i = {i}
                cost_explanation = cost((E_i, S_hs), o.soft_weights, None, None, None)

                # print(f"\n\t\tCandidate explanation for {i} \t\t {E_i} /\\ {S_i} => {N_i} ({cost_explanation})\n")

                if cost_best is None or cost_explanation < cost_best:
                    E_best, S_best, N_best = E_i, S_i, N_i
                    cost_best = cost_explanation


            # post-processing the MSSes
            keep = set()
            for (m1, m1_model) in o.MSSes:
                keep_m1 = True
                for (m2, _) in o.MSSes:
                    if m1 != m2 and m1 < m2:
                        keep_m1 = False
                if keep_m1:
                    keep.add((m1, m1_model))
            o.MSSes = keep

            if timedout:
                results[filename]['OmusIncr']['exec_times'].append('timeout')
                break

            tend_lit = time.time()
            results[filename]['OmusIncr']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['OmusIncr']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['OmusIncr']['greedy'].append(o.greedy_steps[-1])
            results[filename]['OmusIncr']['incr'].append(o.incremental_steps[-1])
            results[filename]['OmusIncr']['opt'].append(o.optimal_steps[-1])
            # post-processing the MSSes

            New_info = optimalPropagate(o.hard_clauses + E_best + S_best, I)
            N_best = New_info.intersection(model) - I

            # add new info
            I = I | N_best
            I_cnf += [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]

        print(f'{filename}: Writing OmusIncr... to \n\t\t', outputDir + filename.replace('.cnf', '') + '_OmusIncr_' + outputFile, '\n')
        with open(outputDir + 'OmusIncr/' + filename.replace('.cnf', '')  + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusIncr'], fp)

        'OmusIncrPost'

        print(f'{filename}: Starting OmusIncrPost...\n')
        I = set()
        I_cnf = [frozenset({lit}) for lit in I]

        w_I = [1 for _ in I] + [1]

        o.reuse_mss = True
        timedout = False
        o.MSSes= set()
        o.MSS_sizes = []

        tstart_exp1 = time.time()
        for j in range(n_literals):

            cost_best = None
            E_best, S_best, N_best = None, None, None

            # existing facts + unit weight for negated literal
            w_I = [1 for _ in I] + [1]
            tstart_lit = time.time()
            for i in model - I:
                remaining_time = timeout - (time.time() - tstart_exp1)

                hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                            explained_literal=i,
                                            add_weights=w_I,
                                            timeout=remaining_time,
                                            postponed_omus=True
                                            )

                if hs is None:
                    timedout = True
                    break

                assert len(hs) > 0, "OMUS shoudl be non empty"

                # explaining facts
                E_i = [ci for ci in explanation if ci in I_cnf]

                # constraint used ('and not ci in E_i': dont repeat unit clauses)
                S_i = [ci for ci in explanation if ci in o.soft_clauses and ci not in E_i]
                S_hs = [o.soft_clauses.index(si) for si in S_i]
                N_i = {i}
                cost_explanation = cost((E_i, S_hs), o.soft_weights, None, None, None)

                # print(f"\n\t\tCandidate explanation for {i} \t\t {E_i} /\\ {S_i} => {N_i} ({cost_explanation})\n")

                if cost_best is None or cost_explanation < cost_best:
                    E_best, S_best, N_best = E_i, S_i, N_i
                    cost_best = cost_explanation


            if timedout:
                results[filename]['OmusIncrPost']['exec_times'].append('timeout')
                break
            # post-processing the MSSes
            keep = set()
            for (m1, m1_model) in o.MSSes:
                keep_m1 = True
                for (m2, _) in o.MSSes:
                    if m1 != m2 and m1 < m2:
                        keep_m1 = False
                if keep_m1:
                    keep.add((m1, m1_model))
            o.MSSes = keep

            tend_lit = time.time()
            results[filename]['OmusIncrPost']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['OmusIncrPost']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['OmusIncrPost']['greedy'].append(o.greedy_steps[-1])
            results[filename]['OmusIncrPost']['incr'].append(o.incremental_steps[-1])
            results[filename]['OmusIncrPost']['opt'].append(o.optimal_steps[-1])
            # post-processing the MSSes

            New_info = optimalPropagate(o.hard_clauses + E_best + S_best, I)
            N_best = New_info.intersection(model) - I

            # add new info
            I = I | N_best
            I_cnf += [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]


        print(f'{filename}: Writing _OmusIncrPost_... to \n\t\t', outputDir + filename.replace('.cnf', '') + '_OmusIncrPost_' + outputFile, '\n')
        with open(outputDir + 'OmusIncrPost/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusIncrPost'], fp)

        # 'OmusIncrPost warm start'
        print(f'{filename}: Starting OmusIncrPost warm start...\n')
        o.reuse_mss = True
        timedout = False
        o.MSSes= set()
        o.MSS_sizes = []

        best_costs = dict({i: 9999999 for i in model - I})

        base_F = set(range(len(o.soft_clauses)))
        # F = base_F | set({o.softClauseIdxs[frozenset({-i})] for i in model - I})
        # o.MSSes.add((o.fullMss, frozenset(model)))
        print("Seeding")
        for i in model - I:
            o.clauses = o.soft_clauses + [frozenset({-i})]
            o.weights = o.soft_weights + [1]
            F_prime = set({o.softClauseIdxs[frozenset({-i})]})

            MSS, MSS_Model = o.grow(F_prime, set())

            o.MSSes.add((frozenset(MSS), frozenset(MSS_Model)))

            # -- precompute some hitting sets for a rough idea on the costs
            w_I = [1 for _ in I] + [1]

        tstart_exp1 = time.time()

        I = set()
        I_cnf = [frozenset({lit}) for lit in I]
        w_I = [1 for _ in I] + [1]

        for j in range(n_literals):
            print(f'\t Explaining literal {j+1}/[{n_literals}]...\n')
            cost_best = None
            E_best, S_best, N_best = None, None, None

            # existing facts + unit weight for negated literal
            w_I = [1 for _ in I] + [1]
            tstart_lit = time.time()
            for i in model - I:
                remaining_time = timeout - (time.time() - tstart_exp1)

                hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                            explained_literal=i,
                                            add_weights=w_I,
                                            timeout=remaining_time,
                                            postponed_omus=True,
                                            best_cost=cost_best
                                            )

                if hs is None and time.time() - tstart_exp1 > timeout:
                    timedout = True
                    break
                elif hs is None:
                    best_costs[i] = 1000+explanation
                    continue

                assert len(hs) > 0, "OMUS shoudl be non empty"

                # explaining facts
                E_i = [ci for ci in explanation if ci in I_cnf]

                # constraint used ('and not ci in E_i': dont repeat unit clauses)
                S_i = [ci for ci in explanation if ci in o.soft_clauses and ci not in E_i]
                S_hs = [o.soft_clauses.index(si) for si in S_i]
                N_i = {i}
                cost_explanation = cost((E_i, S_hs), o.soft_weights, None, None, None)
                best_costs[i] = min([cost_explanation, best_costs[i]])

                if cost_best is None or cost_explanation < cost_best:
                    E_best, S_best, N_best = E_i, S_i, N_i
                    cost_best = cost_explanation

            if timedout:
                results[filename]['OmusIncrPostWarm']['exec_times'].append('timeout')
                break
            # post-processing the MSSes
            keep = set()
            for (m1, m1_model) in o.MSSes:
                keep_m1 = True
                for (m2, _) in o.MSSes:
                    if m1 != m2 and m1 < m2:
                        keep_m1 = False
                if keep_m1:
                    keep.add((m1, m1_model))
            o.MSSes = keep

            tend_lit = time.time()
            print(o.hs_sizes[-1])
            print(o.greedy_steps[-1])
            print(o.incremental_steps[-1])
            print(o.optimal_steps[-1])
            results[filename]['OmusIncrPostWarm']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['OmusIncrPostWarm']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['OmusIncrPostWarm']['greedy'].append(o.greedy_steps[-1])
            results[filename]['OmusIncrPostWarm']['incr'].append(o.incremental_steps[-1])
            results[filename]['OmusIncrPostWarm']['opt'].append(o.optimal_steps[-1])
            # post-processing the MSSes

            New_info = optimalPropagate(o.hard_clauses + E_best + S_best, I)
            N_best = New_info.intersection(model) - I

            # add new info
            I = I | N_best
            I_cnf += [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]

        print(f'{filename}: Writing _OmusIncrPostWarm_... to \n\t\t', outputDir + filename.replace('.cnf', '') + '_OmusIncrPostWarm_' + outputFile, '\n')
        with open(outputDir +'OmusIncrPostWarm/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusIncrPostWarm'], fp)

        del o

def experiment2_omus(sd, timeout):

    results = {
        'filename': 'origin',
        'extension':'maxsat',
        'exec_times':[],
        'setup':'omus'
    }

    parameters={'extension': 'maxsat','output': 'log.json'}
    (bij, trans, clues), (bv_clues, bv_trans, bv_bij), rels = originProblem()

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))

    hard_clauses = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_clues]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_bij]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_trans]

    # print(maxPropagate(hard_clauses + soft_clauses))

    soft_weights = [100 for clause in bv_clues] + \
              [60 for clause in bv_trans] + \
              [60 for clause in bv_bij]

    unknown_facts = set()
    for rel in rels:
        # print(rel.df)
        for item in rel.df.values:
            unknown_facts |= set(i.name+1 for i in item)
    # print(soft_clauses)

    clues=set(i for i in range(len(bv_clues)))
    bij=set(i for i in range(len(bv_clues), len(bv_clues)+len(bv_bij)))
    trans=set(i for i in range(len(bv_bij), len(bv_clues)+len(bv_bij)+len(trans)))

    I0 = set()
    I = set()
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses

    # # TODO: match fact with table element from rels

    I_cnf = [frozenset({lit}) for lit in I0]

    I_end = maxPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)
    # print(len(explainable_facts))

    # explanation sequence
    expl_seq = []

    o = OMUSBase(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=I_end,
        soft_weights=soft_weights,
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=False,
        clues=clues,
        trans=trans,
        bij=bij)

    tstart_o1 = time.time()
    timedout = False

    while len(explainable_facts - I) > 0:
        print("Remaining facts:", len(explainable_facts - I))
        cost_best = None
        E_best, S_best, N_best = None, None, None

        # existing facts + unit weight for negated literal
        w_I = [1 for _ in I] + [1]
        t_start_lit = time.time()
        for i in explainable_facts - I:
            remaining_time = timeout - (time.time() - tstart_o1)
            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                        explained_literal=i,
                                        add_weights=w_I,
                                        postponed_omus=False,
                                        timeout=remaining_time)
            # DEBUG INFO
            if hs is None and time.time() - tstart_o1 > timeout:
                timedout = True
                break
            # explaining facts
            E_i = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in explanation if ci in soft_clauses and ci not in E_i]
            S_hs = [soft_clauses.index(si) for si in S_i]

            # new fact
            N_i = {i}

            cost_explanation = cost((E_i, S_hs), soft_weights, clues, trans, bij)

            # print(f"\n\t\tCandidate explanation for {i} \t\t {E_i} /\\ {S_i} => {N_i} ({cost_explanation})\n")

            if cost_best is None or cost_explanation < cost_best:
                E_best, S_best, N_best = E_i, S_i, N_i
                cost_best = cost_explanation

        if timedout:
            results['exec_times'].append('timeout')
            break
        else:
            t_end_lit = time.time()
            results['exec_times'].append(round(t_end_lit-t_start_lit, 3))

        New_info = optimalPropagate(hard_clauses + E_best + S_best, I)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        I_cnf += [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]



    today = date.today().strftime("%Y_%m_%d")

    outputDir = 'data/experiment2/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    with open(outputDir +'Omus' + outputFile , 'w') as fp:
        json.dump(results, fp)
    del o

def experiment2_omusIncr(sd, timeout):
    
    results = {
        'filename': 'origin',
        'extension':'maxsat',
        'exec_times':[],
        'setup':'omusIncr'
    }

    parameters={'extension': 'maxsat','output': 'log.json'}
    (bij, trans, clues), (bv_clues, bv_trans, bv_bij), rels = originProblem()

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))

    hard_clauses = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_clues]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_bij]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_trans]

    # print(maxPropagate(hard_clauses + soft_clauses))

    soft_weights = [20 for clause in bv_clues] + \
              [5 for clause in bv_trans] + \
              [5 for clause in bv_bij]

    unknown_facts = set()
    for rel in rels:
        # print(rel.df)
        for item in rel.df.values:
            unknown_facts |= set(i.name+1 for i in item)
    # print(soft_clauses)

    clues=set(i for i in range(len(bv_clues)))
    bij=set(i for i in range(len(bv_clues), len(bv_clues)+len(bv_bij)))
    trans=set(i for i in range(len(bv_bij), len(bv_clues)+len(bv_bij)+len(trans)))

    I0 = set()
    I = set()
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses

    # # TODO: match fact with table element from rels

    I_cnf = [frozenset({lit}) for lit in I0]

    I_end = maxPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)

    # explanation sequence
    expl_seq = []

    o = OMUSBase(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=I_end,
        soft_weights=soft_weights,
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=True,
        clues=clues,
        trans=trans,
        bij=bij)

    tstart_o1 = time.time()
    timedout = False

    while len(explainable_facts - I) > 0:
        print("Remaining facts:", len(explainable_facts - I))
        cost_best = None
        E_best, S_best, N_best = None, None, None

        # existing facts + unit weight for negated literal
        w_I = [1 for _ in I] + [1]
        t_start_lit = time.time()
        for i in explainable_facts - I:
            remaining_time = timeout - (time.time() - tstart_o1)
            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                        explained_literal=i,
                                        add_weights=w_I,
                                        postponed_omus=False,
                                        timeout=remaining_time)
            # DEBUG INFO
            if hs is None and time.time() - tstart_o1 > timeout:
                timedout = True
                break
            # explaining facts
            E_i = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in explanation if ci in soft_clauses and ci not in E_i]
            S_hs = [soft_clauses.index(si) for si in S_i]

            # new fact
            N_i = {i}

            cost_explanation = cost((E_i, S_hs), soft_weights, clues, trans, bij)

            if cost_best is None or cost_explanation < cost_best:
                E_best, S_best, N_best = E_i, S_i, N_i
                cost_best = cost_explanation
        if timedout:
            results['exec_times'].append('timeout')
            break
        else:
            t_end_lit = time.time()
            results['exec_times'].append(round(t_end_lit-t_start_lit, 3))
        New_info = optimalPropagate(hard_clauses + E_best + S_best, I)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        I_cnf += [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]



    today = date.today().strftime("%Y_%m_%d")

    outputDir = 'data/experiment2/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    with open(outputDir +'OmusIncr' + outputFile , 'w') as fp:
        json.dump(results, fp)

    del o
def experiment2_omusPost(sd, timeout):

    results = {
        'filename': 'origin',
        'extension':'maxsat',
        'exec_times':[],
        'setup':'omusPost'
    }

    parameters={'extension': 'maxsat','output': 'log.json'}
    (bij, trans, clues), (bv_clues, bv_trans, bv_bij), rels = originProblem()

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))

    hard_clauses = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_clues]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_bij]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_trans]

    # print(maxPropagate(hard_clauses + soft_clauses))

    soft_weights = [20 for clause in bv_clues] + \
              [5 for clause in bv_trans] + \
              [5 for clause in bv_bij]

    unknown_facts = set()
    for rel in rels:
        for item in rel.df.values:
            unknown_facts |= set(i.name+1 for i in item)
    # print(soft_clauses)

    clues=set(i for i in range(len(bv_clues)))
    bij=set(i for i in range(len(bv_clues), len(bv_clues)+len(bv_bij)))
    trans=set(i for i in range(len(bv_bij), len(bv_clues)+len(bv_bij)+len(trans)))

    I0 = set()
    I = set()
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses

    # # TODO: match fact with table element from rels

    I_cnf = [frozenset({lit}) for lit in I0]

    I_end = maxPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)

    # explanation sequence
    expl_seq = []

    o = OMUSBase(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=explainable_facts,
        soft_weights=[w for w in soft_weights],
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=False)

    tstart_o1 = time.time()
    timedout = False

    while len(explainable_facts - I) > 0:
        print("Remaining facts:", len(explainable_facts - I))
        cost_best = None
        E_best, S_best, N_best = None, None, None

        # existing facts + unit weight for negated literal
        w_I = [1 for _ in I] + [1]
        t_start_lit = time.time()
        for i in explainable_facts - I:
            print(i)
            remaining_time = timeout - (time.time() - tstart_o1)
            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                        explained_literal=i,
                                        add_weights=w_I,
                                        postponed_omus=True,
                                        timeout=remaining_time)

            # DEBUG INFO
            print(hs, explanation)
            if hs is None and time.time() - tstart_o1 > timeout:
                timedout = True
                break
            # explaining facts
            E_i = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in explanation if ci in soft_clauses and ci not in E_i]
            S_hs = [soft_clauses.index(si) for si in S_i]

            # new fact
            N_i = {i}

            cost_explanation = cost((E_i, S_hs), soft_weights, clues, trans, bij)

            if cost_best is None or cost_explanation < cost_best:
                E_best, S_best, N_best = E_i, S_i, N_i
                cost_best = cost_explanation
        if timedout:
            results['exec_times'].append('timeout')
            break
        else:
            t_end_lit = time.time()
            results['exec_times'].append(round(t_end_lit-t_start_lit, 3))

        New_info = optimalPropagate(hard_clauses + E_best + S_best, I)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        I_cnf += [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]


    today = date.today().strftime("%Y_%m_%d")

    outputDir = 'data/experiment2/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    with open(outputDir +'OmusPost' + outputFile , 'w') as fp:
        json.dump(results, fp)

    del o

def experiment2_omusIncrPost(sd, timeout):
 
    results = {
        'filename': 'origin',
        'extension':'maxsat',
        'exec_times':[],
        'setup':'omusIncrPost'
    }

    parameters={'extension': 'maxsat','output': 'log.json'}
    (bij, trans, clues), (bv_clues, bv_trans, bv_bij), rels = originProblem()

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))

    hard_clauses = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_clues]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_bij]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_trans]

    # print(maxPropagate(hard_clauses + soft_clauses))

    soft_weights = [100 for clause in bv_clues] + \
              [60 for clause in bv_trans] + \
              [60 for clause in bv_bij]

    unknown_facts = set()
    for rel in rels:
        # print(rel.df)
        for item in rel.df.values:
            unknown_facts |= set(i.name+1 for i in item)
    # print(soft_clauses)

    clues=set(i for i in range(len(bv_clues)))
    bij=set(i for i in range(len(bv_clues), len(bv_clues)+len(bv_bij)))
    trans=set(i for i in range(len(bv_bij), len(bv_clues)+len(bv_bij)+len(trans)))

    I0 = set()
    I = set()
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses

    # # TODO: match fact with table element from rels

    I_cnf = [frozenset({lit}) for lit in I0]

    print("\n")
    print("\n")
    print("\n")
    print("\n")
    print("Starting propagate")
    t1 = time.time()
    I_end = maxPropagate(cnf, I0)
    t2 = time.time()
    print("Ending propagate", round(t2-t1))
    print("\n")
    print("\n")
    print("\n")
    print("\n")
    # I_end = optimalPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)

    # explanation sequence
    expl_seq = []

    o = OMUSBase(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=I_end,
        soft_weights=soft_weights,
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=True,
        clues=clues,
        trans=trans,
        bij=bij)

    tstart_o1 = time.time()
    timedout = False

    while len(explainable_facts - I) > 0:
        print("Remaining facts:", len(explainable_facts - I))

        cost_best = None
        E_best, S_best, N_best = None, None, None

        # existing facts + unit weight for negated literal
        w_I = [1 for _ in I] + [1]
        t_start_lit = time.time()
        for i in explainable_facts - I:
            remaining_time = timeout - (time.time() - tstart_o1)
            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                        explained_literal=i,
                                        add_weights=w_I,
                                        postponed_omus=True,
                                        timeout=remaining_time)

            # DEBUG INFO
            if hs is None and time.time() - tstart_o1 > timeout:
                timedout = True
                break
            # explaining facts
            E_i = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in explanation if ci in soft_clauses and ci not in E_i]
            S_hs = [soft_clauses.index(si) for si in S_i]

            # new fact
            N_i = {i}

            cost_explanation = cost((E_i, S_hs), soft_weights, clues, trans, bij)

            if cost_best is None or cost_explanation < cost_best:
                E_best, S_best, N_best = E_i, S_i, N_i
                cost_best = cost_explanation

        if timedout:
            results['exec_times'].append('timeout')
            break
        else:
            t_end_lit = time.time()
            results['exec_times'].append(round(t_end_lit-t_start_lit, 3))

        New_info = optimalPropagate(hard_clauses + E_best + S_best, I)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        I_cnf += [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]



        # post-processing the MSSes
        keep = set()
        for (m1, m1_model) in o.MSSes:
            keep_m1 = True
            for (m2, _) in o.MSSes:
                if m1 != m2 and m1 < m2:
                    keep_m1 = False
            if keep_m1:
                keep.add((m1, m1_model))
        o.MSSes = keep

    today = date.today().strftime("%Y_%m_%d")

    outputDir = 'data/experiment2/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    with open(outputDir +'OmusIncrPost' + outputFile , 'w') as fp:
        json.dump(results, fp)

    del o

def experiment2_omusIncrPostWarm(sd, timeout):

    results = {
        'filename': 'origin',
        'extension':'maxsat',
        'exec_times':[],
        'setup':'omusIncrPostWarm'
    }

    parameters={'extension': 'maxsat','output': 'log.json'}
    (bij, trans, clues), (bv_clues, bv_trans, bv_bij), rels = originProblem()

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))

    hard_clauses = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_clues]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_bij]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_trans]

    # print(maxPropagate(hard_clauses + soft_clauses))

    soft_weights = [100 for clause in bv_clues] + \
              [60 for clause in bv_trans] + \
              [60 for clause in bv_bij]

    unknown_facts = set()
    for rel in rels:
        # print(rel.df)
        for item in rel.df.values:
            unknown_facts |= set(i.name+1 for i in item)
    # print(soft_clauses)

    clues=set(i for i in range(len(bv_clues)))
    bij=set(i for i in range(len(bv_clues), len(bv_clues)+len(bv_bij)))
    trans=set(i for i in range(len(bv_bij), len(bv_clues)+len(bv_bij)+len(trans)))

    I0 = set()
    I = set()
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses

    # # TODO: match fact with table element from rels

    I_cnf = [frozenset({lit}) for lit in I0]

    I_end = maxPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)

    # explanation sequence
    expl_seq = []

    o = OMUSBase(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=I_end,
        soft_weights=soft_weights,
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=True,
        clues=clues,
        trans=trans,
        bij=bij)

    best_costs = dict({i: 9999999 for i in explainable_facts - I})
    # add full theory without negation literal
    # o.MSSes.add((o.fullMss, frozenset(I_end)))
    base_F = set(range(len(o.soft_clauses)))

    for i in explainable_facts - I:

        F = base_F | set({o.softClauseIdxs[frozenset({-i})]})

        # Only negation of literal inside
        o.clauses = o.soft_clauses + [frozenset({-i})]
        o.weights = o.soft_weights + [1]
        # F_prime = last variable
        F_prime = set({len(soft_clauses)})

        MSS, MSS_Model = o.grow(F_prime, {-i})

        # build MSS with correct indexes
        mssIdxs = frozenset(o.softClauseIdxs[o.clauses[id]] for id in MSS&F)

        o.MSSes.add((mssIdxs, frozenset(MSS_Model)))
    
    tstart_o1 = time.time()
    timedout = False
    while len(explainable_facts - I) > 0:
        print("Remaining facts:", len(explainable_facts - I))
        assert len(I) == len(I_cnf)

        cost_best = None
        E_best, S_best, N_best = None, None, None

        # existing facts + unit weight for negated literal
        w_I = [1 for _ in I] + [1]
        t_start_lit = time.time()
        for id, i in enumerate(sorted(explainable_facts - I, key=lambda i: best_costs[i])):
            print('Trying to explain ', i )
            remaining_time = timeout - (time.time() - tstart_o1)
            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                            explained_literal=i,
                                            add_weights=w_I,
                                            best_cost=cost_best,
                                            timeout=remaining_time)
            # print(hs, explanation)
            if hs is None and time.time() - tstart_o1 > timeout:
                timedout = True
                break
            elif hs is None:
                # HACK: store my_cost of this guy, for sorting next iter
                best_costs[i] = 1000+explanation
                continue

            assert len(hs) > 0, "OMUS shoudl be non empty"

            # explaining facts
            E_i = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in explanation if ci in soft_clauses and ci not in E_i]
            S_hs = [soft_clauses.index(si) for si in S_i]

            # new fact
            N_i = {i}

            cost_explanation = cost((E_i, S_hs), soft_weights, clues, trans, bij)
            best_costs[i] = min([cost_explanation, best_costs[i]])

            if cost_best is None or cost_explanation < cost_best:
                E_best, S_best, N_best = E_i, S_i, N_i
                cost_best = cost_explanation

        if timedout:
            results['exec_times'].append('timeout')
            break
        else:
            t_end_lit = time.time()
            results['exec_times'].append(round(t_end_lit-t_start_lit, 3))

        # post-processing the MSSes
        keep = set()
        for (m1, m1_model) in o.MSSes:
            keep_m1 = True
            for (m2, _) in o.MSSes:
                if m1 != m2 and m1 < m2:
                    keep_m1 = False
            if keep_m1:
                keep.add((m1, m1_model))
        o.MSSes = keep

        New_info = optimalPropagate(hard_clauses + E_best + S_best, I)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        I_cnf += [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]

    today = date.today().strftime("%Y_%m_%d")

    outputDir = 'data/experiment2/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    with open(outputDir +'omusIncrPostWarm' + outputFile , 'w') as fp:
        json.dump(results, fp)
    del o

def experiment2_omusConstr(sd, timeout):

    results = {
        'filename': 'origin',
        'extension':'maxsat',
        'exec_times':[],
        'setup':'omusConstr'
    }

    parameters={'extension': 'maxsat','output': 'log.json'} 

    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    # model constraints
    (bij, trans, clues), (bv_clues, bv_trans, bv_bij), rels = originProblem()

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))

    hard_clauses = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_clues]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_bij]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_trans]

    # print(maxPropagate(hard_clauses + soft_clauses))
    soft_weights = [100 for clause in bv_clues] + \
              [60 for clause in bv_trans] + \
              [60 for clause in bv_bij]

    unknown_facts = set()
    for rel in rels:
        # print(rel.df)
        for item in rel.df.values:
            unknown_facts |= set(i.name+1 for i in item)
    # print(soft_clauses)

    # initial interpretation
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses
    else:
        raise Exception("omusExplain2: hard and soft clauses can not be None")

    I0 = set()
    I = I0

    I_cnf = [frozenset({lit}) for lit in I0]

    all_unk = unknown_facts | set(-l for l in unknown_facts)
    I_end = optimalPropagate(cnf, I0, focus=all_unk)
    # I_end = maxPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)

    # explanation sequence
    expl_seq = []

    o = OMUS(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=explainable_facts,
        soft_weights=soft_weights,
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=False)

    total_exec_start = time.time()
    while len(explainable_facts - I) > 0:
        print("Remaining facts:", len(explainable_facts - I))
        t_start_lit = time.time()
        remaining_time = timeout - (time.time() - total_exec_start)
        hs, explanation = o.omusConstr(do_incremental=False, greedy=False, timeout=remaining_time)

        if hs is None:
            results['exec_times'].append('timeout')
            break

        # explaining facts
        E_best = [ci for ci in explanation if ci in I_cnf]

        # constraint used ('and not ci in E_i': dont repeat unit clauses)
        S_best = [ci for ci in explanation if ci in soft_clauses and ci not in E_best]

        #print("optimal:", hard_clauses, E_best, S_best, I)
        New_info = optimalPropagate(hard_clauses + E_best + S_best, I, focus=all_unk)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        new_cnf = [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]
        I_cnf += new_cnf

        expl_seq.append((E_best, S_best, N_best))

        o.updateObjWeightsInterpret(I)

        t_end_lit = time.time()
        results['exec_times'].append(round(t_end_lit-t_start_lit, 3))

    today = date.today().strftime("%Y_%m_%d")

    outputDir = 'data/experiment2/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    with open(outputDir +'omusConstr' + outputFile , 'w') as fp:
        json.dump(results, fp)

def experiment2_omusConstrWarm(sd, timeout):

    results = {
        'filename': 'origin',
        'extension':'maxsat',
        'exec_times':[],
        'setup':'omusConstrWarm'
    }

    parameters={'extension': 'maxsat','output': 'log.json'} 

    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    # model constraints
    (bij, trans, clues), (bv_clues, bv_trans, bv_bij), rels = originProblem()

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))

    hard_clauses = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_clues]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_bij]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_trans]

    # print(maxPropagate(hard_clauses + soft_clauses))
    soft_weights = [100 for clause in bv_clues] + \
              [60 for clause in bv_trans] + \
              [60 for clause in bv_bij]

    unknown_facts = set()
    for rel in rels:
        # print(rel.df)
        for item in rel.df.values:
            unknown_facts |= set(i.name+1 for i in item)
    # print(soft_clauses)

    # initial interpretation
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses
    else:
        raise Exception("omusExplain2: hard and soft clauses can not be None")

    I0 = set()
    I = I0

    I_cnf = [frozenset({lit}) for lit in I0]

    all_unk = unknown_facts | set(-l for l in unknown_facts)
    I_end = optimalPropagate(cnf, I0, focus=all_unk)
    # I_end = maxPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)

    # explanation sequence
    expl_seq = []

    o = OMUS(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=explainable_facts,
        soft_weights=soft_weights,
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=False)

    F = frozenset(range(o.nClauses))
    # each -i
    seedable = set(-i for i in explainable_facts-I0)

    while len(seedable) > 0:
        i = next(iter(seedable))

        F_prime = set([o.softClauseIdxs[frozenset({i})]])
        MSS, MSS_Model = o.grow(F_prime, I0|{i})

        C = F - MSS
        o.addSetGurobiOmusConstr(C)

        other_seeds = seedable&frozenset(MSS_Model)
        #print("mss",i,":",MSS, other_seeds,"C",C)
        # no need to 'grow' a literal that already has an MSS
        seedable -= other_seeds

    total_exec_start = time.time()
    while len(explainable_facts - I) > 0:
        print("Remaining facts:", len(explainable_facts - I))
        t_start_lit = time.time()
        remaining_time = timeout - (time.time() - total_exec_start)
        hs, explanation = o.omusConstr(do_incremental=False, greedy=False, timeout=remaining_time)

        if hs is None:
            results['exec_times'].append('timeout')
            break

        # explaining facts
        E_best = [ci for ci in explanation if ci in I_cnf]

        # constraint used ('and not ci in E_i': dont repeat unit clauses)
        S_best = [ci for ci in explanation if ci in soft_clauses and ci not in E_best]

        #print("optimal:", hard_clauses, E_best, S_best, I)
        New_info = optimalPropagate(hard_clauses + E_best + S_best, I, focus=all_unk)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        new_cnf = [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]
        I_cnf += new_cnf

        expl_seq.append((E_best, S_best, N_best))

        o.updateObjWeightsInterpret(I)

        t_end_lit = time.time()
        results['exec_times'].append(round(t_end_lit-t_start_lit, 3))

    today = date.today().strftime("%Y_%m_%d")

    outputDir = 'data/experiment2/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    with open(outputDir +'omusConstrWarm' + outputFile , 'w') as fp:
        json.dump(results, fp)

def experiment2_OmusConstrIncr(sd, timeout):

    results = {
        'filename': 'origin',
        'extension':'maxsat',
        'exec_times':[],
        'setup':'OmusConstrIncr'
    }

    parameters={'extension': 'maxsat','output': 'log.json'} 

    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    # model constraints
    (bij, trans, clues), (bv_clues, bv_trans, bv_bij), rels = originProblem()

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))

    hard_clauses = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_clues]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_bij]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_trans]

    # print(maxPropagate(hard_clauses + soft_clauses))
    soft_weights = [100 for clause in bv_clues] + \
              [60 for clause in bv_trans] + \
              [60 for clause in bv_bij]

    unknown_facts = set()
    for rel in rels:
        # print(rel.df)
        for item in rel.df.values:
            unknown_facts |= set(i.name+1 for i in item)
    # print(soft_clauses)

    # initial interpretation
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses
    else:
        raise Exception("omusExplain2: hard and soft clauses can not be None")

    I0 = set()
    I = I0

    I_cnf = [frozenset({lit}) for lit in I0]

    all_unk = unknown_facts | set(-l for l in unknown_facts)
    I_end = optimalPropagate(cnf, I0, focus=all_unk)
    # I_end = maxPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)

    # explanation sequence
    expl_seq = []

    o = OMUS(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=explainable_facts,
        soft_weights=soft_weights,
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=True)

    total_exec_start = time.time()
    while len(explainable_facts - I) > 0:
        print("Remaining facts:", len(explainable_facts - I))
        t_start_lit = time.time()
        remaining_time = timeout - (time.time() - total_exec_start)
        hs, explanation = o.omusConstr(do_incremental=True, greedy=True, timeout=remaining_time)

        if hs is None:
            results['exec_times'].append('timeout')
            break

        # explaining facts
        E_best = [ci for ci in explanation if ci in I_cnf]

        # constraint used ('and not ci in E_i': dont repeat unit clauses)
        S_best = [ci for ci in explanation if ci in soft_clauses and ci not in E_best]

        #print("optimal:", hard_clauses, E_best, S_best, I)
        New_info = optimalPropagate(hard_clauses + E_best + S_best, I, focus=all_unk)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        new_cnf = [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]
        I_cnf += new_cnf

        expl_seq.append((E_best, S_best, N_best))

        o.updateObjWeightsInterpret(I)

        t_end_lit = time.time()
        results['exec_times'].append(round(t_end_lit-t_start_lit, 3))

    today = date.today().strftime("%Y_%m_%d")

    outputDir = 'data/experiment2/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    with open(outputDir +'omusConstrIncr' + outputFile , 'w') as fp:
        json.dump(results, fp)

def experiment2_OmusConstrIncrWarm(sd, timeout):

    results = {
        'filename': 'origin',
        'extension':'maxsat',
        'exec_times':[],
        'setup':'OmusConstrIncrWarm'
    }

    parameters={'extension': 'maxsat','output': 'log.json'} 

    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    # model constraints
    (bij, trans, clues), (bv_clues, bv_trans, bv_bij), rels = originProblem()

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))

    hard_clauses = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_clues]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_bij]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_trans]

    # print(maxPropagate(hard_clauses + soft_clauses))
    soft_weights = [100 for clause in bv_clues] + \
              [60 for clause in bv_trans] + \
              [60 for clause in bv_bij]

    unknown_facts = set()
    for rel in rels:
        # print(rel.df)
        for item in rel.df.values:
            unknown_facts |= set(i.name+1 for i in item)
    # print(soft_clauses)

    # initial interpretation
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses
    else:
        raise Exception("omusExplain2: hard and soft clauses can not be None")

    I0 = set()
    I = I0

    I_cnf = [frozenset({lit}) for lit in I0]

    all_unk = unknown_facts | set(-l for l in unknown_facts)
    I_end = optimalPropagate(cnf, I0, focus=all_unk)
    # I_end = maxPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)

    # explanation sequence
    expl_seq = []

    o = OMUS(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=explainable_facts,
        soft_weights=soft_weights,
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=True)

    F = frozenset(range(o.nClauses))
    # each -i
    seedable = set(-i for i in explainable_facts-I0)

    while len(seedable) > 0:
        i = next(iter(seedable))

        F_prime = set([o.softClauseIdxs[frozenset({i})]])
        MSS, MSS_Model = o.grow(F_prime, I0|{i})

        C = F - MSS
        o.addSetGurobiOmusConstr(C)

        other_seeds = seedable&frozenset(MSS_Model)
        #print("mss",i,":",MSS, other_seeds,"C",C)
        # no need to 'grow' a literal that already has an MSS
        seedable -= other_seeds

    total_exec_start = time.time()
    while len(explainable_facts - I) > 0:
        print("Remaining facts:", len(explainable_facts - I))
        t_start_lit = time.time()
        remaining_time = timeout - (time.time() - total_exec_start)
        hs, explanation = o.omusConstr(do_incremental=True, greedy=True, timeout=remaining_time)

        if hs is None:
            results['exec_times'].append('timeout')
            break

        # explaining facts
        E_best = [ci for ci in explanation if ci in I_cnf]

        # constraint used ('and not ci in E_i': dont repeat unit clauses)
        S_best = [ci for ci in explanation if ci in soft_clauses and ci not in E_best]

        #print("optimal:", hard_clauses, E_best, S_best, I)
        New_info = optimalPropagate(hard_clauses + E_best + S_best, I, focus=all_unk)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        new_cnf = [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]
        I_cnf += new_cnf

        expl_seq.append((E_best, S_best, N_best))

        o.updateObjWeightsInterpret(I)

        t_end_lit = time.time()
        results['exec_times'].append(round(t_end_lit-t_start_lit, 3))

    today = date.today().strftime("%Y_%m_%d")

    outputDir = 'data/experiment2/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    with open(outputDir +'OmusConstrIncrWarm' + outputFile , 'w') as fp:
        json.dump(results, fp)

def experiment3(sd, timeout):
    parameters={'extension': 'maxsat','output': 'log.json'} 

    # model constraints
    (bij, trans, clues), (bv_clues, bv_trans, bv_bij), rels = originProblem()

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))

    hard_clauses = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_clues]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_bij]
    soft_clauses += [frozenset({bv1.name + 1}) for bv1 in bv_trans]

    bv_clues_soft_clauses = [frozenset({bv1.name + 1}) for bv1 in bv_clues]
    bv_bij_soft_clauses = [frozenset({bv1.name + 1}) for bv1 in bv_bij]
    bv_trans_soft_clauses = [frozenset({bv1.name + 1}) for bv1 in bv_trans]

    # print(maxPropagate(hard_clauses + soft_clauses))
    soft_weights = [100 for clause in bv_clues] + \
              [100 for clause in bv_trans] + \
              [20 for clause in bv_bij]

    unknown_facts = set()
    for rel in rels:
        # print(rel.df)
        for item in rel.df.values:
            unknown_facts |= set(i.name+1 for i in item)

    # initial interpretation
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses
    else:
        raise Exception("omusExplain2: hard and soft clauses can not be None")

    I0 = set()
    I = I0

    I_cnf = [frozenset({lit}) for lit in I0]

    all_unk = unknown_facts | set(-l for l in unknown_facts)
    I_end = optimalPropagate(cnf, I0, focus=all_unk)
    # I_end = maxPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)

    # explanation sequence
    expl_seq = []

    o = OMUS(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=explainable_facts,
        soft_weights=soft_weights,
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=False,
        clues=set(i for i in range(len(bv_clues))),
        bij=set(i for i in range(len(bv_clues), len(bv_clues) + len(bv_bij))),
        trans=set(i for i in range(len(bv_clues) + len(bv_bij), len(bv_clues) + len(bv_bij) + len(bv_trans))))

    F = frozenset(range(o.nClauses))
    # each -i
    seedable = set(-i for i in explainable_facts-I0)

    while len(seedable) > 0:
        i = next(iter(seedable))

        F_prime = set([o.softClauseIdxs[frozenset({i})]])
        MSS, MSS_Model = o.grow(F_prime, I0|{i})

        C = F - MSS
        o.addSetGurobiOmusConstr(C)

        other_seeds = seedable&frozenset(MSS_Model)
        seedable -= other_seeds

    t_start_problem = time.time()
    while len(explainable_facts - I) > 0:
        print("Remaining facts:", len(explainable_facts - I))
        hs, explanation = o.omusConstr(do_incremental=False, greedy=False)

        # explaining facts
        E_best = [ci for ci in explanation if ci in I_cnf]

        # constraint used ('and not ci in E_i': dont repeat unit clauses)
        S_best = [ci for ci in explanation if ci in soft_clauses and ci not in E_best]

        #print("optimal:", hard_clauses, E_best, S_best, I)
        New_info = optimalPropagate(hard_clauses + E_best + S_best, I, focus=all_unk)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        new_cnf = [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]
        I_cnf += new_cnf

        expl_seq.append((E_best, S_best, N_best))

        constraint_type = None
        if len(S_best) == 1:
            if S_best[0] in bv_bij_soft_clauses:
                constraint_type = 'bijectivity'
            elif S_best[0] in bv_trans_soft_clauses:
                constraint_type = 'transitivity'
            elif S_best[0] in bv_clues_soft_clauses:
                constraint_type = 'clue'
            else:
                constraint_type= 'unknown'
        else:
            nClues = sum([1 if c in bv_clues_soft_clauses else 0 for c in S_best])
            nBij = sum([1 if c in bv_bij_soft_clauses else 0 for c in S_best])
            nTrans = sum([1 if c in bv_trans_soft_clauses else 0 for c in S_best])
            if nClues > 1 and (nBij+nTrans) == 0:
                constraint_type = 'multiple-clues'
            elif nBij+nTrans > 1 and (nClues == 0):
                constraint_type = 'multiple-constraints'
            else:
                constraint_type = 'clue+constraints'
        print(constraint_type, S_best)

        o.updateObjWeightsInterpret(I)

    t_end_problem = time.time()
    results = {
        'tot_exec_time' : round(t_end_problem - t_start_problem, 3),
        'explanations': []
    }

    for (E_best, S_best, N_best) in expl_seq:
        nClues = sum([1 if c in bv_clues_soft_clauses else 0 for c in S_best])
        nBij = sum([1 if c in bv_bij_soft_clauses else 0 for c in S_best])
        nTrans = sum([1 if c in bv_trans_soft_clauses else 0 for c in S_best])
        constraint_type = None
        if len(S_best) == 1:
            if S_best[0] in bv_bij_soft_clauses:
                constraint_type = 'bijectivity'
            elif S_best[0] in bv_trans_soft_clauses:
                constraint_type = 'transitivity'
            elif S_best[0] in bv_clues_soft_clauses:
                constraint_type = 'clue'
            else:
                constraint_type= 'unknown'
        else:
            if nClues > 1 and (nBij+nTrans) == 0:
                constraint_type = 'multiple-clues'
            elif nBij+nTrans > 1 and (nClues == 0):
                constraint_type = 'multiple-constraints'
            else:
                constraint_type = 'clue+constraints'

        results['explanations'].append({
            'clue': constraint_type,
            'facts': len(E_best),
            'derivations':len(N_best),
            'constraints': [list(c) for c in S_best],
            'nClues':nClues,
            'nBij':nBij,
            'nTrans':nTrans
        })


    today = date.today().strftime("%Y_%m_%d")

    outputDir = 'data/experiment3/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    with open(outputDir +'explanations' + outputFile , 'w') as fp:
        json.dump(results, fp)

def experiment2(sd, timeout):

    # print("Starting experiment2_omusConstrWarm")
    # experiment2_omusConstrWarm(sd, timeout=timeout)
    # print("Ending experiment2_omusConstrWarm")

    # print("Starting omusConstr")
    # experiment2_omusConstr(sd, timeout=timeout)
    # print("Ending omusConstr")

    # print("Starting experiment2_OmusConstrIncr")
    # experiment2_OmusConstrIncr(sd, timeout=timeout)
    # print("Ending experiment2_OmusConstrIncr")

    # print("Starting experiment2_OmusConstrIncrWarm")
    # experiment2_OmusConstrIncrWarm(sd, timeout=timeout)
    # print("Ending experiment2_OmusConstrIncrWarm")
    # print("Starting OMUSIncrPost")
    # experiment2_omusIncrPost(sd, timeout=timeout)
    # print("Ending OMUSIncrPost")

    print("Starting OMUSIncrPostWarm")
    experiment2_omusIncrPostWarm(sd, timeout=timeout)
    print("Ending OMUSIncrPostWarm")

    # print("Starting OMUSIncr")
    # experiment2_omusIncr(sd, timeout=timeout)
    # print("Ending OMUSIncr")

    # print("Starting OMUSPost")
    # experiment2_omusPost(sd, timeout=timeout)
    # print("Ending OMUSPost")

    # print("Starting OMUS")
    # experiment2_omus(sd, timeout=timeout)
    # print("Ending OMUS")

def parallelExperiment1():
    fns = [experiment1_OMUS,experiment1_OMUSIncr, experiment1_OMUSPost,experiment1_OMUSIncrPost,experiment1_OMUSIncrPostWarm, experiment1_OMUSIncrWarm]
    # fns = [experiment1_OMUSPost, experiment1_OMUSIncrPost,experiment1_OMUSIncrPostWarm, experiment1_OMUSIncrWarm]
    proc = []
    for fn in fns:
        p = Process(target=fn)
        p.start()
        proc.append(p)
    for p in proc:
        p.join()


def main():
    sd = datetime.now()
    # parallelExperiment1()
    # experiment1_OMUSIncrPostWarm()
    # experiment1(sd)
    # experiment2(sd, timeout=1*HOURS)
    # experiment3(sd, timeout=None)


if __name__ == "__main__":
    main()


