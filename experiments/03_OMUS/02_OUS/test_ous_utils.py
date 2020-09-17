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

sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
sys.path.append('/home/emilio/Documents/cppy_src/')
sys.path.append('/home/emilio/documents/cppy_mysrc/')

# from cppy.solver_interfaces.pysat_tools import
from cppy.model_tools import to_cnf
from cppy import BoolVarImpl, Comparison, Model, Operator, cnf_to_pysat


from multiprocessing import Process

SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES
TIMEOUT_EXP1 = 10 * MINUTES


def runParallel(fns, args):
    procs = []
    for fn, arg in zip(fns, args):
        p = Process(target=fn, args=arg)
        p.start()
        procs.append(p)

    for p in procs:
        p.join()

def experiment1():
    today = date.today().strftime("%Y_%m_%d")
    outputDir = 'data/experiment1/results/'+today + '/'
    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    # setup experiments
    

    # 

    param = OUSParams()

def exp1_instance(params):

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
            parameters={'extension': 'greedy_vertical', 'output': instance.stem + '.json'},
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