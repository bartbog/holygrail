
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
# from cppy.solver_interfaces.pysat_tools import
from cppy.model_tools.to_cnf import *
from cppy import BoolVarImpl, Comparison, Model, Operator, cnf_to_pysat

random.seed(datetime.now())

SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES


def maxPropagate(cnf, I=list()):
    with Solver() as s:
        s.append_formula(cnf, no_return=False)
        solved = s.solve()
        if solved:
            return set(s.get_model())
        else:
            raise "Problem"


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


def get_instances(n=10):
    p = Path('data/experiment1/SW100-8-0/')
    # print(p.exists())
    # for child in p.iterdir():
    #     print(child)
    instances = random.sample([x for x in p.iterdir()], n)
    filenames = [instance.name for instance in instances]
    return instances, filenames



def experiment1(sd):
    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    outputDir = 'data/experiment1/results/'+today + '/'

    filepath = Path(outputDir)
    filepath.mkdir(parents=True, exist_ok=True)

    outputFile = ".json"

    # parameters
    timeout = 1 * MINUTES
    n_literals = 50
    n_instances = 10

    #
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

        configs = ['Omus', 'OmusPost', 'OmusIncr', 'OmusIncrPost',
                   'OmusIncrPostWarm', 'OmusConstr', 'OmusConstrIncr', 'OmusConstrIncrWarm']

        for c in configs:

            filepath = Path(outputDir + c + '/')
            filepath.mkdir(parents=True, exist_ok=True)

            results[filename][c] = {
                'filename':filename.replace('.cnf', ''),
                'exec_times': [],
                'H_sizes': [],
                'greedy':[],
                'incr':[],
                'opt':[],
            }

        cnf = CNF(from_file=instance)

        print(f'{filename}: Starting OMUSConstr...\n')

        o = OMUS(
            modelname='gp2',
            hard_clauses=list(),
            soft_clauses=[frozenset(clause) for clause in cnf.clauses],
            I=model,
            soft_weights=weights[filename],
            parameters={'extension': 'maxsat',
                        'output': instance.stem + '.json'},
        )

        I = set()
        I_cnf = []
        # derived_literals = []

        tstart_o1 = time.time()
        for i in range(n_literals):
            print(f'\t Explaining literal {i+1}/[{n_literals}]...\n')
            remaining_time = timeout - (time.time() - tstart_o1)
            print(remaining_time)
            # OMUS no improvements
            t_start = time.time()
            hs, explanation = o.omusConstr(timeout=remaining_time)
            if hs is None:
                results[filename]['OmusConstr']['exec_times'].append('timeout')
                results[filename]['OmusConstr']['H_sizes'].append(o.hs_sizes[-1])
                results[filename]['OmusConstr']['greedy'].append(o.greedy_steps[-1])
                results[filename]['OmusConstr']['incr'].append(o.incremental_steps[-1])
                results[filename]['OmusConstr']['opt'].append(o.optimal_steps[-1])
                # o.deleteModel()
                break
            t_end = time.time()
            literal = [clause for clause in explanation if len(clause) == 1 and clause in [frozenset({-lit}) for lit in model]]
            print(literal)

            # explaining facts
            E_best = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_best = [ci for ci in explanation if ci in o.soft_clauses and ci not in E_best]

            New_info = optimalPropagate([] + E_best + S_best, I)
            N_best = New_info.intersection(model) - I

            # add new info
            I = I | N_best
            new_cnf = [frozenset({lit})
                       for lit in N_best if frozenset({lit}) not in I_cnf]
            I_cnf += new_cnf

            o.updateObjWeightsInterpret(I)

            results[filename]['OmusConstr']['exec_times'].append(round(t_end-t_start, 3))
            results[filename]['OmusConstr']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['OmusConstr']['greedy'].append(o.greedy_steps[-1])
            results[filename]['OmusConstr']['incr'].append(o.incremental_steps[-1])
            results[filename]['OmusConstr']['opt'].append(o.optimal_steps[-1])

        o.deleteModel()
        del o
        print(f'{filename}: Writing OMUSConstr... to \n\t\t',  outputDir + filename.replace('.cnf', '') + 'OmusConstr_' + outputFile,  '\n')

        with open(outputDir + 'OmusConstr/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusConstr'], fp)

        print(f'{filename}: Starting OmusConstrIncr...\n')
        o2 = OMUS(
            modelname='gp1',
            hard_clauses=list(),
            soft_clauses=[frozenset(clause) for clause in cnf.clauses],
            I=model,
            soft_weights=weights[filename],
            parameters={'extension': 'maxsat',
                        'output': instance.stem + '.json'},
        )

        I = set()
        I_cnf = []
        tstart_o2 = time.time()
        for i in range(n_literals):
            print(f'\t Explaining literal {i+1}/[{n_literals}]...\n')
            remaining_time = timeout - (time.time() - tstart_o2)
            # OMUS no improvements
            t_start = time.time()
            hs, explanation = o2.omusConstr(do_incremental=True, greedy=True, timeout=remaining_time)
            if hs is None:
                results[filename]['OmusConstrIncr']['exec_times'].append('timeout')
                results[filename]['OmusConstrIncr']['H_sizes'].append(o2.hs_sizes[-1])
                results[filename]['OmusConstrIncr']['greedy'].append(o2.greedy_steps[-1])
                results[filename]['OmusConstrIncr']['incr'].append(o2.incremental_steps[-1])
                results[filename]['OmusConstrIncr']['opt'].append(o2.optimal_steps[-1])
                # o.deleteModel()
                break
            t_end = time.time()

            # explaining facts
            E_best = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_best = [ci for ci in explanation if ci in o2.soft_clauses and ci not in E_best]

            New_info = optimalPropagate([] + E_best + S_best, I)
            N_best = New_info.intersection(model) - I

            # add new info
            I = I | N_best
            new_cnf = [frozenset({lit})
                    for lit in N_best if frozenset({lit}) not in I_cnf]
            I_cnf += new_cnf

            o2.updateObjWeightsInterpret(I)

            results[filename]['OmusConstrIncr']['exec_times'].append(round(t_end-t_start, 3))
            results[filename]['OmusConstrIncr']['H_sizes'].append(o2.hs_sizes[-1])
            results[filename]['OmusConstrIncr']['greedy'].append(o2.greedy_steps[-1])
            results[filename]['OmusConstrIncr']['incr'].append(o2.incremental_steps[-1])
            results[filename]['OmusConstrIncr']['opt'].append(o2.optimal_steps[-1])

        o2.deleteModel()
        del o2

        print(f'{filename}: Writing OMUSConstr... to \n\t\t',  outputDir + filename.replace('.cnf', '') + 'OmusConstrIncr_' + outputFile, '\n')

        with open(outputDir + 'OmusConstrIncr/' + filename.replace('.cnf', '') + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusConstrIncr'], fp)

        print(f'{filename}: Starting OmusConstrIncr...\n')
        o3 = OMUS(
            modelname='gp3',
            hard_clauses=list(),
            soft_clauses=[frozenset(clause) for clause in cnf.clauses],
            I=model,
            soft_weights=weights[filename],
            parameters={'extension': 'maxsat',
                        'output': instance.stem + '.json'},
        )
        print(f'\t Seeding....\n')

        tstart_o3 = time.time()
        F = frozenset(range(o3.nClauses))
        seedable = set(-i for i in model)
        while len(seedable) > 0:
            i = next(iter(seedable))

            F_prime = set([o3.softClauseIdxs[frozenset({i})]])
            MSS, MSS_Model = o3.grow(F_prime, set()|{i})

            C = F - MSS
            o3.addSetGurobiOmusConstr(C)

            other_seeds = seedable&frozenset(MSS_Model)
            seedable -= other_seeds

        I = set()
        I_cnf = []
        for i in range(n_literals):
            print(f'\t Explaining literal {i+1}/[{n_literals}]...\n')
            # OMUS no improvements
            remaining_time = timeout - (time.time() - tstart_o3)
            t_start = time.time()
            hs, explanation = o3.omusConstr(do_incremental=True, greedy=True)
            t_end = time.time()
            if hs is None:
                results[filename]['OmusConstrIncrWarm']['exec_times'].append('timeout')
                results[filename]['OmusConstrIncrWarm']['H_sizes'].append(o3.hs_sizes[-1])
                results[filename]['OmusConstrIncrWarm']['greedy'].append(o3.greedy_steps[-1])
                results[filename]['OmusConstrIncrWarm']['incr'].append(o3.incremental_steps[-1])
                results[filename]['OmusConstrIncrWarm']['opt'].append(o3.optimal_steps[-1])
                # o.deleteModel()
                break

            # explaining facts
            E_best = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_best = [ci for ci in explanation if ci in o3.soft_clauses and ci not in E_best]

            New_info = optimalPropagate([] + E_best + S_best, I)
            N_best = New_info.intersection(model) - I

            # add new info
            I = I | N_best
            new_cnf = [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]
            I_cnf += new_cnf

            o3.updateObjWeightsInterpret(I)

            results[filename]['OmusConstrIncrWarm']['exec_times'].append(round(t_end-t_start, 3))
            results[filename]['OmusConstrIncrWarm']['H_sizes'].append(o3.hs_sizes[-1])
            results[filename]['OmusConstrIncrWarm']['greedy'].append(o3.greedy_steps[-1])
            results[filename]['OmusConstrIncrWarm']['incr'].append(o3.incremental_steps[-1])
            results[filename]['OmusConstrIncrWarm']['opt'].append(o3.optimal_steps[-1])


        o3.deleteModel()
        del o3
        print(f'{filename}: Writing OMUSConstr... to \n\t\t', outputDir + filename.replace('.cnf', '') + 'OmusConstrIncrWarm_' + outputFile, '\n')

        with open(outputDir+ 'OmusConstrIncrWarm/' + filename.replace('.cnf', '')  + outputFile , 'w') as fp:
            json.dump(results[filename]['OmusConstrIncrWarm'], fp)

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

            tend_lit = time.time()
            results[filename]['Omus']['exec_times'].append(round(tend_lit-tstart_lit, 3))
            results[filename]['Omus']['H_sizes'].append(o.hs_sizes[-1])
            results[filename]['Omus']['greedy'].append(o.greedy_steps[-1])
            results[filename]['Omus']['incr'].append(o.incremental_steps[-1])
            results[filename]['Omus']['opt'].append(o.optimal_steps[-1])

            if timedout:
                results[filename]['Omus']['exec_times'].append('timeout')
                break
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

        # 'OmusIncrPost'
        print(f'{filename}: Starting OmusIncrPost...\n')
        I = set()
        I_cnf = [frozenset({lit}) for lit in I]
        w_I = [1 for _ in I] + [1]

        o.MSSes= set()
        o.MSS_sizes = []

        o.reuse_mss = True
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
                results[filename]['OmusIncrPost']['exec_times'].append('timeout')
                break

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
        print(model)
        o.reuse_mss = True
        timedout = False
        o.MSSes= set()
        o.MSS_sizes = []

        best_costs = dict({i: 9999999 for i in model - I})
        print(o.weights)
        base_F = set(range(len(o.soft_clauses)))
        F = base_F | set({o.softClauseIdxs[frozenset({-i})] for i in model - I})
        o.MSSes.add((o.fullMss, frozenset(model)))
        print("Seeding")
        for i in model - I:
            o.clauses = o.soft_clauses + [frozenset({-i})]
            o.weights = o.soft_weights + [1] * len(o.I_lits)
            F_prime = set({o.softClauseIdxs[frozenset({-i})]})

            MSS, MSS_Model = o.maxsat_fprime(F_prime, set())

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
                results[filename]['OmusIncrPostWarm']['exec_times'].append('timeout')
                break

            tend_lit = time.time()
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


def experiment2_omus(sd, timeout):
    pass
def experiment2_omusIncr(sd, timeout):
    pass
def experiment2_omusPost(sd, timeout):
    pass
def experiment2_omusIncrPost(sd, timeout):
    pass
def experiment2_omusIncrPostWarm(sd, timeout):
    pass
def experiment2_omusConstr(sd, timeout):
    pass
def experiment2_OmusConstrIncr(sd, timeout):
    pass
def experiment2_OmusConstrIncrWarm(sd, timeout):
    pass

# def experiment3(sd, timeout):
    



def main():
    sd = datetime.now()
    random.seed(sd)
    experiment1(sd)
    # experiment2()
    # experiment3()


if __name__ == "__main__":
    main()


