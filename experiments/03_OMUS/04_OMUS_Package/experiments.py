import json
import random
import time
from datetime import date, datetime
from pathlib import Path

#pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

# omus imports
from omus import OMUS

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

    outputDir = 'data/experiment1/'
    outputFile = today + "_" + now + ".json"

    # parameters
    timeout = 15 * MINUTES
    n_literals = 5
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
        assert sat == True

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
            },
            'omus': {
                'exec_times': [],
                'H_sizes': [],
            },
            'omus_postponed': {
                'exec_times': [],
                'H_sizes': [],
            },
            'omus_incremental': {
                'exec_times': [],
                'H_sizes': [],
            },
            'omus_incremental_postponed': {
                'exec_times': [],
                'H_sizes': [],
            }
        }

        cnf = CNF(from_file=instance)

        o = OMUS(
            hard_clauses=list(),
            soft_clauses=[frozenset(clause) for clause in cnf.clauses],
            I=model,
            bv=None,
            soft_weights=weights[instance],
            parameters={'extension': 'maxsat', 'output': instance.stem + '.json'},
        )

        for lit in instance_literals[instance]:
            # OMUS no improvements
            o.reuse_mss = False
            t_start = time.time()
            hs, explanation = o.omusIncr(I_cnf=list(),
                                        explained_literal=lit,
                                        add_weights=[1],
                                        timeout=timeout,
                                        postponed_omus=False,
                                        )
            t_end = time.time()
            results[filename]['omus']['exec_times'].append(t_end - t_start)
            results[filename]['omus']['H_sizes'].append(len(o.hs_sizes))

            # OMUS postponing optimization
            t_start = time.time()
            hs, explanation = o.omusIncr(I_cnf=list(),
                                        explained_literal=lit,
                                        add_weights=[1],
                                        timeout=timeout,
                                        postponed_omus=True,
                                        )
            t_end = time.time()
            results[filename]['omus_postponed']['exec_times'].append(t_end - t_start)
            results[filename]['omus_postponed']['H_sizes'].append(len(o.hs_sizes))

            # OMUS incremental 
            o.reuse_mss = True
            t_start = time.time()
            hs, explanation = o.omusIncr(I_cnf=list(),
                                        explained_literal=lit,
                                        add_weights=[1],
                                        timeout=timeout,
                                        postponed_omus=False,
                                        )
            t_end = time.time()
            results[filename]['omus_incremental']['exec_times'].append(t_end - t_start)
            results[filename]['omus_incremental']['H_sizes'].append(len(o.hs_sizes))

            # OMUS incremental + postponing optimization
            o.reuse_mss = True
            t_start = time.time()
            hs, explanation = o.omusIncr(I_cnf=list(),
                                        explained_literal=lit,
                                        add_weights=[1],
                                        timeout=timeout,
                                        postponed_omus=True,
                                        )
            t_end = time.time()
            results[filename]['omus_incremental_postponed']['exec_times'].append(t_end - t_start)
            results[filename]['omus_incremental_postponed']['H_sizes'].append(len(o.hs_sizes))

    with open(outputDir + outputFile, 'w') as file:
        file.write(json.dumps(results))
    # return o.export_results('results/puzzles/origin/', today + "_" + now + ".json")
# start 15:12
def main():
    sd = datetime.now()
    random.seed(sd)
    experiment1(sd)
    # experiment2()
    # experiment3()

if __name__ == "__main__":
    main()

# def experiment2():
#     timeout = 5 * HOURS

#     # setup origin puzzle
#     origin_puzzle = ....

#     # OMUS no improvements
#     csp

#     # OMUS postponing optimization
#     csp-explain ....

#     # OMUS incremental 
#     csp-explain ...

#     # OMUS incremental + postponing optimization
#     csp-explain ...

#     # OMUS incremental + postponing optimization + warm start
#     csp-explain ...

# def experiment3():
#     # running a whole explanation sequence!
