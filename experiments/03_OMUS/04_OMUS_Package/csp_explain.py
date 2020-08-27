import json
import sys
import time
import random

# pysat imports
from pysat.formula import CNF
from pysat.solvers import Solver

# sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
sys.path.append('/home/emilio/Documents/cppy_src/')

from cppy import BoolVarImpl, Comparison, Model, Operator, cnf_to_pysat
# from cppy.solver_interfaces.pysat_tools import 
from cppy.model_tools.to_cnf import *
from frietkot import frietKotProblem, p5, Relation, exactly_one
from omus import OMUS, Steps


def literalstoDict(literals, literal_match):
    # TODO match literals with their axioms in first-order logic
    dictLiterals = []
    for literal in literals:
        # TODO do the matching of literals with pred-subjects-object-value
        continue

    return dictLiterals


def explanationsToJson(explanations, clue_match, literal_match, output):
    """Generates a .json file for visualizing the explanations in the zebra tutor system. Output
    format follows the following structure:
         {
             # integer value provided by the cost function
             "cost":,
             # type of constraint used
             "clue":,
              # facts used to derive new information
             "assumptions":[
                 {"pred":"", "subject":"", "object":"", "value":true/false},
                 ...
             ],
             # new information derived
             "derivations":[
                {"pred":"", "subject":"", "object":"", "value":true/false},
                 ...
             ]
         }

    Ends with :
        {
            "clue": "Solution!",
            "assumptions": [],
            "derivations": []
        }


    Args:
        explanations {iterable(dict)}: [description]
        clue_match dict(int): Match the clauses to clue or constraint
        literal_match dict(int): Match the literals to the axioms
        output {string}: name of output file
    """
    json_expls = []
    for expl in explanations:

        clue = clue_match[expl["clue"]]
        assumptions = literalstoDict(expl["assumptions"], literal_match)
        derivations = literalstoDict(expl["derived"], literal_match)

        json_expl = {
            "cost": 0,
            "clue": clue,
            "assumptions": assumptions,
            "derivations": derivations
        }

        json_expls.append(json_expl)

    with open(output, 'w') as fp:
        json.dump(json_expls, fp)


def maxPropagate(cnf, I=list()):
    with Solver() as s:
        s.append_formula(cnf, no_return=False)
        solved = s.solve()
        if solved:
            return set(s.get_model())
        else:
            raise "Problem"


def basecost(constraints, clues):
    # nClues = len(constraints.intersection(clues))
    nClues = 0
    nOthers = len(constraints) - nClues
    # print("constraints = ", constraints)
    if nClues == 0 and nOthers == 1:
        return 0
    elif nClues == 0 and nOthers > 1:
        return 20
    else:
        return nClues * 20


def cost(explanation):
    facts, constraints, new = explanation
    return basecost(constraints, set()) + len(facts) + len(constraints)


def propagate(cnf, I=list()):
    lits = set(lit for ci in cnf for lit in ci) | set(-lit for ci in cnf for lit in ci)

    with Solver() as s:
        s.append_formula(cnf, no_return=False)
        s.solve(assumptions=I)
        model = set(s.get_model())

    cnf_lits = lits.intersection(model)

    return cnf_lits


def optimalPropagate(cnf, I):
    # m1 = [1, 2, 3, ....]
    # m2 = [ -1, 2, 3, ....] => [2, 3]
    # m3 = cnf + [-2, -3] => nieuw model [ .., ....]
    # if sat: nieuw intersection => model zoeken
    # anders: stoppen, huidige intersection gebruike
    with Solver() as s:
        s.append_formula(cnf, no_return=False)
        s.solve(assumptions=list(I))
        # models = []
        model = None
        for i, m in enumerate(s.enum_models()):
            if i == 2:
                break
            if model is None:
                model = set(m)
            else:
                model.intersection(set(m))

        while(True):
            s.add_clause(list(-lit for lit in model))
            solved = s.solve()
            if solved:
                new_model = set(s.get_model())
                model = model.intersection(new_model)
            else:
                return model - I


def naiveOptimalPropagate(cnf, I):
    # The most precise and most expensive version returns the partial structure in which atoms are unknown 
    # iff they do not have the same truth value in all models
    # I_prop = set(I)
    all_models = set()
    with Solver() as s:
        s.append_formula(cnf, no_return=False)
        for m in s.enum_models():
            all_models |= set(m)
    lits = set(lit for lit in all_models if -lit not in all_models and lit not in I)
    return lits


def omusExplain(cnf, rels=None, weights=None, parameters=None, incremental=False, reuse_mss=False, I0=None):
    # initial interpretation
    # # TODO: match fact with table element from rels
    if I0 is None:
        I0 = set()
    I = I0
    I_cnf = [frozenset({lit}) for lit in I0]
    I_end_all = maxPropagate(cnf, list(I0))
    # if rels != None:
    grid_variables = set()
    if rels is not None:
        for rel in rels:
            # print("\n", rel.df, "\n")

            for item in rel.df.values:
                grid_variables |= set(i.name+1 for i in item)

        I_end = set(i for i in I_end_all if abs(i) in grid_variables)
    else:
        I_end = I_end_all
    print("Done max propagate:",I_end)

    # explanation sequence
    expl_seq = []
    # print(I_cnf)
    # add unit literals to Interpretation
    for id, cl in enumerate(list(cnf)):
        if len(cl) == 1:
            lit = next(iter(cl))
            I.add(lit)
            I_cnf.append(frozenset({lit}))
            cnf.remove(cl)
            del weights[id]
            expl_seq.append((set(), cl, lit))
            print(f"UNIT explanation \t\t {set()}\t /\\ {cl}\t => {lit}\n")

    print(I_cnf)
    # @TIAS:  OMUS model with all clauses
    print("Creating OMUSable cnf with",len(cnf),"clauses")
    o = OMUS(from_clauses=cnf, I=I_end_all, parameters=parameters, weights=weights, logging=True, reuse_mss=reuse_mss)

    cnt = 0
    while len(I_end - I) > 0:
        assert len(I) == len(I_cnf)
        cost_best = None
        E_best, S_best, N_best = None, None, None

        # existing facts
        w_I = [1 for _ in I] + [1]
        print(f"run {cnt}")
        explainable_facts = list(I_end - I)
        random.shuffle(explainable_facts)
        for i in explainable_facts:
            print(f"\n\t{cnt} - Explaining fact [{i}]")
            t_start_omus = time.time()
            # Match MSS
            if incremental:

                hs, explanation = o.omusIncr(add_clauses=I_cnf + [frozenset({-i})],
                                                add_weights=w_I)
            else:
                hs, explanation = o.omus(add_clauses=I_cnf + [frozenset({-i})],
                                            add_weights=w_I)
            t_end_omus = time.time()
            print(f"\t\t OMUS total exec time: {round(t_end_omus - t_start_omus, 2)}")
            print("\t\t\t - #Steps OptHS\t\t\t", o.optimal_steps[-1])
            print("\t\t\t - #Steps Greedy HS\t\t", o.greedy_steps[-1])
            print("\t\t\t - #Steps Incremental HS\t", o.incremental_steps[-1])

            print("\t\t\t - Time OptHS\t\t\t", round(sum(o.timing.optimal[-1:-(1+o.optimal_steps[-1]):-1]),3), "s")
            print("\t\t\t - Time Greedy HS\t\t", round(sum(o.timing.greedy[-1:-(1+o.greedy_steps[-1]):-1]),3), "s")
            print("\t\t\t - Time Incremental HS\t\t", round(sum(o.timing.incremental[-1:-(1+o.incremental_steps[-1]):-1]),3), "s")
            # print(f"\t OMUS: {round(t_end_omus - t_start_omus, 2)}")
            print(f"\t\t MSS size={o.MSS_sizes[-1]}\n")

            # explaining facts
            E_i = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in explanation if ci in cnf and ci not in E_i]

            # new fact
            N_i = {i}
            print(E_i, S_i, N_i)

            if cost_best is None or cost((E_i, S_i, N_i)) < cost_best:
                E_best, S_best, N_best = E_i, S_i, N_i
                cost_best = cost((E_i, S_i, N_i))

                # @TIAS: printing explanations as they get better
                # print(f"Facts:\n\t{E_best}  \nClause:\n\t{S_best} \n=> Derive (at cost {cost_best}) \n\t{N_best}")
        
        # propagate as much info as possible
        N_best = optimalPropagate(E_best + S_best, I)

        # add new info
        I = I | N_best
        I_cnf += [frozenset({lit}) for lit in N_best]

        expl_seq.append((E_best, S_best, N_best))

        # @TIAS: printing explanations
        print(f"Optimal explanation \t\t {E_best} /\\ {S_best} => {N_best}\n")
        # print(f"Facts:\n\t{E_best}  \nClause:\n\t{S_best} \n=> Derive (at cost {cost_best}) \n\t{N_best}")

        cnt += 1

    assert all(False if -lit in I or lit not in I_end else True for lit in I)

    # o.export_results('results/')

    return o, expl_seq


if __name__ == "__main__":
    # parameters
    parameters = {'extension': 'greedy_no_param','output': 'log.json'}
    reuse_mss = True
    incremental = True
    # explain
    cppy_model = frietKotProblem()
    cnf = cnf_to_pysat(cppy_model.constraints)
    frozen_cnf = [frozenset(c) for c in cnf]
    seq = omusExplain(frozen_cnf, weights=[len(c) for c in cnf], parameters=parameters, incremental=incremental, reuse_mss=reuse_mss)