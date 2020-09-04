import json
import sys
import time
import random

import builtins

# pysat imports
from pysat.formula import CNF
from pysat.solvers import Solver

sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
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
    # print(cnf)
    with Solver() as s:
        s.append_formula(cnf, no_return=False)
        solved = s.solve()
        if solved:
            # for id, m in enumerate(s.enum_models()):
            #     print(id)
            return set(s.get_model())
        else:
            raise "Problem"


def basecost(constraints, weights, clues, trans, bij):
    # nClues = len(constraints.intersection(clues))
    nClues = 0 #sum([1 if id in clues else 0 for id in constraints])
    nOthers = len(constraints) - nClues
    # print("constraints = ", constraints)
    if nClues == 0 and nOthers == 1:
        return 0
    elif nClues == 0 and nOthers > 1:
        return 20
    else:
        return nClues * 20


def cost(explanation, weights, clues, trans, bij):
    facts, constraints = explanation
    return basecost(constraints, weights, clues, trans, bij) + len(facts) + len(constraints)


# def propagate(cnf, I=list()):
#     lits = set(lit for ci in cnf for lit in ci) | set(-lit for ci in cnf for lit in ci)

#     with Solver() as s:
#         s.append_formula(cnf, no_return=False)
#         s.solve(assumptions=I)
#         model = set(s.get_model())

#     cnf_lits = lits.intersection(model)

#     return cnf_lits


def optimalPropagate(cnf, I=None):
    # m1 = [1, 2, 3, ....]
    # m2 = [ -1, 2, 3, ....] => [2, 3]
    # m3 = cnf + [-2, -3] => nieuw model [ .., ....]
    # if sat: nieuw intersection => model zoeken
    # anders: stoppen, huidige intersection gebruike
    with Solver() as s:
        s.append_formula(cnf, no_return=False)
        if I is None or len(I) == 0:
            s.solve()
        elif len(I) > 0:
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
                return model - set()


def print_omus_debug(o):
    print("\t\t\t - #Steps OptHS\t\t\t", o.optimal_steps[-1])
    print("\t\t\t - #Steps Greedy HS\t\t", o.greedy_steps[-1])
    print("\t\t\t - #Steps Incremental HS\t", o.incremental_steps[-1])
    print("\t\t\t - #Steps SAT HS\t\t", o.sat_steps[-1])
    print("\t\t\t - #Steps GROW HS\t\t", o.grow_steps[-1])

    # print("\t\t\t - Time OptHS\t\t\t", round(sum(o.timing.optimal[-1:-(1+o.optimal_steps[-1]):-1]),3), "\t[s]")
    # print("\t\t\t - Time Greedy HS\t\t", round(sum(o.timing.greedy[-1:-(1+o.greedy_steps[-1]):-1]),3), "\t[s]")
    # print("\t\t\t - Time Incremental HS\t\t", round(sum(o.timing.incremental[-1:-(1+o.incremental_steps[-1]):-1]),3), "\t[s]")
    # print("\t\t\t - Time SAT\t\t\t", round(sum(o.timing.sat[-1:-(1+o.sat_steps[-1]):-1]),3), "\t[s]")
    # print("\t\t\t - Time GROW\t\t\t", round(sum(o.timing.growMss[-1:-(1+o.grow_steps[-1]):-1]),3), "\t[s]")

    # if o.optimal_steps[-1] > 0:
    #     print("\t\t\t - AVG/step OPT\t\t\t", round(sum(o.timing.optimal[-1:-(1+o.optimal_steps[-1]):-1])/o.optimal_steps[-1],3), "\t[s/step]")
    # if o.greedy_steps[-1] > 0:
    #     print("\t\t\t - AVG/step Greedy \t\t", round(sum(o.timing.greedy[-1:-(1+o.greedy_steps[-1]):-1])/o.greedy_steps[-1],3), "\t[s/step]")
    # if o.incremental_steps[-1] > 0:
    #     print("\t\t\t - AVG/step Incremental \t", round(sum(o.timing.incremental[-1:-(1+o.incremental_steps[-1]):-1])/o.incremental_steps[-1],3), "\t[s/step]")
    # if o.sat_steps[-1] > 0:
    #     print("\t\t\t - AVG/step SAT\t\t\t", round(sum(o.timing.sat[-1:-(1+o.sat_steps[-1]):-1])/o.sat_steps[-1],3), "\t[s/step]")
    # if o.grow_steps[-1] > 0:
    #     print("\t\t\t - AVG/step GROW\t\t", round(sum(o.timing.growMss[-1:-(1+o.grow_steps[-1]):-1])/o.grow_steps[-1],3), "\t[s/step]")
    # # print(f"\t OMUS: {round(t_end_omus - t_start_omus, 2)}")
    # print(f"\t\t MSS size={o.MSS_sizes[-1]}\n")


def omusExplain(
        parameters=None,
        incremental=False,
        reuse_mss=False,
        seed_mss=False,
        timeout=None,
        cnf=None, 
        bv=None,
        hard_clauses=None,
        soft_clauses=None,
        soft_weights=None,
        I0=None,
        unknown_facts=None,
        bij=None,
        trans=None,
        clues=None,
        constrained=True
    ):
    # initial interpretation
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses

    # # TODO: match fact with table element from rels
    if I0 is None:
        I0 = set()

    I = I0

    I_cnf = [frozenset({lit}) for lit in I0]

    I_end = optimalPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)

    # explanation sequence
    expl_seq = []

    o = OMUS(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=I_end,
        soft_weights=soft_weights,
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=reuse_mss,
        clues=clues,
        trans=trans,
        bij=bij)

    best_costs = dict({i: 9999999 for i in explainable_facts - I})

    if seed_mss:
        # add full theory without negation literal
        # o.MSSes.add((o.fullMss, frozenset(I_end)))
        base_F = set(range(len(o.soft_clauses)))
        F = base_F | set({o.softClauseIdxs[frozenset({-i})] for i in explainable_facts - I})

        for i in explainable_facts - I:

            # F = base_F | set({o.softClauseIdxs[frozenset({-i})] for })

            # Only negation of literal inside
            # o.clauses = o.soft_clauses + [frozenset({-i})]
            # o.weights = o.soft_weights + [1] * len(o.I_lits)
            # F_prime = last variable
            F_prime = set({o.softClauseIdxs[frozenset({-i})]})

            MSS, MSS_Model = o.maxsat_fprime(F_prime, set())

            o.MSSes.add((frozenset(MSS), frozenset(MSS_Model)))

    print(o.MSSes)
    # -- precompute some hitting sets for a rough idea on the costs
    w_I = [1 for _ in I] + [1]

    t_start_seed = time.time()
    if seed_mss:
        for i in explainable_facts - I:
            hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                        explained_literal=i,
                                        add_weights=w_I,
                                        best_cost=best_costs[i],
                                        hs_limit=len(explainable_facts - I) + 10
                                        )
            if type(explanation) != list:
                best_costs[i] = explanation + 1000
            else:
                E_i = [ci for ci in explanation if ci in I_cnf]

                # constraint used ('and not ci in E_i': dont repeat unit clauses)
                S_i = [ci for ci in explanation if ci in soft_clauses and ci not in E_i]
                S_hs = [soft_clauses.index(si) for si in S_i]

                # new fact
                N_i = {i}

                cost_explanation = cost((E_i, S_hs), soft_weights, clues, trans, bij)
                best_costs[i] = min([cost_explanation, best_costs[i]])
    
    t_end_seed = time.time()
    # print("Time_seed = ", t_end_seed - t_start_seed)

    cnt = 0

    while len(explainable_facts - I) > 0:
        t_iter = time.time()
        assert len(I) == len(I_cnf)

        cost_best = None
        E_best, S_best, N_best = None, None, None

        # existing facts + unit weight for negated literal
        w_I = [1 for _ in I] + [1]

        # print("\n", {i: best_costs[i] for i in sorted(explainable_facts - I, key=lambda i: best_costs[i])}, "\n")
        print("Remaining explanations=", explainable_facts - I)
        for i in explainable_facts - I:
        # for id, i in enumerate(sorted(explainable_facts - I, key=lambda i: best_costs[i])):

            print("Explaining=", i)
            # print(f"Expl {i:4} [{id+1:4}/{len(explainable_facts-I):4}] \tbest_cost_i= ", best_costs[i], "\t - \t", "cost_best=\t", cost_best, end="\r")

            t_start_omus = time.time()

            if constrained:
                hs, explanation = o.omusConstr(I_cnf=I_cnf, 
                                               explained_literal=i)
            elif incremental:
                hs, explanation = o.omusIncr(I_cnf=I_cnf,
                                             explained_literal=i,
                                             add_weights=w_I,
                                             best_cost=cost_best)
            else:
                hs, explanation = o.omus(add_clauses=I_cnf + [frozenset({-i})],
                                         add_weights=w_I)

            # if hs is None:
            #     # HACK: store my_cost of this guy, for sorting next iter
            #     best_costs[i] = 1000+explanation
            #     continue

            assert len(hs) > 0, "OMUS shoudl be non empty"

            t_end_omus = time.time()

            # DEBUG INFO
            print(f"\n\t\t OMUS total exec time: {round(t_end_omus - t_start_omus, 2)}")
            # print_omus_debug(o)

            # explaining facts
            E_i = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in explanation if ci in soft_clauses and ci not in E_i]
            S_hs = [soft_clauses.index(si) for si in S_i]

            # new fact
            N_i = {i}

            cost_explanation = cost((E_i, S_hs), soft_weights, clues, trans, bij)
            best_costs[i] = min([cost_explanation, best_costs[i]])

            # print(f"\n\t\tCandidate explanation for {i} \t\t {E_i} /\\ {S_i} => {N_i} ({cost_explanation})\n")

            if cost_best is None or cost_explanation < cost_best:
                E_best, S_best, N_best = E_i, S_i, N_i
                cost_best = cost_explanation

        # post-processing the MSSes
        # keep = set()
        # for (m1, m1_model) in o.MSSes:
        #     keep_m1 = True
        #     for (m2, _) in o.MSSes:
        #         if m1 != m2 and m1 < m2:
        #             keep_m1 = False
        #     if keep_m1:
        #         keep.add((m1, m1_model))
        # o.MSSes = keep

            # @TIAS: printing explanations as they get better
            # print(f"\tFacts: {E_i} Clause: {S_i} => {N_i} (", cost_explanation, ")")

        # propagate as much info as possible
        # print(explanation)
        # Timing: skip for now...
        t_start= time.time()
        New_info = optimalPropagate(hard_clauses + E_best + S_best, I)
        t_end= round(time.time() - t_start, 3)
        print("Time Optimal Propagate=\t", t_end)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        I_cnf += [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]

        expl_seq.append((E_best, S_best, N_best))

        # @TIAS: printing explanations
        print(f"\nOptimal explanation \t\t {E_best} /\\ {S_best} => {N_best}", time.time()-t_iter,"\n")

        cnt += 1

    assert all(False if -lit in I or lit not in I_end else True for lit in I)

    # o.export_results('results/')

    return o, expl_seq


def omusExplain2(
        parameters=None,
        reuse_mss=False,
        seed_mss=True,
        hard_clauses=None,
        soft_clauses=None,
        soft_weights=None,
        I0=None,
        unknown_facts=None,
        constrained=True
    ):

    # initial interpretation
    if hard_clauses is not None and soft_clauses is not None:
        cnf = hard_clauses+soft_clauses

    # # TODO: match fact with table element from rels
    if I0 is None:
        I0 = set()

    I = I0

    I_cnf = [frozenset({lit}) for lit in I0]

    I_end = optimalPropagate(cnf, I0)

    explainable_facts = set(lit for lit in I_end if abs(lit) in unknown_facts)
    print("End interpretation=", I_end)
    # explanation sequence
    expl_seq = []

    o = OMUS(
        hard_clauses=hard_clauses,
        soft_clauses=soft_clauses,
        I=I_end,
        soft_weights=soft_weights,
        parameters=parameters,  # default parameters
        logging=True,
        reuse_mss=reuse_mss)

    best_costs = dict({i: 9999999 for i in explainable_facts - I})

    if seed_mss:
        # add full theory without negation literal
        # o.MSSes.add((o.fullMss, frozenset(I_end)))
        base_F = set(range(len(o.soft_clauses)))

        F = base_F | set({o.softClauseIdxs[frozenset({-i})] for i in explainable_facts - I})

        for i in explainable_facts - I:

            F_prime = set({o.softClauseIdxs[frozenset({-i})]})

            MSS, MSS_Model = o.maxsat_fprime(F_prime, set())

            o.MSSes.add((frozenset(MSS), frozenset(MSS_Model)))

    print(o.MSSes)

    # -- precompute some hitting sets for a rough idea on the costs

    while len(explainable_facts - I) > 0:
        E_best, S_best, N_best = None, None, None

        print("Remaining explanations=", explainable_facts - I)

        if constrained:
            hs, explanation = o.omusConstr(I_cnf=I_cnf,
                                           explained_literal=i)
        print("Hs=\t", hs)
        print("explanation=\t", explanation)
        # explaining facts
        E_best = [ci for ci in explanation if ci in I_cnf]

        # constraint used ('and not ci in E_i': dont repeat unit clauses)
        S_best = [ci for ci in explanation if ci in soft_clauses and ci not in E_best]
        S_hs = [soft_clauses.index(si) for si in S_best]


        # propagate as much info as possible
        # print(explanation)
        # Timing: skip for now...
        New_info = optimalPropagate(hard_clauses + E_best + S_best, I)
        N_best = New_info.intersection(explainable_facts) - I

        # add new info
        I = I | N_best
        new_cnf = [frozenset({lit}) for lit in N_best if frozenset({lit}) not in I_cnf]
        I_cnf += new_cnf
        

        expl_seq.append((E_best, S_best, N_best))

        # @TIAS: printing explanations
        print(f"\nOptimal explanation \t\t {E_best} /\\ {S_best} => {N_best}","\n")

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
