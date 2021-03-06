#!/usr/bin/env python
# coding: utf-8

# standard libraries
from __future__ import print_function
import os
import re
import sys
from pathlib import Path
from enum import Enum
import json
import time
from collections import Counter
from datetime import datetime
from statistics import mean
# pysat library
from pysat.solvers import Solver, SolverNames
from pysat.formula import CNF, WCNF
from pysat.examples.fm import FM
from pysat.examples.musx import MUSX
from pysat.examples.rc2 import RC2, RC2Stratified
from pysat.examples.hitman import Hitman

# gurobi library
import gurobipy as gp
from gurobipy import GRB

# or-tools library
from ortools.linear_solver import pywraplp
from OMUS_utils import *

# configs
import pprint

# utilities
ppprint = pprint.PrettyPrinter(indent=4).pprint

def debug(info, verbose=True):
    if verbose:
        print(info)

def debug_ppprint(info, verbose=False):
    if verbose:
        print(json.dumps(info, indent=4))

def complement(F, F_prime):
    return set(i for i in range(len(F))) - set(i for i in F_prime)

def clause_length(clause):
    # weighted based on the number of literals inside the clause
    return len(clause)

def cnf_weights(cnf, weight = clause_length):
    return [weight(clause) for clause in cnf.clauses]

def clauses_weights(clauses, weight = clause_length):
    return [weight(clause) for clause in clauses]

def checkSatClauses(clauses, F_prime):
    if len(F_prime) == 0 :
        return [], True

    cnf_clauses = [clauses[i] for i in F_prime]

    mapping, reverse_mapping = mapping_clauses(cnf_clauses)
    mapped_clauses = map_clauses(cnf_clauses, mapping)

    with Solver() as s:
        added = s.append_formula(mapped_clauses, no_return=False)
        solved = s.solve()
        model = s.get_model()

    if solved:
        mapped_model = frozenset(map(lambda literal: reverse_mapping[abs(literal)]*sign(literal) , model))
        return mapped_model, solved
    else:
        return None, solved

def getBestModel(clauses, models):
    bestmodel = None
    reachability = {id:0 for id, _ in enumerate(models)}

    for id, model in enumerate(models):
        reachability[id] = sum([1 if len(model.intersection(clause)) > 0 else 0 for clause in clauses])

    sorted_reachability = {k: v for k, v in sorted(reachability.items(), key=lambda item: item[1])}

    bestmodel = models[next(iter(sorted_reachability))]

    return bestmodel

def getAllModels(clauses, F_prime):
    if not F_prime :
        return [], True

    cnf_clauses = [clauses[i] for i in F_prime]

    mapping, reverse_mapping = mapping_clauses(cnf_clauses)
    mapped_clauses = map_clauses(cnf_clauses, mapping)
    model = []

    with Solver() as s:
        added = s.append_formula(mapped_clauses, no_return=False)
        solved = s.solve()
        models = [set(l for l in m) for m in s.enum_models()]

        if solved:
            model = getBestModel(clauses, models)

    if solved:
        mapped_model = frozenset(map(lambda literal: reverse_mapping[abs(literal)]*sign(literal) , model))
        return mapped_model, solved
    else:
        return None, solved

def findBestLiteral(clauses, F_prime, literals, diff = True):
    """Find the best literal in the list of `literals' based on the number of clauses
    the literal hits.

    Arguments:
        clauses {iterable(set(int))} -- collection of clauses (sets of literals)
        F_prime {iterable(int)} -- Hitting set
        literals {iterable(int)} -- Candidate literals

    Returns:
        int -- literal hitting the most clauses in the not satisfied clauses of `clauses'
    """
    literal_count = Counter({literal:0 for literal in literals})
    neg_literal_count = Counter({literal:0 for literal in literals if -literal in literals})

    for i, clause in enumerate(clauses):
        if i not in F_prime:
            literal_count.update(clause.intersection(literals))
            neg_literal_count.update([-l for l in clause.intersection(literals)])

    if diff == True:
        literal_diff = literal_count.copy()
        literal_diff.subtract(neg_literal_count)
        best_literal = literal_diff.most_common(1)[0][0] if literal_diff else None
    else:
        best_literal = literal_count.most_common(1)[0][0] if literal_count else None

    return best_literal

def defaultExtension(cnf_clauses, F_prime, model):
    return F_prime

def extension1(clauses, F_prime, model):
    """`Extension1' unit propagate the model to find all clauses hit by the current
    assignment of F_prime.

    Arguments:
        clauses {iterable(iterable(int))} -- collection of clauses (sets of literals)
        F_prime {iterable(int)} -- Hitting set, optimal set of clauses hitting H
        model {iterable(int)} -- model of clauses in F_prime

    Returns:
        iterable(int), iterable(int) -- Grown hitting set, new model of hitting set
    """
    new_F_prime = set(F_prime)
    # precompute both
    lit_true = set(model)
    lit_false = set(-l for l in model)

    clause_added = True
    while(clause_added):
        clause_added = False
        t_F_prime = set(new_F_prime)
        for i, clause in enumerate(clauses):
            if i in new_F_prime:
                continue # already in F_prime

            # Similar alternative:
            if len(clause.intersection(lit_true)) > 0:
                # a true literal, clause is true
                t_F_prime.add(i)
                clause_added = True

            else:
                unassigned = clause - lit_false
                if len(unassigned) == 1:
                    t_F_prime.add(i)
                    # add literal to the model
                    lit = next(iter(unassigned))
                    lit_true.add(lit)
                    lit_false.add(-lit)
                    clause_added = True
        if len(t_F_prime) > len(new_F_prime):
            new_F_prime = t_F_prime
            # check for unit propagation

    assert all([True if -l not in lit_true else False for l in lit_true]), f"Conflicting literals {lit_true}"
    return new_F_prime, lit_true

def extension2(clauses, F_prime, model, random_literal = False):
    all_literals = frozenset.union(*clauses)
    t_F_prime, t_model = extension1(clauses, F_prime, model)
    lit_true = set(t_model)
    lit_false = set(-l for l in t_model)
    clause_added = False

    # alternative, over all literals
    remaining_literals = all_literals - lit_true - lit_false
    conflict_free_literals = remaining_literals - set(-l for l in remaining_literals)

    while(len(conflict_free_literals) > 0):
            if random_literal:
                lit = next(iter(conflict_free_literals))
            else:
                lit = findBestLiteral(clauses, t_F_prime, conflict_free_literals)

            lit_true.add(lit)
            lit_false.add(-lit)

            t_F_prime, t_model = extension1(clauses, t_F_prime, lit_true)

            lit_true = set(t_model)
            lit_false = set(-l for l in t_model)

            remaining_literals = all_literals - lit_true - lit_false
            conflict_free_literals = remaining_literals - set(-l for l in remaining_literals)

    conflictual_literals = set(remaining_literals)

    assert all([True if -l in conflictual_literals else False for l in conflictual_literals])

    # propagate all remaining literals
    while len(conflictual_literals) > 0:
        if random_literal:
            literal = next(iter(conflictual_literals))
        else:
            literal = findBestLiteral(clauses, t_F_prime, conflictual_literals)

        conflictual_literals.remove(literal)
        # because the unit prop created a conflict-free one, we must check
        if -literal in conflictual_literals:
            conflictual_literals.remove(-literal)

        lit_true.add(literal)
        lit_false.add(-literal)

        # unit propagate new literal
        t_F_prime, t_model = extension1(clauses, t_F_prime, lit_true)

        lit_true = set(t_model)
        lit_false = set(-l for l in t_model)

        # code was probably not finished because the latter was missing
        remaining_literals = all_literals - lit_true - lit_false
        conflictual_literals = set(remaining_literals)

    assert all([True if -l not in lit_true else False for l in lit_true])

    return t_F_prime, lit_true

def extension3(clauses, F_prime, model, diff= True):
    # literals
    all_literals = frozenset.union(*clauses)
    t_F_prime = set(F_prime)
    lit_true = set(model)
    lit_false = set(-l for l in model)

    # unit propagate existing model
    for i, clause in enumerate(clauses):
        if i not in t_F_prime and len(clause.intersection(lit_true)) > 0:
            t_F_prime.add(i)

    remaining_literals = set(all_literals - lit_true - lit_false)

    # unit propagate conflict free clauses
    conflict_free_literals = set(l for l in remaining_literals if -l not in remaining_literals)
    lit_true |= conflict_free_literals
    lit_false |= set(-l for l in conflict_free_literals)

    for i, clause in enumerate(clauses):
        if i not in t_F_prime and len(clause.intersection(lit_true)) > 0:
            t_F_prime.add(i)

    remaining_literals -= conflict_free_literals

    while(len(remaining_literals) > 0):
        # Build counter for literal to clause coverage
        literal_count = Counter({literal:0 for literal in remaining_literals})
        neg_literal_count = Counter({literal:0 for literal in remaining_literals})

        for i, clause in enumerate(clauses):
            if i not in t_F_prime:
                if len(clause.intersection(lit_true)) > 0:
                    t_F_prime.add(i)
                else:
                    literal_count.update(clause.intersection(remaining_literals))
                    neg_literal_count.update([-l for l in clause.intersection(remaining_literals)])

        literal_diff = Counter(literal_count)
        literal_diff.subtract(neg_literal_count)
        best_literal = literal_diff.most_common(1)[0][0] if literal_diff else None

        lit_true.add(best_literal)
        lit_false.add(-best_literal)

        remaining_literals.remove(best_literal)

        # because the unit prop created a conflict-free one, we must check
        if -best_literal in remaining_literals:
            remaining_literals.remove(-best_literal)

    return t_F_prime, lit_true


# def extension3(clauses, F_prime, model, diff= True):
#     # literals
#     all_literals = frozenset.union(*clauses)
#     t_F_prime = set(F_prime)
#     lit_true = set(model)
#     lit_false = set(-l for l in model)

#     # unit propagate existing model
#     for i, clause in enumerate(clauses):
#         if i not in t_F_prime and len(clause.intersection(lit_true)) > 0:
#             t_F_prime.add(i)

#     remaining_literals = set(all_literals - lit_true - lit_false)

#     # unit propagate conflict free clauses
#     conflict_free_literals = set(l for l in remaining_literals if -l not in remaining_literals)
#     lit_true |= conflict_free_literals
#     lit_false |= set(-l for l in conflict_free_literals)

#     for i, clause in enumerate(clauses):
#         if i not in t_F_prime and len(clause.intersection(lit_true)) > 0:
#             t_F_prime.add(i)

#     remaining_literals = frozenset.union(*[clause for i, clause in enumerate(clauses) if i not in t_F_prime]) - lit_true - lit_false

#     while(len(remaining_literals) > 0):
#         # Build counter for literal to clause coverage
#         literal_count = Counter({literal:0 for literal in remaining_literals})
#         neg_literal_count = Counter({literal:0 for literal in remaining_literals})

#         for i, clause in enumerate(clauses):
#             if i not in t_F_prime:
#                 if len(clause.intersection(lit_true)) > 0:
#                     t_F_prime.add(i)
#                 else:
#                     literal_count.update(clause.intersection(remaining_literals))
#                     neg_literal_count.update([-l for l in clause.intersection(remaining_literals)])

#         literal_diff = Counter(literal_count)
#         literal_diff.subtract(neg_literal_count)
#         best_literal = literal_diff.most_common(1)[0][0] if literal_diff else None

#         lit_true.add(best_literal)
#         lit_false.add(-best_literal)

#         remaining_literals = frozenset.union(*[clause for i, clause in enumerate(clauses) if i not in t_F_prime]) - lit_true - lit_false

#         conflict_free_literals = set(l for l in remaining_literals if -l not in remaining_literals)
#         lit_true |= conflict_free_literals
#         lit_false |= set(-l for l in conflict_free_literals)
#         remaining_literals -= lit_true
#         remaining_literals -= lit_false
#         # print(len(remaining_literals))

#         # remaining_literals.remove(best_literal)

#         # # because the unit prop created a conflict-free one, we must check
#         # if -best_literal in remaining_literals:
#         #     remaining_literals.remove(-best_literal)


#     return t_F_prime, lit_true

def extension4(clauses, F_prime, model):
    t_F_prime = set(F_prime)

    # t_F_prime, t_model = extension3(clauses, F_prime, model)
    wcnf = WCNF()
    for i, clause in enumerate(clauses):
        if i in F_prime:
            wcnf.append(list(clause))
        else:
            wcnf.append(list(clause), weight=1)

    with RC2(wcnf) as rc2:
        t_model = rc2.compute()

    # print("F_prime:", F_prime, "model:",  model)
    for i, clause in enumerate(clauses):
        if i not in t_F_prime and len(clause.intersection(t_model)) > 0:
            t_F_prime.add(i)

    # print("t_F_prime:", t_F_prime, "t_model:",  t_model)
    return t_F_prime, t_model

def gurobiModel(clauses, weights):
    # create gurobi model
    g_model = gp.Model('MipOptimalHittingSet')

    # model parameters
    # g_model.Params.LogFile = 'logs/'+datetime.now().strftime("%Y_%m_%d_%H_%M_%S")+'.log'
    g_model.Params.OutputFlag = 0
    g_model.Params.LogToConsole = 0
    g_model.Params.Threads = 8

    # create the variables
    x = g_model.addMVar(shape= len(clauses), vtype=GRB.BINARY, name="x")

    # set objective : min sum xi*wi
    g_model.setObjective(sum( x[i] * weights[i] for i in range(len(clauses)) ), GRB.MINIMIZE)

    # update the model
    g_model.update()

    return g_model

def addSetGurobiModel(clauses, gurobi_model, C):

    h = [1 if i in C else 0 for i in range(len(clauses))]

    # variables
    x = gurobi_model.getVars()

    # add new constraint sum x[j] * hij >= 1
    # gurobi_model.addConstr(gp.quicksum(x[i] * h[i] for i in range(len(clauses))) >= 1)
    gurobi_model.addConstr(gp.quicksum(x[i] for i in C) >= 1)

def gurobiOptimalHittingSet(clauses, gurobi_model, C):
    # trivial case
    if len(C) == 0:
        return []

    # add new constraint sum x[j] * hij >= 1
    addSetGurobiModel(clauses, gurobi_model, C)

    # solve optimization problem
    gurobi_model.optimize()

    # output hitting set
    x = gurobi_model.getVars()
    hs = set(i for i in range(len(clauses)) if x[i].x == 1)

    return hs

def gurobiOptimalHittingSetCold(clauses, weights,  H):
    gurobi_model = gurobiModel(clauses, weights)
    # trivial case
    if len(H) == 0:
        return []

    # add new constraint sum x[j] * hij >= 1
    for C in H:
        addSetGurobiModel(clauses, gurobi_model, C)

    # solve optimization problem
    gurobi_model.optimize()

    # output hitting set
    x = gurobi_model.getVars()
    hs = set(i for i in range(len(clauses)) if x[i].x == 1)
    gurobi_model.dispose()

    return hs

def create_data_model(H, weights):
    """Stores the data for the problem:

        data['H']:                  collection of sets (of clauses) to hit
        data['indices']:            unique clause indices
        data['num_constraints']:    number of constraints
        data['bounds']:             >= 1 for every constraint
        data['num_vars']:           number of clauses
        data['obj_coeffs']          Coefficients of the objective function

    """

    # indices of clauses used
    indices_H = sorted(set.union(*H))
    n_constraints = len(H)
    n_vars = len(indices_H)

    data = {}
    data['H'] = H
    data['indices'] = indices_H
    data['num_constraints'] = n_constraints
    data['bounds'] = [1 for i in range(n_constraints)]
    data['num_vars'] = n_vars
    data['obj_coeffs'] = {index:weights[index] for index in indices_H}

    # constraint coefficients hij = 1 if variable x_j is in set h_i
    c_coeffs = [[None for _ in range(n_vars)] for _ in range(n_constraints)]

    for j, hj in enumerate(H):
        for i in range(n_vars):
            c_coeffs[j][i] = 1 if indices_H[i] in hj else 0

    data['constraint_coefficients'] = c_coeffs

    # matching clause indices with position in list of clause indices
    # ex: {3 : 0, 7: 1, ....} clause 3 position 0, clause 7 position 1, ...
    data['matching_table'] = {idx : i for i, idx in enumerate(indices_H) }
    return data

## OR tools Optimal Hitting set MIP implementation
def optimalHittingSet(H, weights):
    # trivial case
    if len(H) == 0:
        return []

    data = create_data_model(H, weights)
    # [START solver]
    # Create the mip solver with the CBC backend.
    # solver = pywraplp.Solver('OptimalHittingSet', pywraplp.Solver.BOP_INTEGER_PROGRAMMING)
    solver = pywraplp.Solver('OptimalHittingSet', pywraplp.Solver.CBC_MIXED_INTEGER_PROGRAMMING)
    # [END solver]

    # [START variables]
    #infinity = solver.infinity()
    x = {}
    for j in data['indices']:
        # x[j] = solver.IntVar(0,1,'x[%i]' % j)
        x[j] = solver.BoolVar('x[%i]' % j)
    # [END variables]

    # [START constraints]
    for i in range(data['num_constraints']):
        # for all i in {1.. |H|}: sum x[j] * hij >= 1
        constraint_expr = [data['constraint_coefficients'][i][j] * x[idx] for j, idx in enumerate(data['indices'])]
        solver.Add(sum(constraint_expr) >= data['bounds'][i])
    # [END constraints]

    # [START objective]
    # Maximize sum w[i] * x[i]
    objective = solver.Objective()
    for idx in data['indices']:
        objective.SetCoefficient(x[idx], data['obj_coeffs'][idx])
    objective.SetMinimization()
    # [END objective]

    # max 10 minute timeout for solution
    # solver.parameters.max_time_in_seconds = 10 (min) * 60 (s) * 1000 ms
    k = solver.SetNumThreads(8)
    solver.set_time_limit(60 * 3* 1000)
    # solver.set_time_limit(10 * 60 * 1000)

    # Solve the problem and print the solution.
    # [START print_solution]
    status = solver.Solve()

    if status == pywraplp.Solver.OPTIMAL:
        hs = [j for j in data['indices'] if x[j].solution_value() == 1]
        return hs
    else:
        raise HittingSetSolver(status, data)
        return []
    # [END print_solution]

def grow(clauses, F_prime, model, extension = 0):
    """

        Procedure to efficiently grow the list clauses in ``F_prime``. The complement of F_prime is a correction
        set.

        :param cnf_clauses: a collection of clauses (list of literals).
        :param F_prime: hitting set : a list of clauses.
        :param extensions: list of extensions activated

        The ``extensions`` argument is a list of extensions on the default grow procedure to optimize
        the building of the minimum correction set.


        :type cnf_clauses: iterable(iterable(int))
        :type F_prime: iterable(int)
        :type extensions: iterable(int)

        Extension 1 :

            add all clauses that are true based on the assignment by the model of Fprime

        Extension 2 :

            for all variables not in variables assigned by model of Fprime
            give random values => manually check wether any clause is satisfied by this and
            add it to Fprime.

        Extension 3:

            greedy

        Extension 4:

            Maxsat
    """

    extensions = {
        0 : defaultExtension,
        1 : extension1,
        2 : extension2,
        3 : extension3,
        4 : extension4
    }

    new_F_prime = frozenset(F_prime)

    new_F_prime, new_model = extensions[extension](clauses, new_F_prime, model)

    return complement(clauses, new_F_prime)

## OMUS algorithm
def omusOrTools(cnf: CNF, extension = 3, sat_model = True, f = clause_length, outputfile = 'log.txt'):
    benchmark_data = {}
    benchmark_data['clauses'] = len(cnf.clauses)
    benchmark_data['avg_clause_len'] = mean([len(clause) for clause in cnf.clauses])

    t_hitting_set = []
    t_sat_check = []
    t_grow = []
    steps = 0
    t_start_omus = time.time()

    frozen_clauses = [frozenset(c for c in clause) for clause in cnf.clauses]
    weights = clauses_weights(cnf.clauses, f)

    H = [] # the complement of a max-sat call

    while(True):
        # compute optimal hitting set
        print("OrTools -", len(H), "Optimal Hitting Set" )
        t_hs_start = time.time()
        hs =  optimalHittingSet(H, weights)
        t_hs_end = time.time()
        t_hitting_set.append(t_hs_end - t_hs_start)

        # hs =  gurobiOptimalHittingSet(cnf.clauses, gurobi_model, C)
        print("OrTools -", len(H), "Check Sat" )

        # check satisfiability of clauses
        if sat_model:
            t_sat_start = time.time()
            model, sat = checkSatClauses(frozen_clauses, hs)
            t_sat_end = time.time()
        else:
            t_sat_start = time.time()
            model, sat = getAllModels(frozen_clauses, hs)
            t_sat_end = time.time()
        t_sat_check.append(t_sat_end-t_sat_start)
        # model, sat = checkSatClauses(frozen_clauses, hs)
        # model, sat = getAllModels(frozen_clauses, hs)

        if not sat:
            # print("OMUS:", hs)
            t_end_omus = time.time()
            benchmark_data['steps'] = steps
            benchmark_data['t_hitting_set'] = t_hitting_set
            benchmark_data['t_sat_check'] = t_sat_check
            benchmark_data['t_grow'] = t_grow
            benchmark_data['total_time'] = t_end_omus - t_start_omus
            benchmark_data['extension'] = extension
            benchmark_data['sat'] = 1 if sat_model else 0

            with open(outputfile, 'w') as file:
                file.write(json.dumps(benchmark_data)) # use `json.loads` to do the reverse
            return hs
        print("OrTools -", len(H), "Growing")

        # add all clauses ny building complement
        t_grow_start = time.time()
        C = grow(frozen_clauses, hs, model,  extension=extension)
        t_grow_end = time.time()
        t_grow.append(t_grow_end- t_grow_start)
        steps += 1

        if C in H:
            raise f"{hs} {C} is already in {H}"
        H.append(C)

def omusGurobi(cnf: CNF, extension = 3, sat_model = True, f = clause_length, outputfile = 'log.txt'):
    benchmark_data = {}
    benchmark_data['clauses'] = len(cnf.clauses)
    benchmark_data['avg_clause_len'] = mean([len(clause) for clause in cnf.clauses])

    t_hitting_set = []
    t_sat_check = []
    t_grow = []
    steps = 0
    t_start_omus = time.time()

    frozen_clauses = [frozenset(c for c in clause) for clause in cnf.clauses]

    # sanity check
    _, solved = checkSatClauses(frozen_clauses, {i for i in range(len(frozen_clauses))})

    assert solved == False, "Cnf is satisfiable"

    weights = clauses_weights(cnf.clauses, f)

    # H = [] # the complement of a max-sat call
    C = []

    gurobi_model = gurobiModel(cnf.clauses, weights)
    while(True):
        # compute optimal hitting set
        # F_prime =  optimalHittingSet(H, weights)
        print("omusGurobi -", steps, "gurobiOptimalHittingSet" )
        t_hs_start = time.time()
        hs =  gurobiOptimalHittingSet(cnf.clauses, gurobi_model, C)
        # print(hs)

        t_hs_end = time.time()
        t_hitting_set.append(t_hs_end - t_hs_start)
        print("omusGurobi -", steps, "checkSatClauses" )
        # check satisfiability of clauses
        if sat_model:
            t_sat_start = time.time()
            model, sat = checkSatClauses(frozen_clauses, hs)
            t_sat_end = time.time()
        else:
            t_sat_start = time.time()
            model, sat = getAllModels(frozen_clauses, hs)
            t_sat_end = time.time()
        t_sat_check.append(t_sat_end-t_sat_start)

        if not sat:
            gurobi_model.dispose()
            # print("OMUS:", hs)
            t_end_omus = time.time()
            benchmark_data['steps'] = steps
            benchmark_data['t_hitting_set'] = t_hitting_set
            benchmark_data['t_sat_check'] = t_sat_check
            benchmark_data['t_grow'] = t_grow
            benchmark_data['total_time'] = t_end_omus - t_start_omus
            benchmark_data['extension'] = extension
            benchmark_data['sat'] = 1 if sat_model else 0

            with open(outputfile, 'w') as file:
                file.write(json.dumps(benchmark_data)) # use `json.loads` to do the reverse
            return hs
        print("omusGurobi -", steps, "grow" )
        # add all clauses ny building complement
        t_grow_start = time.time()
        C = grow(frozen_clauses, hs, model,  extension=extension)
        t_grow_end = time.time()
        t_grow.append(t_grow_end- t_grow_start)
        steps += 1

def omusGurobiCold(cnf: CNF, extension = 3, sat_model = True, f = clause_length, outputfile = 'log.txt'):
    benchmark_data = {}
    benchmark_data['clauses'] = len(cnf.clauses)
    benchmark_data['avg_clause_len'] = mean([len(clause) for clause in cnf.clauses])

    t_hitting_set = []
    t_sat_check = []
    t_grow = []
    steps = 0
    t_start_omus = time.time()

    frozen_clauses = [frozenset(c for c in clause) for clause in cnf.clauses]

    # sanity check
    _, solved = checkSatClauses(frozen_clauses, {i for i in range(len(frozen_clauses))})

    assert solved == False, "Cnf is satisfiable"

    weights = clauses_weights(cnf.clauses, f)

    H = [] # the complement of a max-sat call
    # C = []

    while(True):
        # compute optimal hitting set
        # F_prime =  optimalHittingSet(H, weights)
        print("omusGurobiCold -", len(H), "Optimal Hitting Set" )
        t_hs_start = time.time()
        hs =  gurobiOptimalHittingSetCold(cnf.clauses, weights, H)
        t_hs_end = time.time()
        t_hitting_set.append(t_hs_end - t_hs_start)
        # check satisfiability of clauses
        print("omusGurobiCold -", len(H), "Check Sat" )
        if sat_model:
            t_sat_start = time.time()
            model, sat = checkSatClauses(frozen_clauses, hs)
            t_sat_end = time.time()
        else:
            t_sat_start = time.time()
            model, sat = getAllModels(frozen_clauses, hs)
            t_sat_end = time.time()
        t_sat_check.append(t_sat_end-t_sat_start)

        if not sat:
            # print("OMUS:", hs)
            t_end_omus = time.time()
            benchmark_data['steps'] = steps
            benchmark_data['t_hitting_set'] = t_hitting_set
            benchmark_data['t_sat_check'] = t_sat_check
            benchmark_data['t_grow'] = t_grow
            benchmark_data['total_time'] = t_end_omus - t_start_omus
            benchmark_data['extension'] = extension
            benchmark_data['sat'] = 1 if sat_model else 0

            with open(outputfile, 'w') as file:
                file.write(json.dumps(benchmark_data)) # use `json.loads` to do the reverse
            return hs

        # add all clauses ny building complement
        print("omusGurobiCold -", len(H), "Growing" )
        t_grow_start = time.time()
        C = grow(frozen_clauses, hs, model,  extension=extension)
        t_grow_end = time.time()
        t_grow.append(t_grow_end- t_grow_start)
        steps += 1
        H.append(C)

def main():
    l = 1
    m = 2
    n = 3
    p = 4
    s = 5
    cnf = CNF()
    cnf.append([-s])    # c1: ¬s
    cnf.append([s, -p]) # c2: s or ¬p
    cnf.append([p])     # c3: p
    cnf.append([-p, m]) # c4: ¬p or m
    cnf.append([-m, n]) # c5: ¬m or n
    cnf.append([-n])    # c6: ¬n
    cnf.append([-m, l]) # c7 ¬m or l
    cnf.append([-l])    # c8 ¬l
    # assert sorted(omusGurobiCold(cnf, 4 )) == sorted([0, 1, 2]), "SMUS error"
    assert sorted(omusGurobi(cnf, 3 )) == sorted([0, 1, 2]), "SMUS error"
    assert sorted(omusGurobi(cnf, 4 )) == sorted([0, 1, 2]), "SMUS error"
if __name__ == "__main__":
    main()
