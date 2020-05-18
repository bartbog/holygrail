#!/usr/bin/env python
# coding: utf-8

# standard libraries
from __future__ import print_function
import os
import re
import sys
from pathlib import Path
from enum import Enum, IntEnum
import json
import time
from collections import Counter
from datetime import datetime
from statistics import mean
from functools import wraps

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

class ClauseCounting(IntEnum):
    VALIDATED = 1
    WEIGHTS = 2
    WEIGHTED_UNASSIGNED = 3

class ClauseSorting(IntEnum):
    IGNORE = 0
    WEIGHTS = 1
    UNASSIGNED = 2
    WEIGHTED_UNASSIGNED = 3

class BestCounterLiteral(IntEnum):
    PURE_ONLY = 1
    POLARITY = 2

class UnitLiteral(IntEnum):
    RANDOM = 1
    PURE = 2
    POLARITY = 3
    IMMEDIATE = 4

class SatModel(IntEnum):
    RANDOM = 1
    BEST = 2
    ALL = 3

def time_func(f):
    @wraps(f)
    def decor(*args, **kwargs):
        start = time.time()
        res = f(*args, **kwargs)
        end_time = time.time()
        return end_time-start, res
    return decor

def time_func3(f):
    @wraps(f)
    def decor(*args, **kwargs):
        x, y, z = args
        start = time.time()
        res = f(x, y, z, **kwargs)
        end_time = time.time()
        return end_time-start, res
    return decor

def time_func4(f):
    @wraps(f)
    def decor(*args, **kwargs):
        x, y, z, w = args
        start = time.time()
        res = f( x, y, z, w, **kwargs)
        end_time = time.time()
        return end_time-start, res
    return decor

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

@time_func
def checkSatClauses(clauses, F_prime):
    if len(F_prime) == 0 :
        return [], True

    cnf_clauses = [clauses[i] for i in F_prime]

    mapping, reverse_mapping = mapping_clauses(cnf_clauses)
    mapped_clauses = map_clauses(cnf_clauses, mapping)
    # print(mapped_clauses)
    with Solver() as s:
        added = s.append_formula(mapped_clauses, no_return=False)
        solved = s.solve()
        model = s.get_model()
    if solved:
        mapped_model = frozenset(map(lambda literal: reverse_mapping[abs(literal)]*sign(literal) , model))
        return mapped_model, solved
    else:
        return None, solved

@time_func
def getAllModels(clauses, F_prime):
    if not F_prime :
        return [], True

    cnf_clauses = [clauses[i] for i in F_prime]

    mapping, reverse_mapping = mapping_clauses(cnf_clauses)
    mapped_clauses = map_clauses(cnf_clauses, mapping)

    with Solver() as s:
        added = s.append_formula(mapped_clauses, no_return=False)
        solved = s.solve()

        if solved:
            mapped_models = []
            for i, m in enumerate(s.enum_models()):
                mapped_models.append(frozenset(map(lambda literal: reverse_mapping[abs(literal)]*sign(literal) , m)))
            return mapped_models, solved
        else:
            return None, solved

@time_func
def getBestModel(clauses, F_prime):
    if not F_prime :
        return [], True

    cnf_clauses = [clauses[i] for i in F_prime]

    mapping, reverse_mapping = mapping_clauses(cnf_clauses)
    mapped_clauses = map_clauses(cnf_clauses, mapping)

    with Solver() as s:
        added = s.append_formula(mapped_clauses, no_return=False)
        solved = s.solve()

        if solved:
            best_model = None
            best_coverage = 0
            for i, m in enumerate(s.enum_models()):
                model_coverage = 0
                mapped_model = frozenset(map(lambda literal: reverse_mapping[abs(literal)]*sign(literal) , m))
                coverage = sum([1 for idx, clause in  enumerate(clauses) if idx not in F_prime and len(clause.intersection(mapped_model)) > 0 ])
                if coverage >= best_coverage:
                    best_coverage = coverage
                    best_model = mapped_model
            return best_model, solved
        else:
            return None, solved

def findBestLiteral(clauses, F_prime, literals, parameters):
    """Find the best literal in the list of `literals' based on the number of clauses
    the literal hits.

    Arguments:
        clauses {iterable(set(int))} -- collection of clauses (sets of literals)
        F_prime {iterable(int)} -- Hitting set
        literals {iterable(int)} -- Candidate literals

    Returns:
        int -- literal hitting the most clauses in the not satisfied clauses of `clauses'
    """
    polarity_clauses = parameters['polarity_literals']
    unassigned_clauses = parameters['unassigned_clauses']
    weighted_clauses = parameters['weighted_clauses']

    literal_count = Counter({literal:0 for literal in literals})

    for i, clause in enumerate(clauses):
        if i not in F_prime:
            literal_count.update(clause.intersection(literals))

    return max(literals, key=lambda i: literal_count[i] - literal_count[-i])


def defaultExtension(cnf_clauses, F_prime, model, parameters):
    return F_prime

def extension1(clauses, weights, F_prime, model, parameters):
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

def extension2(clauses, weights, F_prime, model, parameters):
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
            lit = findBestLiteral(clauses, t_F_prime, conflict_free_literals, maxcoverage)
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
            literal = findBestLiteral(clauses, t_F_prime, conflictual_literals, maxcoverage)
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

def extension3(clauses, weights, F_prime, model, parameters):
    # parameters
    count_clauses = parameters['count_clauses']
    sorting = parameters['sorting']
    best_unit_literal = parameters['best_unit_literal']
    best_literal_counter = parameters['best_counter_literal']

    if not isinstance(count_clauses, ClauseCounting):
        print(f"Wong input = {count_clauses}. Defaulting to # validated clauses")
        count_clauses = ClauseCounting.VALIDATED

    if best_unit_literal != None and not isinstance(best_unit_literal, UnitLiteral):
        print(f"Wong input = {best_unit_literal}. Defaulting to random literal choice")
        best_unit_literal = UnitLiteral.RANDOM

    # preprocessing
    lit_true = set(model)
    lit_false = set(-l for l in model)
    cl_true = set(F_prime)
    lit_unk = set(frozenset.union(*clauses)) - lit_true - lit_false
    # clause ordering
    # Pre-processing is necessary
    cl_unk = [i for i in range(len(clauses)) if i not in F_prime]

    # literal- clause counter
    cnt = {lit:0 for lit in lit_unk}

    for i in list(cl_unk):
        clause = clauses[i]
        unassign_lits = clause - lit_false
        # clause is false, remove it
        if len(unassign_lits) == 0:
            cl_unk.remove(i)
        # validated clause
        elif lit_true.intersection(clause):
            cl_true.add(i)
            cl_unk.remove(i)
        else:
            # unassign_lits = clause - lit_false - lit_true
            # clause = clauses[i]
            unassgn_lits = clause.intersection(lit_unk)
            for lit in unassgn_lits:
                if count_clauses == ClauseCounting.VALIDATED:
                    # check if count number of clauses
                    cnt[lit] += 1
                elif count_clauses == ClauseCounting.WEIGHTS:
                    # clause weight
                    cnt[lit] += weights[i]
                elif count_clauses == ClauseCounting.WEIGHTED_UNASSIGNED:
                    # clause weight/# litterals assigned
                    cnt[lit] += weights[i]/len(unassgn_lits)

    if isinstance(sorting, ClauseSorting):
        # clause sorting based on weights
        if sorting == ClauseSorting.WEIGHTS:
            cl_unk.sort(reverse=True, key= lambda i: weights[i])
        # clause sorting based on # unassigned literals
        elif sorting == ClauseSorting.UNASSIGNED:
            cl_unk.sort(reverse=True, key= lambda i: len(clauses[i] - lit_true - lit_false))
        # clause sorting based on weight of clause /# unassigned literals
        elif sorting == ClauseSorting.WEIGHTED_UNASSIGNED:
            cl_unk.sort(reverse=True, key= lambda i: weights[i] / len(clauses[i] - lit_true - lit_false) )

    while(len(cl_unk) > 0):
        # check single polarity literals
        tofix = set()
        for lit in set(abs(lit) for lit in lit_unk):
            if not lit in cnt or cnt[lit] == 0:
                tofix.add(-lit)
            elif not -lit in cnt or cnt[-lit] == 0:
                tofix.add(lit)

        # check if clauses need reordering (only useful for unit literal)
        if isinstance(sorting, ClauseSorting):
            # clause sorting based on weights
            if sorting == ClauseSorting.WEIGHTS:
                cl_unk.sort(reverse=True, key= lambda i: weights[i])
            # clause sorting based on # unassigned literals
            elif sorting == ClauseSorting.UNASSIGNED:
                cl_unk.sort(reverse=True, key= lambda i: len(clauses[i] - lit_true - lit_false))
            # clause sorting based on # unassigned literals
            elif sorting == ClauseSorting.WEIGHTED_UNASSIGNED:
                cl_unk.sort(reverse=True, key= lambda i: weights[i] / max(1, len(clauses[i] - lit_true - lit_false)) )

        #print(cl_unk, tofix, lit_true, lit_false)
        if len(tofix) > 0:
            #print("Tofix", tofix)
            # fix all single polarity literals
            lit_true |= tofix
            lit_unk -= tofix
            tofix_neg = set(-l for l in tofix)
            lit_false |= tofix_neg
            lit_unk -= tofix_neg

        # Validated all pure literals
        pure_lits = {lit for lit in lit_unk if -lit not in lit_unk}

        for lit in pure_lits:
            lit_true.add(lit)
            lit_true.add(-lit)
            lit_unk.remove(lit)
            del cnt[lit]

        if len(lit_unk) > 0:
            # 4. Literal choice
            # 4.1 Literal with highest [clause count] / [sum clause weights] / [ (sum of clause weights)/#unassigned]
            if best_literal_counter == BestCounterLiteral.PURE_ONLY:
                best_lit = max(lit_unk, key=lambda i: cnt[i])
            else:
                # 4.2 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                best_lit = max(lit_unk, key=lambda i: cnt[i] - cnt[-i])

            del cnt[best_lit]
            del cnt[-best_lit]

            lit_unk.remove(best_lit)
            lit_unk.remove(-best_lit)

            lit_true.add(best_lit)
            lit_false.add(-best_lit)

        cnt = {lit:0 for lit in lit_unk}

        unit_literals = set()

        for i in set(cl_unk):
            clause = clauses[i]
            unassign_lits = clause - lit_false

            # clause is false, remove it
            if len(unassign_lits) == 0:
                cl_unk.remove(i)
            # validated clause
            elif lit_true.intersection(clause):
                cl_true.add(i)
                cl_unk.remove(i)
            # validate unit literals
            elif len(unassign_lits) == 1 and best_unit_literal != None:
                lit = next(iter(unassign_lits))
                if best_unit_literal == UnitLiteral.IMMEDIATE:
                    cl_true.add(i)
                    # cl_unk
                    cl_unk.remove(i)
                    # literal
                    lit_true.add(lit)
                    lit_false.add(-lit)
                    lit_unk.remove(lit)
                    del cnt[lit]
                    if -lit in lit_unk:
                        lit_unk.remove(-lit)
                        del cnt[-lit]
                else:
                    unit_literals.add(lit)
            else:
                for lit in unassign_lits:
                    # check if count number of clauses
                    if count_clauses == ClauseCounting.VALIDATED:
                        cnt[lit] += 1
                    # clause weight
                    elif count_clauses == ClauseCounting.WEIGHTS:
                        cnt[lit] += weights[i]
                    # clause weight/# litterals assigned
                    elif count_clauses == ClauseCounting.WEIGHTED_UNASSIGNED:
                        cnt[lit] += weights[i]/len(unassign_lits)

        if  len(unit_literals) > 0 and best_unit_literal in [UnitLiteral.RANDOM,  UnitLiteral.PURE, UnitLiteral.POLARITY]:
            # 4. Literal choice
            # 4.1 Random literal
            if best_unit_literal == UnitLiteral.RANDOM:
                best_lit = next(iter(unit_literals))
            # 4.2 Literal with highest [clause count] / [sum clause weights] / [ (sum of clause weights)/#unassigned]
            elif best_unit_literal == UnitLiteral.PURE:
                best_lit = max(unit_literals, key=lambda i: cnt[i])
            elif best_unit_literal == UnitLiteral.POLARITY:
            # 4.3 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                best_lit = max(unit_literals, key=lambda i: cnt[i] - cnt[-i])
            # literal
            lit_true.add(best_lit)
            lit_false.add(-best_lit)
            lit_unk.remove(best_lit)
            del cnt[best_lit]

            if -lit in lit_unk:
                lit_unk.remove(-best_lit)
                del cnt[-best_lit]

    return cl_true, lit_true

def unknown_clauses(clauses,weights,  F_prime, model, parameters):
    cl_true = set(F_prime)
    cl_unk = set( range(len(clauses)) ) - cl_true

    lit_true = set(model)
    lit_false = set(-l for l in model)
    lit_unk = set(frozenset.union(*clauses)) - lit_true - lit_false

    # init counter
    cnt = Counter({literal:0 for literal in lit_unk})
    for i in cl_unk:
        cnt.update(clauses[i])

    # as long as some clauses are unassigned
    while len(cl_unk) > 0:
        # check single polarity literals
        tofix = set()
        for lit in set(abs(lit) for lit in lit_unk):
            if not lit in cnt or cnt[lit] == 0:
                tofix.add(-lit)
            elif not -lit in cnt or cnt[-lit] == 0:
                tofix.add(lit)

        #print(cl_unk, tofix, lit_true, lit_false)
        if len(tofix) > 0:
            #print("Tofix", tofix)
            # fix all single polarity literals
            lit_true |= tofix
            lit_unk -= tofix
            tofix_neg = set(-l for l in tofix)
            lit_false |= tofix_neg
            lit_unk -= tofix_neg
        elif len(lit_unk) > 0:
            # print(cnt, lit_unk, cl_unk)
            # choose best
            # bestlit = max(lit_unk, key=lambda i: cnt[i])
            # other definition of 'best'
            bestlit = max(lit_unk, key=lambda i: cnt[i] - cnt[-i])
            #print("Best", bestlit, cnt[bestlit], cnt[-bestlit])

            lit_true.add(bestlit)
            lit_unk.remove(bestlit)
            lit_false.add(-bestlit)
            lit_unk.remove(-bestlit)
            del cnt[bestlit]
            del cnt[-bestlit]

        # update clauses (cl_unk will be modified in place)
        for idx in list(cl_unk):
            clause = clauses[idx]
            unassgn = clause - lit_false
            if len(unassgn) == 0:
                # false, no need to check again
                cl_unk.remove(idx)
            # print(idx, clause, cl_unk, clause.intersection(lit_false))
            elif len(clause.intersection(lit_true)) > 0:
                # true, store and remove from counter
                cl_unk.remove(idx)
                cl_true.add(idx)
                cnt = cnt - Counter(clause)
            elif len(unassgn) == 1:
                # unit...
                # print(lit_true, unassgn)
                bestlit = next(iter(unassgn))
                lit_true.add(bestlit)
                lit_unk.remove(bestlit)
                lit_false.add(-bestlit)
                lit_unk.remove(-bestlit)
                del cnt[bestlit]
                del cnt[-bestlit]
                cl_unk.remove(idx)
                cl_true.add(idx)

    return cl_true, lit_true

def extension4(clauses, weights, F_prime, model, parameters):
    t_F_prime = set(F_prime)

    wcnf = WCNF()
    for i, clause in enumerate(clauses):
        if i in F_prime:
            wcnf.append(list(clause))
        else:
            wcnf.append(list(clause), weight=1)

    with RC2(wcnf) as rc2:
        t_model = rc2.compute()

    for i, clause in enumerate(clauses):
        if i not in t_F_prime and len(clause.intersection(t_model)) > 0:
            t_F_prime.add(i)

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

@time_func
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
@time_func
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
@time_func
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

@time_func
def grow(clauses, weights, F_prime, model, parameters):
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
    extension = parameters['extension']

    extensions = {
        0 : defaultExtension,
        1 : extension1,
        2 : extension2,
        3 : extension3,
        4 : extension4
    }
    # print("clauses=", clauses)
    # print("weights=",weights)
    # print("F_prime=", F_prime)
    # print("model=", model)
    # print("parameters=", parameters)
    new_F_prime, new_model = extensions[extension](clauses,weights,  F_prime, model, parameters)

    return complement(clauses, new_F_prime)

## OMUS algorithm
def omusOrTools(cnf: CNF, parameters,  f = clause_length):
    benchmark_data = {}
    benchmark_data['clauses'] = len(cnf.clauses)
    benchmark_data['avg_clause_len'] = mean([len(clause) for clause in cnf.clauses])

    t_hitting_set = []
    t_sat_check = []
    t_grow = []
    steps = 0
    t_start_omus = time.time()
    s_hs = []
    s_grow = []
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
        s_hs.append(len(hs))
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
            benchmark_data['s_hs'] = s_hs
            benchmark_data['s_grow'] = s_grow
            with open(outputfile, 'w') as file:
                file.write(json.dumps(benchmark_data)) # use `json.loads` to do the reverse
            return hs
        print("OrTools -", len(H), "Growing")

        # add all clauses ny building complement
        t_grow_start = time.time()
        # new_F_prime, new_model = extension2(frozen_clauses, hs, model, random_literal =(not greedy), maxcoverage=maxcoverage )
        # C = complement(frozen_clauses, new_F_prime)
        C = grow(frozen_clauses, hs, model, parameters)

        t_grow_end = time.time()
        t_grow.append(t_grow_end- t_grow_start)
        steps += 1
        s_grow.append(len(C))

        if C in H:
            raise f"{hs} {C} is already in {H}"
        H.append(C)

def omusGurobi(cnf: CNF, parameters, f = clause_length):
    benchmark_data = {}
    benchmark_data['clauses'] = len(cnf.clauses)
    benchmark_data['avg_clause_len'] = mean([len(clause) for clause in cnf.clauses])


    t_hitting_set = []
    t_sat_check = []
    t_grow = []
    steps = 0
    t_start_omus = time.time()
    s_hs = []
    s_grow = []

    frozen_clauses = [frozenset(c for c in clause) for clause in cnf.clauses]

    # sanity check
    _, solved = checkSatClauses(frozen_clauses, {i for i in range(len(frozen_clauses))})

    assert solved == False, "Cnf is satisfiable"

    weights = clauses_weights(cnf.clauses, f)

    H = [] # the complement of a max-sat call
    C = []

    gurobi_model = gurobiModel(cnf.clauses, weights)
    while(True):
        # compute optimal hitting set
        t_exec, hs =  gurobiOptimalHittingSet(cnf.clauses, gurobi_model, C)
        t_hitting_set.append(t_exec)
        s_hs.append(len(hs))

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
            print("OMUS:", hs)
            t_end_omus = time.time()
            benchmark_data['steps'] = steps
            benchmark_data['t_hitting_set'] = t_hitting_set
            benchmark_data['t_sat_check'] = t_sat_check
            benchmark_data['t_grow'] = t_grow
            benchmark_data['total_time'] = t_end_omus - t_start_omus
            benchmark_data['extension'] = extension
            # benchmark_data['sat'] = 1 if sat_model else 0
            benchmark_data['s_hs'] = s_hs
            benchmark_data['s_grow'] = s_grow
            with open(outputfile, 'w') as file:
                file.write(json.dumps(benchmark_data)) # use `json.loads` to do the reverse
            return hs
        # print("omusGurobi -", steps, "grow" )
        # add all clauses ny building complement
        t_grow_start = time.time()
        # new_F_prime, new_model = extension2(frozen_clauses, hs, model, random_literal =(not greedy), maxcoverage=maxcoverage )
        # C = complement(frozen_clauses, new_F_prime)

        C = grow(frozen_clauses, weights, hs, model, parameters)

        if C in H:
            raise f"{hs} {C} is already in {H}"
        H.append(C)
        t_grow_end = time.time()
        t_grow.append(t_grow_end- t_grow_start)
        s_grow.append(len(C))
        print(f"{steps}: t_hs={round(t_hs_end - t_hs_start, 2)}s t_C={round(t_grow_end- t_grow_start, 2)}s t_Sat = {round(t_sat_end-t_sat_start, 2)}  |C|={len(C)} |clauses|={len(frozen_clauses)}")
        print(f"\n\t{hs}\n")

        steps += 1

def omusGurobiCold(cnf: CNF, parameters, extension = 3, f = clause_length):
    benchmark_data = {}
    benchmark_data['clauses'] = len(cnf.clauses)
    benchmark_data['avg_clause_len'] = mean([len(clause) for clause in cnf.clauses])

    steps = 0
    t_hitting_set = []
    t_sat_check = []
    t_grow = []
    t_start_omus = time.time()
    s_hs = []
    s_grow = []
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
        s_hs.append(len(hs))
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
            benchmark_data['s_hs'] = s_hs
            benchmark_data['s_grow'] = s_grow


            with open(outputfile, 'w') as file:
                file.write(json.dumps(benchmark_data)) # use `json.loads` to do the reverse
            return hs

        # add all clauses ny building complement
        print("omusGurobiCold -", len(H), "Growing" )
        t_grow_start = time.time()

        C = grow(frozen_clauses, hs, model, parameters, extension=extension)
        # new_F_prime, new_model = extension2(frozen_clauses, hs, model, random_literal =(not greedy), maxcoverage=maxcoverage )
        # C = complement(frozen_clauses, new_F_prime)
        t_grow_end = time.time()
        t_grow.append(t_grow_end- t_grow_start)
        s_grow.append(len(C))
        steps += 1
        H.append(C)

def checkVariableNaming(clauses):
    lits = set(abs(l) for l in frozenset.union(*clauses))
    min_lit = min(lits)
    assert min_lit == 1, f"First Literal at {min_lit}"
    max_lit = max(lits)
    assert sorted(set(i for i in range(min_lit, max_lit))) == sorted(lits), "Be careful missing literals"

def omus(cnf: CNF, parameters, f = clause_length, weights = None ):
    # benchmark variables
    steps = 0
    t_hitting_set = []
    t_sat_check = []
    t_grow = []
    t_start_omus = time.time()
    s_hs = []
    s_grow = []

    # parameters
    bestModel = parameters['sat_model']
    extension = parameters['extension']
    outputfile = parameters['output']
    # print("Parameters:")
    # ppprint(parameters)

    # Performance
    frozen_clauses = [frozenset(c for c in clause) for clause in cnf.clauses]

    # check if all literals are in the clauses else need to be mapped
    # checkVariableNaming(frozen_clauses)

    # sanity check
    (_, (_, solved)) = checkSatClauses(frozen_clauses, {i for i in range(len(frozen_clauses))})

    assert solved == False, "Cnf is satisfiable"

    if weights == None:
        weights = clauses_weights(cnf.clauses, f)

    gurobi_model = gurobiModel(cnf.clauses, weights)

    C = []

    while(True):
        # compute optimal hitting set
        t_exec_hs, hs =  gurobiOptimalHittingSet(cnf.clauses, gurobi_model, C)

        t_hitting_set.append(t_exec_hs)
        s_hs.append(len(hs))

        # check satisfiability of clauses
        if bestModel == SatModel.BEST:
            (t_exec_model, (model, sat)) = getBestModel(frozen_clauses, hs)
            # print(model, sat)
        elif bestModel == SatModel.ALL:
            (t_exec_model, (models, sat)) = getAllModels(frozen_clauses, hs)
            # print(models, sat)
        else:
            (t_exec_model, (model, sat)) = checkSatClauses(frozen_clauses, hs)
        t_sat_check.append(t_exec_model)
        # print(f"Sat check={t_exec_model}: {model}")


        if not sat:
            # print("Steps=", steps, "OMUS=", hs)
            gurobi_model.dispose()

            # Benchmark data
            benchmark_data = {}
            benchmark_data['steps'] = steps
            benchmark_data['OMUS'] = list(hs)
            benchmark_data['clauses'] = len(cnf.clauses)
            benchmark_data['avg_clause_len'] = mean([len(clause) for clause in cnf.clauses])
            benchmark_data['parameters'] = parameters
            benchmark_data['clause_length'] = f.__name__
            benchmark_data['t_hitting_set'] = t_hitting_set
            benchmark_data['t_sat_check'] = t_sat_check
            benchmark_data['t_grow'] = t_grow
            benchmark_data['extension'] = extension
            benchmark_data['s_hs'] = s_hs
            benchmark_data['s_grow'] = s_grow
            ppprint(benchmark_data)
            if outputfile != None :
                with open(outputfile, 'w') as file:
                    file.write(json.dumps(benchmark_data)) # use `json.loads` to do the reverse
            return hs
        if bestModel == SatModel.ALL and len(models) == 0:
            t_exec_grow, C = grow(frozen_clauses, weights, hs, set(),  parameters)
        elif bestModel == SatModel.ALL:
            C = None
            # Cbis = None
            # Crest = []
            t_exec_grow = 0
            best_weight = sum(weights)
            C_sz = len(frozen_clauses)
            for idx, model in enumerate(models):
                t_model_grow, C_grown = grow(frozen_clauses, weights, hs, model,  parameters)
                w_grown = sum([weight for i, weight in enumerate(weights) if i in C_grown])
                if w_grown <= best_weight:
                    best_weight = w_grown
                    C = C_grown
                # if len(C_grown) < C_sz:
                #     C_sz = len(C_grown)
                #     C = C_grown
                #     Cbis = C_grown
                # else:
                #     Crest.append(C_grown)
                # print(C_grown)
                t_exec_grow += t_model_grow
            t_exec_grow = t_exec_grow/len(models)
            # C = Cbis.intersection(*Crest)
        else:
            t_exec_grow, C = grow(frozen_clauses, weights, hs, model,  parameters)
        t_grow.append(t_exec_grow)
        s_grow.append(len(C))
        print(f"Steps={steps}\t, |hs|={len(hs)}, |C|={len(C)}")
        steps += 1


def bacchus_cnf():
    cnf = CNF()
    cnf.append([6, 2])    # c1: ¬s
    cnf.append([-6, 2])    # c1: ¬s
    cnf.append([-2, 1])    # c1: ¬s
    cnf.append([-1])    # c1: ¬s
    cnf.append([-6,8])    # c1: ¬s
    cnf.append([6, 8])    # c1: ¬s
    cnf.append([2, 4])    # c1: ¬s
    cnf.append([-4, 5])    # c1: ¬s
    cnf.append([7, 5])    # c1: ¬s
    cnf.append([-7, 5])    # c1: ¬s
    cnf.append([-5, 3])    # c1: ¬s
    cnf.append([-3])    # c1: ¬s
    return cnf

def zebra_instance():
    # f_path = "data/easy_instances/bf0432-007.cnf"
    f_path = "data/easy_instances/zebra_v155_c1135.cnf"
    clauses = []
    t_clauses = []
    for clause in CNF(from_file=f_path).clauses:
        if clause not in t_clauses and len(clause) > 0:
            clauses.append(frozenset(clause))
            t_clauses.append(clause)
    cnf = CNF(from_clauses=clauses)
    print(omusGurobi(cnf, extension = 3))

def omus_cnf():
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
    return cnf

def main():
    # omusGurobi(bacchus_cnf(), 3 )
    # omusGurobi(omus_cnf(), 3 )
    # assert sorted(omusGurobiCold(cnf, 4 )) == sorted([0, 1, 2]), "SMUS error"
    # assert sorted(omusGurobi(omus_cnf(), 3 )) == sorted([0, 1, 2]), "SMUS error"
    zebra_instance()
if __name__ == "__main__":
    main()
