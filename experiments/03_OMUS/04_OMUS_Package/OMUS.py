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
import math
import random

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
from OMUS_utils import HittingSetSolver

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
    LITERAL_ORDERING = 4

class BestLiteral(IntEnum):
    COUNT_PURE_ONLY = 1
    COUNT_POLARITY = 2

class UnitLiteral(IntEnum):
    IGNORE = 0
    RANDOM = 1
    SINGLE_POLARITY = 2
    POLARITY = 3
    IMMEDIATE = 4

class SatModel(IntEnum):
    RANDOM = 1
    BEST_CLAUSES_VALIDATED = 2
    BEST_CLAUSE_WEIGHTS_COVERAGE = 3
    BEST_WEIGHTED_UNASSIGNED_CLAUSE_COVERAGE = 4
    ALL = 5

def time_func(f):
    @wraps(f)
    def decor(*args, **kwargs):
        start = time.time()
        res = f(*args, **kwargs)
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
    lits = set( abs(lit) for lit in frozenset.union(*cnf_clauses))

    with Solver() as s:
        added = s.append_formula(cnf_clauses, no_return=False)
        solved = s.solve()
        model = s.get_model()
    if solved:
        mapped_model = set(lit for lit in model if abs(lit) in lits )
        return mapped_model, solved
    else:
        return None, solved

def defaultExtension(cnf_clauses, F_prime, model, parameters):
    return F_prime

def unitprop(clauses, weights, F_prime, model, parameters):
    """`Extension1' unit propagate the model to find all clauses hit by the current
    assignment of F_prime.

    Arguments:
        clauses {iterable(iterable(int))} -- collection of clauses (sets of literals)
        F_prime {iterable(int)} -- Hitting set, optimal set of clauses hitting H
        model {iterable(int)} -- model of clauses in F_prime

    Returns:
        iterable(int), iterable(int) -- Grown hitting set, new model of hitting set
    """
    # parameters
    count_clauses = parameters['count_clauses']
    sorting = parameters['sorting']
    best_unit_literal = parameters['best_unit_literal']

    best_literal_counter = parameters['best_counter_literal']

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
                if len(unassigned) == 1 and best_unit_literal == UnitLiteral.IMMEDIATE:
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

def maxprop(clauses, weights, F_prime, model, parameters):
    # parameters
    count_clauses = parameters['count_clauses']
    sorting = parameters['sorting']
    best_unit_literal = parameters['best_unit_literal']
    best_literal_counter = parameters['best_counter_literal']

    # init counter
    all_literals = frozenset.union(*clauses)
    t_F_prime, t_model = unitprop(clauses,weights, F_prime, model, parameters)
    lit_true = set(t_model)
    lit_false = set(-l for l in t_model)

    # alternative, over all literals
    remaining_literals = all_literals - lit_true - lit_false
    conflict_free_literals = remaining_literals - set(-l for l in remaining_literals)

    cnt = Counter({literal:0 for literal in remaining_literals})
    for i,clause in enumerate(clauses):
        if i not in t_F_prime:
            lit_intersect_cl = remaining_literals.intersection(clause)
            cnt.update(lit_intersect_cl)

    while(len(conflict_free_literals) > 0):

        if best_literal_counter == BestLiteral.COUNT_PURE_ONLY:
            best_lit = max(conflict_free_literals, key=lambda i: cnt[i])
        else:
            # 4.2 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
            best_lit = max(conflict_free_literals, key=lambda i: cnt[i] - cnt[-i])

        lit_true.add(best_lit)
        lit_false.add(-best_lit)

        t_F_prime, t_model = unitprop(clauses, weights, t_F_prime, lit_true, parameters)

        lit_true = set(t_model)
        lit_false = set(-l for l in t_model)

        remaining_literals = all_literals - lit_true - lit_false
        conflict_free_literals = remaining_literals - set(-l for l in remaining_literals)

    conflictual_literals = set(remaining_literals)

    assert all([True if -l in conflictual_literals else False for l in conflictual_literals])

    # propagate all remaining literals
    while len(conflictual_literals) > 0:
        if best_literal_counter == BestLiteral.COUNT_PURE_ONLY:
            best_lit = max(conflict_free_literals, key=lambda i: cnt[i])
        else:
            # 4.2 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
            best_lit = max(conflict_free_literals, key=lambda i: cnt[i] - cnt[-i])

        conflictual_literals.remove(best_lit)
        # because the unit prop created a conflict-free one, we must check
        if -best_lit in conflictual_literals:
            conflictual_literals.remove(-best_lit)

        lit_true.add(best_lit)
        lit_false.add(-best_lit)

        # unit propagate new literal
        t_F_prime, t_model = unitprop(clauses, weights, t_F_prime, lit_true, parameters)

        lit_true = set(t_model)
        lit_false = set(-l for l in t_model)

        # code was probably not finished because the latter was missing
        remaining_literals = all_literals - lit_true - lit_false
        conflictual_literals = set(remaining_literals)

    assert all([True if -l not in lit_true else False for l in lit_true])

    return t_F_prime, lit_true

def greedy_param(clauses, weights, F_prime, model, parameters):
    # parameters
    count_clauses = parameters['count_clauses']
    sorting = parameters['sorting']
    best_unit_literal = parameters['best_unit_literal']
    best_literal_counter = parameters['best_counter_literal']

    # preprocessing
    lit_true = set(model)
    lit_false = set(-l for l in model)
    cl_true = set(F_prime)
    lit_unk = set(frozenset.union(*clauses)) - lit_true - lit_false
    # Pre-processing is necessary
    if sorting in [ClauseSorting.UNASSIGNED,ClauseSorting.WEIGHTED_UNASSIGNED, ClauseSorting.WEIGHTS ]:
        cl_unk = list(set(range(len(clauses))) - cl_true)
    else:
        cl_unk = set(range(len(clauses))) - cl_true

    # literal- clause counter
    cnt = {lit:0 for lit in lit_unk}

    for i in list(cl_unk):
        clause = clauses[i]
        unassign_lits = clause - lit_false - lit_true
        # clause is false, remove it
        if len(unassign_lits) == 0:
            cl_unk.remove(i)
        # validated clause
        elif len(lit_true.intersection(clause)) > 0:
            cl_true.add(i)
            cl_unk.remove(i)
        else:
            for lit in unassign_lits:
                if count_clauses == ClauseCounting.VALIDATED:
                    # check if count number of clauses
                    cnt[lit] += 1
                elif count_clauses == ClauseCounting.WEIGHTS:
                    # clause weight
                    cnt[lit] += weights[i]
                elif count_clauses == ClauseCounting.WEIGHTED_UNASSIGNED:
                    # clause weight/# litterals assigned
                    cnt[lit] += weights[i]/len(unassign_lits)

    while(len(cl_unk) > 0):
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
                # cl_unk.sort(reverse=True, key= lambda i: weights[i] / max(1, len(clauses[i] - lit_true - lit_false)) )
                cl_unk.sort(reverse=True, key= lambda i: weights[i] / len(clauses[i] - lit_true - lit_false) if len(clauses[i] - lit_true - lit_false)> 0 else 0 )
            elif sorting == ClauseSorting.LITERAL_ORDERING:
                cl_unk.sort(reverse=False, key= lambda cl_id: min(abs(lit) for lit in clauses[cl_id]))

        # check single polarity literals
        tofix = set()
        for lit in set(abs(lit) for lit in lit_unk):
            if not lit in cnt or cnt[lit] == 0:
                tofix.add(-lit)
            elif not -lit in cnt or cnt[-lit] == 0:
                tofix.add(lit)

        if len(tofix) > 0:
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
            lit_false.add(-lit)
            lit_unk.remove(lit)
            del cnt[lit]

        if len(lit_unk) > 0:
            # 4. Literal choice
            # 4.1 Literal with highest [clause count] / [sum clause weights] / [ (sum of clause weights)/#unassigned]
            if best_literal_counter == BestLiteral.COUNT_PURE_ONLY:
                best_lit = max(lit_unk, key=lambda i: cnt[i])
                # print(lit_unk)
                # print(cnt)
                # lit_max_val = max(lit_unk, key=lambda i: cnt[i])
                # best_lit = random.choice([lit for lit in lit_unk if cnt[lit] == cnt[lit_max_val]])
            else:
                # 4.2 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                best_lit = max(lit_unk, key=lambda i: cnt[i] - cnt[-i])
                # lit_max_val = max(lit_unk, key=lambda i: cnt[i] - cnt[-i])
                # best_lit = random.choice([lit for lit in lit_unk if (cnt[lit] - cnt[-lit]) == (cnt[lit_max_val] - cnt[-lit_max_val])])

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
            elif len(lit_true.intersection(clause)) > 0:
                cl_unk.remove(i)
                cl_true.add(i)
            # validate unit literals
            elif len(unassign_lits) == 1 and best_unit_literal != UnitLiteral.IGNORE:
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
                    lit_unk.remove(-lit)
                    del cnt[-lit]
                else:
                    unit_literals.add(lit)
                    # for lit in unassign_lits:
                    # check if count number of clauses
                    if count_clauses == ClauseCounting.VALIDATED:
                        cnt[lit] += 1
                    # clause weight
                    elif count_clauses == ClauseCounting.WEIGHTS:
                        cnt[lit] += weights[i]
                    # clause weight/# litterals assigned
                    elif count_clauses == ClauseCounting.WEIGHTED_UNASSIGNED:
                        cnt[lit] += weights[i]/len(unassign_lits)
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

        while len(unit_literals) > 0:
            # 4. Literal choice
            # 4.2 Literal with highest [clause count] / [sum clause weights] / [ (sum of clause weights)/#unassigned]
            if best_unit_literal == UnitLiteral.SINGLE_POLARITY:
                best_lit = max(unit_literals, key=lambda i: cnt[i])
                # lit_max_val = max(unit_literals, key=lambda i: cnt[i])
                # best_lit = random.choice([lit for lit in unit_literals if cnt[lit] == cnt[lit_max_val]])
                # best_lit = min(unit_literals, key=lambda i: cnt[-i])
            elif best_unit_literal == UnitLiteral.POLARITY:
            # 4.3 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                # lit_max_val = max(unit_literals, key=lambda i: cnt[i] - cnt[-i])
                # best_lit = random.choice([lit for lit in unit_literals if (cnt[lit] - cnt[-lit]) == (cnt[lit_max_val] - cnt[-lit_max_val])])
                best_lit = max(unit_literals, key=lambda i: cnt[i] - cnt[-i])
            else:
                best_lit = next(iter(unit_literals))
            # literal
            lit_true.add(best_lit)
            lit_false.add(-best_lit)
            lit_unk.remove(best_lit)
            lit_unk.remove(-best_lit)
            unit_literals.remove(best_lit)
            if -best_lit in unit_literals:
                unit_literals.remove(-best_lit)
            del cnt[best_lit]
            del cnt[-best_lit]

    # print(lit_true)
    # print(cl_true)
    # print( set(i for i, clause in enumerate(clauses) if len(clause.intersection(lit_true)) > 0))
    # assert all(False if -lit in lit_true else True for lit in lit_true)
    cl_true = set(i for i, clause in enumerate(clauses) if len(clause.intersection(lit_true)) > 0)
    return cl_true, lit_true

    # ## Dist : Tailoring local Search for Partial MaxSat (Shaowei Cai, Chuan Luo, Joh, Thornton, Kaile Su)
    # # optimizing using local search
    # maxsteps = 1000
    # # already good assignment
    # assignment = set(lit_true)
    # best_assignment = set(lit_true)

    # sp = 0.001
    # soft_clauses = set(i for i in range(len(clauses)) if i not in F_prime)
    # hard_clauses = set(i for i in F_prime)
    # # h_score
    # h_weights = {i:1 for i in hard_clauses}

    # # Dist adopts the weighted version of hard score and the unweighted version of soft score, as it employs a clause weighting scheme 
    # # that works only for hard clauses.
    # h_score = lambda x: sum(h_weights[i] for i in hard_clauses if -x in clauses[i]) - sum(h_weights[i]  for i in hard_clauses if x in clauses[i])
    # s_score = lambda x: sum(1 for i in soft_clauses if -x in clauses[i]) - sum(1 for i in soft_clauses if x in clauses[i])

    # # The increase of the number/total weight of satisfied soft clauses by flipping x
    # # h_score = lambda x: sum(h_weights[i] for i in hard_clauses if -x in clauses[i]) - sum(h_weights[i]  for i in hard_clauses if x in clauses[i])
    # # s_score = lambda x: sum(1 for i in soft_clauses if -x in clauses[i]) - sum(1 for i in soft_clauses if x in clauses[i])Z

    # # total weight of validated clauses
    # cost = lambda x: sum(1 for i in soft_clauses if len(x.intersection(clauses[i])) == 0 )

    # # initilization best cost
    # cost_best_sol = cost(best_assignment)
    # t_best_sol = cost_best_sol

    # falsified_hard_clause = lambda x: list(i for i in hard_clauses if len(x.intersection(clauses[i])) == 0)
    # falsified_soft_clause = lambda x: list(i for i in soft_clauses if len(x.intersection(clauses[i])) == 0)

    # start_time = time.time()
    # steps_not_updating = 0

    # # Dist Algorithm
    # for step in range(maxsteps):
    #     print(step, end= '\r')
    #     # print(cost(assignment), cost_best_sol)
    #     falsified_hard = falsified_hard_clause(assignment)

    #     if len(falsified_hard) == 0 and cost(assignment) < cost_best_sol:
    #         print(f"\t \t Improving {cost_best_sol} => {cost(assignment)}", end='\r')
    #         best_assignment = assignment
    #         cost_best_sol = cost(assignment)
    #         steps_not_updating = 0
    #     else:
    #         steps_not_updating += 1

    #     if(time.time() - start_time > cutoff or steps_not_updating > 50):
    #         break

    #     H = list()
    #     S = dict()
    #     for x in assignment:
    #         h_score_x = h_score(x)
    #         s_score_x = s_score(x)
    #         if h_score_x > 0:
    #             H.append(x)
    #         elif s_score_x > 0 and h_score_x == 0:
    #             S[x] = s_score_x

    #     # S = {x: s_score(x) for x in assignment if s_score(x) > 0 and h_score(x) > 0}
    #     if len(H) > 0:
    #         # variable randomly picked from H
    #         v = random.choice(H)
    #     elif len(S) > 0:
    #         # variable in S with greatest sscore
    #         v = max(S, key=lambda lit: S[lit])
    #     else:
    #         # TODO: add smoothing factor
    #         for cl in h_weights:
    #             clause = clauses[cl]
    #             if len(assignment.intersection(clause)) > 0 and h_weights[cl] > 1:
    #                 h_weights[cl] -= 1
    #             elif len(assignment.intersection(clause)) == 0:
    #                 h_weights[cl] += 1

    #         falsified_hard = falsified_hard_clause(assignment)
    #         if len(falsified_hard) > 0:
    #             ci = random.choice(falsified_hard)
    #         else:
    #             falsified_soft = falsified_soft_clause(assignment)
    #             ci = random.choice(falsified_soft)
    #         clause = clauses[ci]
    #         v = max(clause, key=lambda lit: s_score(lit))

    #     assignment = set(-lit if abs(lit) == abs(v) else lit for lit in assignment)

    # if (cost_best_sol < t_best_sol):
    #     print("diff:", cost_best_sol, t_best_sol )

    # print("\t\t\t\t\t\tTime local_search = ", time.time() - start_time)
    # if cost_best_sol <= sum(weights[i] for i, clause in enumerate(clauses) if i not in F_prime):
    #     cl_true = {i for i, clause in enumerate(clauses) if len(best_assignment.intersection(clause))  > 0}
    #     return  cl_true, best_assignment
    # else:
    #     return cl_true, lit_true

def SATLike(clauses, weights, F_prime, model, parameters):
    # Things tested:
    # - Add already visited assignment => when that happens, we generate new initial assignment
    # parameters
    cutoff = parameters['cutoff']
    sp = 0.01
    max_steps = 100000 # very big number
    h_inc = parameters['h_inc'] # Paper value = 3
    s_inc = parameters['s_inc'] # Paper value = 1
    # optimziation parameters
    max_iters_no_change = 100
    max_restarts = 3
    # Paper : Unit Propagation-based initilization is not useful for SATLike on WPMS
    # initial assignment is generated randomly for WPMS

    # assignment = set()
    assignment = set(model)
    # cl_true = set(F_prime)

    all_lits = set(frozenset.union(*clauses))
    all_lits |= set(-lit for lit in all_lits)

    hard_clauses = frozenset(F_prime)
    soft_clauses = frozenset(i for i in range(len(clauses))) - hard_clauses

    lit_clauses_neighborhood = dict.fromkeys(all_lits, [])
    w = [0 for i in range(len(clauses))]

    lit_unk = list(all_lits - assignment - set(-l for l in assignment))
    # lit_unk = list(all_lits)

    # literals and their negation

    while(len(lit_unk) > 0):
        lit = random.choice(lit_unk)
        assignment.add(lit)
        # lit_false.add(-lit)
        lit_unk.remove(lit)
        lit_unk.remove(-lit)

    # assignment = set(lit_true)
    best_assignment = None
    best_cost = sum(weights[i] for i in soft_clauses)

    falsified_hard_clauses = set()
    falsified_soft_clauses = set()

    # optimization of scores usage
    scores = {}
    for lit in assignment:
        scores[lit] = 0
        scores[-lit] = 0
        # score_lit = 0
        lit_clauses = lit_clauses_neighborhood[lit]
        for clause_id in lit_clauses:
            clause = clauses[clause_id]
            scores[lit] -= weights[clause_id]
            scores[-lit] += weights[clause_id]

        neg_lit_clauses = lit_clauses_neighborhood[-lit]
        for clause_id in neg_lit_clauses:
            clause = clauses[clause_id]
            scores[-lit] -= weights[clause_id]
            scores[lit] += weights[clause_id]


    for clause_id, clause in enumerate(clauses):
        # filling lit -> clause edge
        for lit in clause:
            lit_clauses_neighborhood[lit].append(clause_id)

        if clause_id in hard_clauses:
            # for each hard clause, we associate an integer number as its weight which is initiliazed to 1
            w[clause_id] = 1
            if len(clause.intersection(assignment)) == 0:
                falsified_hard_clauses.add(clause_id)
        else:
            # for each soft clause we use the original weight
            w[clause_id] = weights[clause_id]
            if len(clause.intersection(assignment)) == 0:
                falsified_soft_clauses.add(clause_id)

    v = 0

    # variabels 
    useless_iterations = 0
    total_iterations = 0
    iters_no_change = 0
    longest_iterations =0
    restarts = 0
    # Cut off timer
    start_time = time.time()
    for step in range(max_steps):
        falsified_hard_clauses = set(i for i in hard_clauses if len(clauses[i].intersection(assignment)) == 0 )
        falsified_soft_clauses = set(i for i in soft_clauses if len(clauses[i].intersection(assignment)) == 0 )

        # cost_assignment = sum(weights[i] for i in falsified_soft_clauses)
        cost_assignment = sum(weights[i] for i in falsified_soft_clauses)

        if len(falsified_hard_clauses) == 0 and cost_assignment < best_cost:
            # print(f"{best_cost} => {cost_assignment}")
            if iters_no_change > longest_iterations:
                longest_iterations = iters_no_change
            iters_no_change = 0
            best_assignment = assignment
            best_cost = cost_assignment
        else:
            useless_iterations += 1

        # update score only on clauses impacted by variable v
        if v != 0:
            # variable flipped to -v
            lit = -v
            scores[lit] = 0
            scores[-lit] = 0
            # score_lit = 0
            lit_clauses = lit_clauses_neighborhood[lit]
            for clause_id in lit_clauses:
                clause = clauses[clause_id]
                scores[lit] -= weights[clause_id]
                scores[-lit] += weights[clause_id]

            neg_lit_clauses = lit_clauses_neighborhood[-lit]
            for clause_id in neg_lit_clauses:
                clause = clauses[clause_id]
                scores[-lit] -= weights[clause_id]
                scores[lit] += weights[clause_id]

        D = [lit for lit in scores if scores[lit] > 0]
        if len(D) > 0:
            # BMS =  best from multiple selections
            # t random variables with replacement and returns the one with the highest score
            vars_D = set(random.choices(D, k=50))
            v = max(vars_D, key= lambda lit: scores[lit])
        else:
            # udpate weights of clauses by Weighting-PMS
            p = random.uniform(0, 1)
            if p > sp:
                for cl in falsified_hard_clauses:
                    w[cl] += h_inc
                for cl in falsified_soft_clauses:
                    if w[cl] < s_inc:
                        w[cl] += 1
            else:
                satisfied_hard_clauses = hard_clauses - falsified_hard_clauses
                satisfied_soft_clauses = soft_clauses - falsified_soft_clauses
                for cl in satisfied_hard_clauses:
                    if w[cl] > 1:
                        w[cl] -= h_inc
                for cl in satisfied_soft_clauses:
                    if w[cl] > 1:
                        w[cl] -= 1
            if len(falsified_hard_clauses) > 0:
                c = random.choice(list(falsified_hard_clauses))
            else:
                c = random.choice(list(falsified_soft_clauses))
            clause = clauses[c]

            v = max(clause, key=lambda lit: scores[lit])
        # flip sign of variable v in assignment

        assignment = set(-lit if abs(v) == abs(lit) else lit for lit in assignment)

        total_iterations += 1
        if time.time() - start_time > cutoff:
            if iters_no_change > longest_iterations:
                longest_iterations = iters_no_change
            break

        if (iters_no_change > max_iters_no_change):
            # restarts +=1
            iters_no_change = 0
            # Force new valid assignment
            # assignment = set()
            assignment = set(model)
            lit_unk = list(all_lits - assignment - set(-l for l in assignment))

            while(len(lit_unk) > 0):
                lit = random.choice(lit_unk)
                assignment.add(lit)
                # lit_false.add(-lit)
                lit_unk.remove(lit)
                lit_unk.remove(-lit)
            for lit in assignment:
                scores[lit] = 0
                scores[-lit] = 0
                # score_lit = 0
                lit_clauses = lit_clauses_neighborhood[lit]
                for clause_id in lit_clauses:
                    clause = clauses[clause_id]
                    scores[lit] -= weights[clause_id]
                    scores[-lit] += weights[clause_id]

                neg_lit_clauses = lit_clauses_neighborhood[-lit]
                for clause_id in neg_lit_clauses:
                    clause = clauses[clause_id]
                    scores[-lit] -= weights[clause_id]
                    scores[lit] += weights[clause_id]

        iters_no_change += 1

    # print(f"Useful iterations [%] {round((1 - useless_iterations/total_iterations)*100, 2)} on total_iterations={total_iterations}")
    # print(f"Longest iterations without progress {longest_iterations}")

    if best_assignment == None:
        cl_true = set(i for i, clause in enumerate(clauses) if len(clause.intersection(assignment)) > 0)
        if(not F_prime <= cl_true):
            raise f"F_prime not validated {F_prime}, {cl_true}"

        return cl_true, assignment
    else:
        cl_true = set(i for i, clause in enumerate(clauses) if len(clause.intersection(best_assignment)) > 0)
        return cl_true, best_assignment

def greedy_no_param(clauses,weights,  F_prime, model, parameters):
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

def maxsat_fprime(clauses, weights, F_prime, model, parameters):
    t_F_prime = set(F_prime)

    wcnf = WCNF()
    for i, clause in enumerate(clauses):
        if i in F_prime:
            wcnf.append(list(clause))
        else:
            wcnf.append(list(clause), weight=weights[i])

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
def gurobiOptimalHittingSetAll(clauses, gurobi_model, C):
    # trivial case
    if len(C) == 0:
        return []

    # print(C)
    for ci in C:
        # print(ci)
        # add new constraint sum x[j] * hij >= 1
        addSetGurobiModel(clauses, gurobi_model, ci)

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
        'complement' : defaultExtension,
        'unitprop' : unitprop,
        'maxprop' : maxprop,
        'greedy_param' : greedy_param,
        'greedy_no_param' : greedy_no_param,
        'maxsat' : maxsat_fprime,
        'satlike' : SATLike
    }
    # print("clauses=", clauses)
    # print("weights=",weights)
    # print("F_prime=", F_prime)
    # print("model=", model)
    # print("parameters=", parameters)
    new_F_prime, new_model = extensions[extension](clauses,weights,  F_prime, model, parameters)

    return complement(clauses, new_F_prime)

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

    # default parameters
    extension = parameters['extension']
    outputfile = parameters['output']
    # Performance
    cnf_clauses = cnf.clauses
    frozen_clauses = [frozenset(c for c in clause) for clause in cnf_clauses]

    # check if all literals are in the clauses else need to be mapped
    # checkVariableNaming(frozen_clauses)

    # sanity check
    (_, (_, solved)) = checkSatClauses(frozen_clauses, {i for i in range(len(frozen_clauses))})

    assert solved == False, "Cnf is satisfiable"

    if weights == None:
        weights = clauses_weights(cnf.clauses, f)
    
    assert len(weights) == len(cnf_clauses), "clauses and weights of same length"

    gurobi_model = gurobiModel(cnf.clauses, weights)

    C = []
    while(True):
        # compute optimal hitting set
        t_exec_hs, hs =  gurobiOptimalHittingSet(cnf.clauses, gurobi_model, C)
        # print(f"Steps={steps}\t, |hs|={len(hs)}")

        t_hitting_set.append(t_exec_hs)
        s_hs.append(len(hs))

        # check satisfiability of clauses
        (t_exec_model, (model, sat)) = checkSatClauses(frozen_clauses, hs)
        t_sat_check.append(t_exec_model)
        # print(f"Sat check={t_exec_model}: {model}")

        # if not sat or steps > max_steps_main:
        if not sat:
            print("Steps=", steps, "OMUS=", hs)
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
            benchmark_data['omus'] = not sat
            # ppprint(benchmark_data)
            if outputfile != None :
                with open(outputfile, 'w') as file:
                    file.write(json.dumps(benchmark_data)) # use `json.loads` to do the reverse
            return hs

        t_exec_grow, C = grow(frozen_clauses, weights, hs, model,  parameters)

        print(f"Steps={steps}\t, |hs|={len(hs)}, |C|={len(C)}", end='\r')
        s_grow.append(len(C))
        t_grow.append(t_exec_grow)
        # print("\t C=", C)
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

def smus():
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

    parameters = {
        'extension': 'satlike',
        'output': "smus_log.json",
        'cutoff' : 5,
        'h_inc' : 3,
        's_inc' : 1,
        'sp': 0.0001
    }
    return omus(cnf, parameters)

def main():
    smus()
    # omusGurobi(bacchus_cnf(), 3 )
    # omusGurobi(omus_cnf(), 3 
if __name__ == "__main__":
    main()
