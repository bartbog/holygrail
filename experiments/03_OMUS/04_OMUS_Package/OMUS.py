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
            neg_literal_count.update([-l for l in clause.intersection(literals) if -l in literals])
    # print("literal_count:\t\t", literal_count)
    # print("neg literal_count:\t", neg_literal_count)
    if diff == True:
        # literal_diff = literal_count.copy()
        literal_count.subtract(neg_literal_count)
    # print("diff literal_count:\t", literal_count)
    best_literal = literal_count.most_common(1)[0][0] if literal_count else None

    return best_literal

def findTopBestLiterals(clauses, F_prime, literals, best = 3):
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
            neg_literal_count.update([-l for l in clause.intersection(literals) if -l in literals])
    # print("literal_count:\t\t", literal_count)
    # print("neg literal_count:\t", neg_literal_count)
    # if diff == True:
        # literal_diff = literal_count.copy()
    literal_count.subtract(neg_literal_count)
    # print("diff literal_count:\t", literal_count)
    if literal_count == None:
        return None

    best_counts = literal_count.most_common()

    best_literals = set()
    for i in range(0, min(best, round(len(literal_count)) ) ):
        lit = best_counts[i][0]
        if -lit not in best_literals:
            best_literals.add(lit)
    return best_literals

def findTopBestLiteralsWithCounter(literal_count, neg_literal_count,literals, best = 3):
    """Find the best literal in the list of `literals' based on the number of clauses
    the literal hits.

    Arguments:
        clauses {iterable(set(int))} -- collection of clauses (sets of literals)
        F_prime {iterable(int)} -- Hitting set
        literals {iterable(int)} -- Candidate literals

    Returns:
        int -- literal hitting the most clauses in the not satisfied clauses of `clauses'
    """
    # literal_count = Counter({literal:0 for literal in literals})
    # neg_literal_count = Counter({literal:0 for literal in literals if -literal in literals})

    # for i, clause in enumerate(clauses):
    #     if i not in F_prime:
    #         literal_count.update(clause.intersection(literals))
    #         neg_literal_count.update([-l for l in clause.intersection(literals) if -l in literals])
    # print("literal_count:\t\t", literal_count)
    # print("neg literal_count:\t", neg_literal_count)
    # if diff == True:
        # literal_diff = literal_count.copy()
    # print(literal_count, neg_literal_count, literals, best)
    diffcount = Counter(literal_count)
    diffcount.subtract(neg_literal_count)
    # print("diff literal_count:\t", literal_count)
    if diffcount ==None:
        return None

    best_counts = dict(diffcount.most_common())

    best_literals = set()
    best_cnt = 0
    for i, (lit, _) in enumerate(best_counts.items()):
        if lit not in literals:
            continue
        if best_cnt == best:
            return best_literals
        if -lit not in best_literals:
            best_literals.add(lit)
            best_cnt += 1
    return best_literals

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

def extension2(clauses, F_prime, model, random_literal = False, maxcoverage=True):
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

def propmodel(clauses, F_prime, model):
    t_F_prime = set(F_prime)
    # precompute both
    lit_true = set(model)
    lit_false = set(-l for l in model)
    clause_added = True

    while(clause_added):
        literals_consider = set()
        clause_added = False
        # t_F_prime = set(new_F_prime)
        for i, clause in enumerate(clauses):
            if i in t_F_prime:
                continue # already in F_prime

            # Similar alternative:
            if len(clause.intersection(lit_true)) > 0:
                # a true literal, clause is true
                t_F_prime.add(i)
                clause_added = True
            else:
                unassigned = clause - lit_false
                if len(unassigned) == 1:
                    lit = next(iter(unassigned))
                    literals_consider.add(lit)


        if len(literals_consider) > 0:
            # removing lonely literals
            conflict_free = set(l for l in literals_consider if -l not in literals_consider)
            lit_true |= conflict_free
            lit_false |= set(-l for l in conflict_free)
            literals_consider -= conflict_free

            # Literals to add
            lits = findTopBestLiterals(clauses, t_F_prime, literals_consider, 1)
            lit_true |= lits
            lit_false |= set(-l for l in lits)

    c = set(l for l in lit_true if -l in lit_true)
    assert all([True if -l not in lit_true else False for l in lit_true]), f"Conflicting literals {c}"
    return t_F_prime, lit_true

def extension3(clauses, F_prime, model, diff= True):
    all_literals = frozenset.union(*clauses)

    # t_F_prime = set(F_prime)
    # t_model = set(model)
    if len(F_prime) == 0:
        lits = findTopBestLiterals(clauses, set(), all_literals, 1)
        t_F_prime, t_model = propmodel(clauses, set(), lits)
    else:
        t_F_prime, t_model = propmodel(clauses, F_prime, model)

    lit_true = set(t_model)
    lit_false = set(-l for l in t_model)

    # alternative, over all literals
    remaining_literals = all_literals - lit_true - lit_false
    if len(remaining_literals) == 0:
        return t_F_prime, t_model

    # counter with remaining literals coverage
    literal_counter = Counter({literal:0 for literal in remaining_literals})
    # counter with negated literals coverage
    neg_literal_counter = Counter({literal:0 for literal in remaining_literals if -literal in remaining_literals})

    for i, clause in enumerate(clauses):
        if i not in t_F_prime:
            intersect = clause.intersection(remaining_literals)
            literal_counter.update(intersect)
            neg_literal_counter.update([-l for l in intersect if -l in remaining_literals])

    while(len(remaining_literals) > 0):
        # removal of conflict free elements
        conflict_free = set(l for l in remaining_literals if -l not in remaining_literals)
        lit_true |= conflict_free
        remaining_literals -= conflict_free

        for l in conflict_free:
            del literal_counter[l]
            del literal_counter[-l]
            del neg_literal_counter[l]
            del neg_literal_counter[-l]

        lits = findTopBestLiteralsWithCounter(literal_counter, neg_literal_counter, remaining_literals, best = 1)

        lit_true |= lits
        lit_false |= set(-l for l in lits)
        remaining_literals -= ( lit_true | lit_false)

        for l in lits:
            del literal_counter[l]
            del literal_counter[-l]
            del neg_literal_counter[l]
            del neg_literal_counter[-l]

        clause_added = True

        while(clause_added):

            literals_consider = set()
            clause_added = False
            # t_F_prime = set(new_F_prime)
            for i, clause in enumerate(clauses):
                if i in t_F_prime:
                    continue # already in F_prime

                # Similar alternative:
                clause_literal_intersection = clause.intersection(lit_true)
                if len(clause_literal_intersection) > 0:
                    # a true literal, clause is true
                    t_F_prime.add(i)
                    clause_added = True

                    literal_counter.subtract(Counter([l for l in clause - clause_literal_intersection if l in remaining_literals]))
                    neg_literal_counter.subtract(Counter([-l for l in  clause - clause_literal_intersection if -l in remaining_literals]))
                else:
                    unassigned = clause - lit_false
                    if len(unassigned) == 1:
                        lit = next(iter(unassigned))
                        literals_consider.add(lit)

            if len(literals_consider) > 0:
                # removing lonely literals
                conflict_free = set(l for l in literals_consider if -l not in literals_consider)
                lit_true |= conflict_free
                lit_false |= set(-l for l in conflict_free)
                literals_consider -= conflict_free

                for l in conflict_free:
                    del literal_counter[l]
                    del literal_counter[-l]
                    del neg_literal_counter[l]
                    del neg_literal_counter[-l]

                # Literals to add
                lits = findTopBestLiteralsWithCounter(literal_counter, neg_literal_counter, literals_consider, best = 1)
                lit_true |= lits
                lit_false |= set(-l for l in lits)
                remaining_literals -= (lits | set(-l for l in lits) )

                for l in lits:
                    del literal_counter[l]
                    del literal_counter[-l]
                    del neg_literal_counter[l]
                    del neg_literal_counter[-l]

        # lit_true = set(t_model)
        # lit_false = set(-l for l in t_model)

        # remaining_literals -= lit_true
        # remaining_literals -= lit_false

    assert all([True if -l not in lit_true else False for l in lit_true])

    return t_F_prime, lit_true

def extension3withCounter(clauses, F_prime, model, diff= True):

    all_literals = frozenset.union(*clauses)
    t_F_prime = set(F_prime)
    t_model = set(model)
    if len(F_prime) == 0:
        lits = findTopBestLiterals(clauses, set(), all_literals, 1)
        t_F_prime, t_model = propmodel(clauses, set(), lits)
    else:
        t_F_prime, t_model = propmodel(clauses, t_F_prime, t_model)

    lit_true = set(t_model)
    lit_false = set(-l for l in t_model)

    # alternative, over all literals
    remaining_literals = all_literals - lit_true - lit_false

    while(len(remaining_literals) > 0):

        conflict_free = set(l for l in remaining_literals if -l not in remaining_literals)
        lit_true |= conflict_free
        remaining_literals -= conflict_free

        lits = findTopBestLiterals(clauses, t_F_prime, remaining_literals, 1)

        lit_true |= lits
        lit_false |= set(-l for l in lits)

        remaining_literals -= lit_true
        remaining_literals -= lit_false

        t_F_prime, t_model = propmodel(clauses, t_F_prime, lit_true)

        lit_true = set(t_model)
        lit_false = set(-l for l in t_model)

        remaining_literals -= lit_true
        remaining_literals -= lit_false

    assert all([True if -l not in lit_true else False for l in lit_true])

    return t_F_prime, lit_true


def extension5(clauses, F_prime, model):
    t_F_prime = set(F_prime)
    lit_true = set(model)
    # create gurobi model
    g_model = gp.Model('mipMaxSat')

    # model parameters
    # g_model.Params.LogFile = 'logs/'+datetime.now().strftime("%Y_%m_%d_%H_%M_%S")+'.log'
    g_model.Params.OutputFlag = 0
    g_model.Params.LogToConsole = 0
    g_model.Params.Threads = 8

    clause_literals = set(frozenset.union(*clauses))
    all_literals = clause_literals | set(-l for l in clause_literals)
    # dup_literals = [l for l in all_literals if -l in all_literals]

    n_literals = len(all_literals)
    # print("n_literals=", n_literals)
    distinct_literals = set(abs(l) for l in all_literals)
    # print("n_distinct_literals=", distinct_literals)

    # n_distinct_literals = len(distinct_literals)

    literal_count = Counter({literal:0 for literal in all_literals})

    for clause in clauses:
        literal_count.update(clause)

    d_literal_count = dict(literal_count)
    literal_coverage = {k: d_literal_count[k] for k in sorted(d_literal_count)}

    pos_literals = {key:i for i, key in enumerate([*literal_coverage])}

    # create the variables
    l = g_model.addMVar(shape= n_literals, vtype=GRB.BINARY, name="l")

    # weights = []
    max_sum = sum( [ v for k,v in literal_coverage.items()])
    # set objective : min sum xi*wi
    g_model.setObjective(sum( l[i] * literal_coverage[key] for i, key in enumerate([*literal_coverage]) if literal_coverage[key] > 0), GRB.MAXIMIZE)

    # g_model.addConstr(sum( l[i] * literal_coverage[key] for i, key in enumerate([*literal_coverage])) <= max_sum )

    # update the model
    g_model.addConstr(sum(l[i] for i in range(n_literals)) >= n_literals/2)
    g_model.addConstr(sum(l[i] for i in range(n_literals)) <= n_literals/2)

    # l_i + l_-i > 0
    # l_i + l_-i < 2
    # print("literal_coverage=",literal_coverage)
    # print("pos_literals=",pos_literals)
    # print("literal_coverage=",*literal_coverage)
    for literal in distinct_literals:
        pos_literal = pos_literals[literal]
        pos_neg_literal = pos_literals[-literal]
        # print(f"l[{pos_literal}] + l[{pos_neg_literal}] >= 1 ")
        # print(f"{literal} + {-literal} >= 1")
        # print(f"{literal} + {-literal} <= 1")
        # print(f"{pos_literal,l[pos_neg_literal] ]) >= 1)
        g_model.addConstr(sum([l[pos_literal],l[pos_neg_literal] ]) >= 1)
        g_model.addConstr(sum([l[pos_literal],l[pos_neg_literal] ]) <= 1)


    for i, clause in enumerate(clauses):
        if i not in F_prime :
            # print( " + ".join([f"l[{pos_literals[literal]}]" for literal in clause]), ">= 1")
            # print( " + ".join([str(literal) for literal in clause]), ">= 1")
            g_model.addConstr(sum(l[pos_literals[literal]] for literal in clause ) >= 1)
    for literal in model:
        g_model.addConstr(l[pos_literals[literal]] >= 1)
        g_model.addConstr(l[pos_literals[literal]] <= 1)
        # g_model.addConstr(sum([l[pos_literal],l[pos_neg_literal] ]) <= 1)
        # else:
    # for i, clause in enumerate(clauses):
    #     # if i not in F_prime :
    #     g_model.addConstr(sum(l[pos_literals[literal]] for literal in clause ) >= 1)
        #     g_model.addConstr()
    g_model.optimize()

    status = g_model.status
    if status in (GRB.INF_OR_UNBD, GRB.INFEASIBLE, GRB.UNBOUNDED):
        print('The model cannot be solved because it is infeasible or unbounded')
        return F_prime, model
        # sys.exit(1)

    if status == GRB.OPTIMAL:
        print('Optimization was stopped with status %d' % status)
        # sys.exit(0)

    # output hitting set
    for i,v in enumerate(g_model.getVars()):
        # print('%s %g' % (v.varName, v.x))
        print(f'l[{i}]\t{[*literal_coverage][i]}\t= {v.x}')
    # print(x)
    lit_true = set( key for i, key in enumerate([*literal_coverage]) if g_model.getVars()[i].x == 1)

    for i, clause in enumerate(clauses):
        # if i in t_F_prime:
        #     continue # already in F_prime
        if len(clause.intersection(lit_true)) > 0:
            t_F_prime.add(i)

    return t_F_prime, lit_true

# def extension3(clauses, F_prime, model):
#     t_F_prime = set(F_prime)
#     t_model = set(model)
#     remaining_literals = frozenset.union(*clauses) - t_model - set(-l for l in t_model )
#     t_model |= {l for l in remaining_literals if -l not in remaining_literals}
#     remaining_literals -= t_model - set(-l for l in t_model )
#     literal_count = Counter({literal:0 for literal in remaining_literals})
#     neg_literal_count = Counter({literal:0 for literal in remaining_literals})
#     for i, clause in enumerate(clauses):
#         literal_count.update(clause.intersection(remaining_literals))
#         neg_literal_count.update(-l for l in clause.intersection(remaining_literals))

#     literal_count.subtract(neg_literal_count)
#     d_literals = {k: v for k, v in sorted(dict(literal_count).items(), key=lambda item: item[1])}
#     while(len(d_literals) > 0):
#         lit = next(iter(d_literals))
#         t_model.add(lit)
#         del d_literals[lit]
#         del d_literals[-lit]

#     assert sorted(set( abs(l) for l in frozenset.union(*clauses))) == sorted(set(abs(l) for l in t_model))

#     for i, clause in enumerate(clauses):
#         if i not in t_F_prime and len(clause.intersection(t_model)) > 0:
#             t_F_prime.add(i)
#     return t_F_prime, t_model


# def extension3(clauses, F_prime, model, diff= True):
#     all_literals = frozenset.union(*clauses)
#     t_F_prime, t_model = propmodel(clauses, F_prime, model)
#     lit_true = set(t_model)
#     lit_false = set(-l for l in t_model)
#     clause_added = False

#     # alternative, over all literals
#     remaining_literals = all_literals - lit_true - lit_false
#     # conflict_free_literals = remaining_literals - set(-l for l in remaining_literals)



#     while(len(remaining_literals) > 0):
#         jmp = 0.50 *  ( len(clauses) - len(t_F_prime))

#         conflict_free = set(l for l in remaining_literals if -l not in remaining_literals)
#         lit_true |= conflict_free
#         remaining_literals -= conflict_free
#         cnt = jmp
#         # while(cnt > 0 and len(remaining_literals) > 0):

#         lit = findTopBestLiterals(clauses, t_F_prime, remaining_literals, jmp)

#         lit_true |= lits
#         lit_false |= {}

#         remaining_literals -= set({lit})
#         remaining_literals -= set({-lit})
#         cnt -= 1

#         t_F_prime, t_model = propmodel(clauses, t_F_prime, lit_true)

#         lit_true = set(t_model)
#         lit_false = set(-l for l in t_model)

#         remaining_literals -= lit_true
#         remaining_literals -= lit_false

#     assert all([True if -l not in lit_true else False for l in lit_true])

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
        4 : extension4,
        5 : extension5
    }

    # new_F_prime = frozenset(F_prime)

    new_F_prime, new_model = extensions[extension](clauses, F_prime, model)

    return complement(clauses, new_F_prime)

## OMUS algorithm
def omusOrTools(cnf: CNF, extension = 3, sat_model = True, f = clause_length, outputfile = 'log.txt', greedy = False, maxcoverage = False):
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

        C = grow(frozen_clauses, hs, model,  extension=extension)
        t_grow_end = time.time()
        t_grow.append(t_grow_end- t_grow_start)
        steps += 1
        s_grow.append(len(C))

        if C in H:
            raise f"{hs} {C} is already in {H}"
        H.append(C)

def omusGurobi(cnf: CNF, extension = 3, sat_model = True, f = clause_length, outputfile = 'log.txt', greedy = False, maxcoverage = False):
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

    # H = [] # the complement of a max-sat call
    C = []

    gurobi_model = gurobiModel(cnf.clauses, weights)
    while(True):
        # compute optimal hitting set
        # F_prime =  optimalHittingSet(H, weights)
        # print("omusGurobi -", steps, "gurobiOptimalHittingSet" )
        t_hs_start = time.time()
        hs =  gurobiOptimalHittingSet(cnf.clauses, gurobi_model, C)
        # print(hs)
        t_hs_end = time.time()
        t_hitting_set.append(t_hs_end - t_hs_start)
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
            benchmark_data['sat'] = 1 if sat_model else 0
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

        C = grow(frozen_clauses, hs, model,  extension=extension)
        t_grow_end = time.time()
        t_grow.append(t_grow_end- t_grow_start)
        s_grow.append(len(C))
        print(f"{steps}: t_hs={round(t_hs_end - t_hs_start, 2)}s t_C={round(t_grow_end- t_grow_start, 2)}s t_Sat = {round(t_sat_end-t_sat_start, 2)}  |C|={len(C)} |clauses|={len(frozen_clauses)}")
        print(f"\t{hs}")

        steps += 1

def omusGurobiCold(cnf: CNF, extension = 3, sat_model = True, f = clause_length, outputfile = 'log.txt', greedy = False, maxcoverage = False):
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
            benchmark_data['sat'] = 1 if sat_model else 0
            benchmark_data['s_hs'] = s_hs
            benchmark_data['s_grow'] = s_grow


            with open(outputfile, 'w') as file:
                file.write(json.dumps(benchmark_data)) # use `json.loads` to do the reverse
            return hs

        # add all clauses ny building complement
        print("omusGurobiCold -", len(H), "Growing" )
        t_grow_start = time.time()
        C = grow(frozen_clauses, hs, model,  extension=extension)
        # new_F_prime, new_model = extension2(frozen_clauses, hs, model, random_literal =(not greedy), maxcoverage=maxcoverage )
        # C = complement(frozen_clauses, new_F_prime)
        t_grow_end = time.time()
        t_grow.append(t_grow_end- t_grow_start)
        s_grow.append(len(C))
        steps += 1
        H.append(C)
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
    # f_clauses = [frozenset(clause) for clause in omus_cnf().clauses]
    # c = [
    #     [1, 2, 3],
    #     [-1, -2],
    #     [1, -2],
    #     [-2],
    #     [-2, -1]
    # ]
    # f_c = [frozenset(clause) for clause in c]
    # print(f_c)
    # print(extension5(f_c, [], [-3]))
    # assert sorted(omusGurobiCold(cnf, 4 )) == sorted([0, 1, 2]), "SMUS error"
    # print(omusGurobi(bacchus_cnf(), 3))
    # assert sorted(omusGurobi(omus_cnf(), 3 )) == sorted([0, 1, 2]), "SMUS error"
    zebra_instance()
    # assert sorted(omusGurobi(cnf, 4 )) == sorted([0, 1, 2]), "SMUS error"
if __name__ == "__main__":
    main()
