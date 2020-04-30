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

# pysat library
from pysat.solvers import Solver, SolverNames
from pysat.formula import CNF, WCNF
from pysat.examples.fm import FM
from pysat.examples.musx import MUSX

# or-tools library
from ortools.linear_solver import pywraplp

# numpy
#import numpy as np

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

sign = lambda x: (1, -1)[x < 0]

def print_omus(H, h, F_prime, C, weights, clauses, write_file=True):
    d = {
        'H':H,
        'h':h,
        'F_prime':F_prime,
        'C':C, 
        #'weights': weights,
        #'clauses': clauses
    }
    
    ppprint(d)

def complement(F, F_prime):
    return {i for i in range(len(F))} - {i for i in F_prime}

def flatten_set(H):
    return set([val for sublist in H for val in sublist])

def clause_length(x):
    # weighted based on the number of literals inside the clause
    # return 1
    return len(x)

def cnf_weights(cnf, weight = clause_length):
    return [weight(clause) for clause in cnf.clauses]

def clauses_weights(clauses, weight = clause_length):
    return [weight(clause) for clause in clauses]
   
def create_data_model(H, weights):
    """Stores the data for the problem."""
    
    # indices of clauses used
    indices_H = sorted(flatten_set(H))
    
    n_vars_H = len(indices_H)
    n_constraints = len(H)
    
    data = {}
    data['indices'] = indices_H
    data['num_constraints'] = n_constraints
    data['bounds'] = [1] * n_constraints
    data['num_vars'] = n_vars_H 
    data['obj_coeffs'] = {index:weights[index] for index in indices_H}

    # constraint coefficients hij = 1 if variable x_j is in set h_i
    constraint_coeffs = [[0 for _ in range(n_vars_H)] for _ in range(n_constraints)] 

    for j in range(n_constraints):
        hj = H[j]
        for i in range(n_vars_H):
            if indices_H[i] in hj:
                constraint_coeffs[j][i] = 1

    data['constraint_coefficients'] = constraint_coeffs
    
    # matching clause indices with position in list of clause indices 
    # ex: {3 : 0, 7: 1, ....} clause 3 position 0, clause 7 position 1, ...
    data['matching_table'] = {idx : i for i, idx in enumerate(indices_H) }
    return data

def mapping_clauses(clauses):

    union_clauses = frozenset.union(*clauses)

    sorted_vars = frozenset(sorted(map(abs, union_clauses)))

    mapping = {elem:i+1 for i, elem in enumerate(sorted_vars)}
    reversemapping = {i+1:elem for i, elem in enumerate(sorted_vars)}

    return mapping, reversemapping

def map_clauses(clauses, mapping):

    newclauses = [[mapping[abs(literal)]*sign(literal) for literal in clause] for clause in clauses]

    return newclauses

def checkSatClauses(clauses, F_prime):
    if not F_prime :
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

# # Optimal Hitting set MIP implementation

def optimalHittingSet(H, weights):
    # trivial case
    if len(H) == 0:
        return []

    data = create_data_model(H, weights)
    # [START solver]
    # Create the mip solver with the CBC backend.
    solver = pywraplp.Solver('OptimalHittingSet', 
                             pywraplp.Solver.BOP_INTEGER_PROGRAMMING)
    # [END solver]
    
    # [START variables]
    #infinity = solver.infinity()
    x = {}
    for j in data['indices']:
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
    
    # Solve the problem and print the solution.
    # [START print_solution]
    status = solver.Solve()

    if status == pywraplp.Solver.OPTIMAL:
        #print('Objective value =', solver.Objective().Value())
        # From Tias: should it not just return the hitting set?
        h = [j for j in data['indices'] if x[j].solution_value() == 1]
        # ohs = 
        return h

        # return [x[j].solution_value() for j in data['indices']]
    else:
        print('The problem does not have an optimal solution.', status)
        return []
    # [END print_solution]

def checkConflict(literals):
    for l in literals:
        assert -l not in literals, f"conflicting literals are present {l}, {-l}"

def default_extension(cnf_clauses, F_prime, model):
    return F_prime

def find_best_literal(clauses, remaining_clauses, conflictual_literals):
    literal_validatable_clauses = {l : 0 for l in conflictual_literals}
    
    validatable_clauses = {}
    for c in remaining_clauses:
        clause = clauses[c]
        
        for literal in clause:
            if literal in conflictual_literals:
                validatable_clauses.add(c)
    
    for c in validatable_clauses:
        clause = clauses[c]
        for literal in clause:
            if literal in conflictual_literals:
                literal_validatable_clauses[literal] += 1
    
    # https://stackoverflow.com/questions/268272/getting-key-with-maximum-value-in-dictionary
    best_literal = max(literal_validatable_clauses.iterkeys(), key=(lambda key: literal_validatable_clauses[key]))
    return best_literal
    
def getLiteralsSubsetClauses(cnf_clauses, subsetClauses):

    s = set()
    
    for c in subsetClauses:
        clause = cnf_clauses[c]
        for literal in clause:
            s.add(literal)
    return s

def getClausesValidatedByLiterals(cnf_clauses, subset_clauses, literals):
    validated_clauses = set()

    for literal in literals:
        for c in subset_clauses:
            clause = cnf_clauses[c]
            if literal in clause:
                validated_clauses.add(c)
    return validated_clauses

def maxsat_fprime(cnf_clauses, F_prime):
    new_F_prime = set(F_prime)

    return new_F_prime

def extension1(cnf_clauses, F_prime, model):
    new_F_prime = set(F_prime)
    # precompute both
    lit_true = set(model)
    lit_false = set(-l for l in model)

    lit_added = True
    while(lit_added):
        lit_added = False
        for i, clause in enumerate(cnf_clauses):
            if i in new_F_prime:
                pass # already in F_prime

            # Similar alternative:
            if len(clause.intersection(lit_true)) > 0:
                # a true literal, clause is true
                new_F_prime.add(i)
            else:
                # check for unit propagation
                unassigned = clause - lit_false
                if len(unassigned) == 1:
                    new_F_prime.add(i)
                    # add literal to the model
                    lit = next(iter(unassigned))
                    lit_true.add(lit)
                    lit_false.add(-lit)
                    lit_added = True
    
    # Tias: you probably want this to return the 'new' model so it can be used by other functions
    return new_F_prime, lit_true

def extension2(cnf_clauses, F_prime, model, random_literal = True):
    new_F_prime, new_model = extension1(cnf_clauses, F_prime, model)

    lit_true = set(new_model)
    lit_false = set(-l for l in new_model)
    
    all_literals = frozenset.union(*cnf_clauses) - lit_false - lit_true
    lit_added = True
    while(lit_added):
        lit_added = False
        for i, clause in enumerate(cnf_clauses):
            if i in new_F_prime:
                pass
            if len(clause.intersection(lit_true)) > 0:
                # a true literal, clause is true
                # print("is that even possible ?????")
                new_F_prime.add(i)
            else:
                unassigned = clause - lit_false

                if len(unassigned) > 0:
                    # print("unassigned:", unassigned)
                    new_F_prime.add(i)
                    # add literal to the model
                    lit = next(iter(unassigned))
                    lit_true.add(lit)
                    lit_false.add(-lit)
                    lit_added = True
                # do something .....

    # print(all_literals)

    return new_F_prime, new_model

def extension3(cnf_clauses, F_prime, model):
    return F_prime

def extension4(cnf_clauses, F_prime, model):
    return F_prime
    
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
        0 : default_extension,
        1 : extension1,
        2 : extension2,
        3 : extension3,
        4 : extension4
    }
    
    
    new_F_prime = frozenset(F_prime)

        # is this meant to be a loop? extensions should just be one??
    new_F_prime, new_model = extensions[extension](clauses, new_F_prime, model)
    
    # print("F_prime:", F_prime, "model:", model)
    # print("new_F_prime:", new_F_prime, "new_model:", new_model)
    
    return complement(clauses, new_F_prime)


# # OMUS algorithm

def omus(cnf: CNF, extension = 0, f = clause_length):
    frozen_clauses = [frozenset(clause) for clause in cnf.clauses]
    weights = clauses_weights(cnf.clauses, f)
    H = [] # the complement of a max-sat call
    C = None

    while(True):
        print("Step", len(H))
        # compute optimal hitting set
        F_prime = optimalHittingSet(H, weights)
        print("--- optimal hitting set")
        # check satisfiability of clauses
        model, sat = checkSatClauses(frozen_clauses, F_prime)
        print("--- satisfiability")
        if not sat:
            print(len(H))
            return F_prime
        
        # add all clauses ny building complement
        C = grow(frozen_clauses, F_prime, model,  extension=extension)
        print("hs", F_prime, "model", model, "sat", sat)
        print("C", C)

        if C in H:
            raise "MCS is already in H'"
        
        H.append(C)
        # printing
