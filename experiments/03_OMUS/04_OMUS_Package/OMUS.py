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



# # Test extensions on simple cases
## MIP model

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
    return set([i for i in range(len(F))]) - set(F_prime)

# def unique_clauses_hs(H):
#    return flatten_set(H)

def flatten_set(H):
    return set([val for sublist in H for val in sublist])

def f(x):
    # weighted based on the number of literals inside the clause
    # return 1
    return len(x)

def cnf_weights(cnf, weight = f):
    return [weight(clause) for clause in cnf.clauses]

def clauses_weights(clauses, weight = f):
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

def checkSatClauses(clauses, F_prime):
    c = [clauses[i] for i in F_prime]
    with Solver() as s:
        added = s.append_formula(c, no_return=False)
        solved = s.solve()
    return solved    


# # Optimal Hitting set MIP implementation

def optimalHittingSet(H, weights):
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
        return [x[j].solution_value() for j in data['indices']]
    else:
        print('The problem does not have an optimal solution.', status)
        return []
    # [END print_solution]


def checkConflict(literals):
    for l in literals:
        assert -l not in literals, f"conflicting literals are present {l}, {-l}"

def default_extension(cnf_clauses, F_prime):
    return F_prime

def extension1(cnf_clauses, F_prime):
    """
    
        Add all clauses that are true based on the assignment by the model of Fprime
        :param cnf_clauses: a collection of clauses (list of literals).
        :param F_prime: hitting set : a list of clauses.
        
        :type cnf_clauses: iterable(iterable(int))
        :type F_prime: iterable(int)    
        
    """
    # new set of validated literals
    new_F_prime = set(F_prime)
    
    # all literals (clauses with 1 element) validated in current hitting set
    validated_literals = {cnf_clauses[index][0] for index in new_F_prime if len(cnf_clauses[index]) == 1}
    
    # remaining clauses to check for validation
    remaining_clauses = {i for i in range(len(cnf_clauses))} - F_prime
    
    for c in remaining_clauses:
        clause = cnf_clauses[c]
        for literal in validated_literals:
            if literal in clause:
                new_F_prime.add(c)

    #validated_variables = flatten_set(validated_clauses)
    return new_F_prime

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
    
def extension2(cnf_clauses, F_prime, random_assignment = True):
    """
    
            Step 1 : Compute clauses with unique literals
            
            Step 2 :
                2.1 Compute validated clauses
                2.2 Compute remaining clauses
            
            Step 3:
                3.1 Compute all literal in validated clauses
                3.2 remove already validated literals from unique literal clauses
                3.3 remove negation of already validated literals from unique clauses
            
            Step 4:
                4.1 Seperate all remaining literals in validated clauses in 2 parts:
                    4.1.1 literals without negation of literal present
                    4.1.2. literals with negation present
            
            Step 5: Add all remaining clauses validated by assignement literals w/o negation
            
            Step 6:
                6.1a choose first literal from all literals with negation
                                or
                6.1b choose literal with best clause propagation
                6.2 Add all remaining clauses validated by assignement of literal                 
                
    """
    
    new_F_prime = set(F_prime)

    # Step 1 : clauses with unique literals
    # clauses with 1 literal 
    unique_literal_validated_clauses = {index for index in new_F_prime if len(cnf_clauses[index]) == 1}
    
    # literals validated in clauses with 1 literal
    validated_literals = {cnf_clauses[index][0] for index in unique_literal_validated_clauses}
    
    # non-unique clauses
    remaining_clauses = {i for i in range(len(cnf_clauses))} - unique_literal_validated_clauses
    
    # Step 2 : clauses with unique literals
    # all clauses satisfied by current single literal assignments of Fprime
    satisfied_clauses = set()
    
    # for every literal in validated literal check for any clause satisfied 
    for literal in validated_literals:
        for c in remaining_clauses:
            clause = cnf_clauses[c]
            if literal in clause:
                satisfied_clauses.add(c)
                new_F_prime.add(c)
    
    # remove unique literal clauses already validated
    satisfied_clauses -= unique_literal_validated_clauses

    remaining_clauses -= satisfied_clauses
    
    # remaining validated clauses in F prime
    assert all([True if -i not in validated_literals else False for i in validated_literals]), "literal conflict"
        
    # remaining literals to assign
    other_literals = flatten_set([cnf_clauses[index] for index in satisfied_clauses])

    # remove already validated literals
    other_literals -= validated_literals
    
    # remove negated already validated literals
    other_literals -= {-i for i in validated_literals}
    
    # filtered literals with negated literal also present 
    conflict_free_literals = {i for i in other_literals if -i not in other_literals}
    
    # remove all clauses validated by conflict free literals
    for literal in conflict_free_literals:
        clauses_to_remove = set()
        for c in remaining_clauses:
            clause = cnf_clauses[c]
            if literal in clause:
                clauses_to_remove.add(c)
                new_F_prime.add(c)
        remaining_clauses -= clauses_to_remove

    validated_literals |= conflict_free_literals

    other_literals -= conflict_free_literals
    # remaining conflictual literals to validate
    conflictual_literals = set(other_literals)    
   
    # check if only conflictual literals are present in conflictual literals
    assert all([True if -i in conflictual_literals else False for i in conflictual_literals]), "conflictual literals error"
    assert len(conflictual_literals) % 2 == 0, "check remaining literals are present in pairs"
    
    # for every literal, remove its negation and 
    while len(conflictual_literals) > 0:
        # randomly assigns truthness value
        if random_assignment:
            literal = conflictual_literals[0]
        else: 
            literal = find_best_literal(cnf_clauses, remaining_clauses, conflictual_literals)
            
        # SANITY CHECK : add to validated literals
        assert literal not in validated_literals, "literal already present"
        assert -literal not in validated_literals, "negation of literal already present, conflict !!!"
        validated_literals.add(literal)

        # remove literal and its negation
        conflictual_literals.remove(literal)
        conflictual_literals.remove(-literal)

        # remove validated clauses
        clauses_to_remove = set()
        
        for c in remaining_clauses:
            clause = cnf_clauses[c]
            if literal in clause:
                clauses_to_remove.add(c)
                new_F_prime.add(c)
        remaining_clauses -= clauses_to_remove
    # print("validated literals:", validated_literals)   
    return new_F_prime

def extension2silly(cnf_clauses, F_prime, random_assignment = True):
    """
    
            Repeatedly apply extension 2 until there is no more progress
            Propagate as much as possible
                
    """
    # TODO: 
    # - add while loop to propagate as long as possible as long as possible
    #   whenever len(other_literals ) > 0 
    # 
    # - exploit validatable clauses
    
    clauses_added = True
    new_F_prime = set(F_prime)

    while(clauses_added):
        ext2_F_prime = extension2(cnf_clauses, new_F_prime, random_assignment)
        ppprint({"new_F_prime" : new_F_prime,
                 "ext2_F_prime":ext2_F_prime,
                 "cnf_clauses": cnf_clauses
                  })
        clauses_added = ext2_F_prime > new_F_prime
        new_F_prime = set(ext2_F_prime)
        
    return new_F_prime

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

def extension3(cnf_clauses, F_prime, random_assignment = True):

    """
    
        Greedy Approach : 
            validated literals = {}

            1. Fprime = {unique literal clauses in F_prime} + {other validated clauses in F_prime} (sanity check)
                . seperate the unique literal clauses from other clauses in Fprime
                    => unique clause literals (a) => add to validated literals

            2. {clauses validated but not in F_prime} = {validated clauses using unique literal clauses in F_prime} - {F_prime}
                . get clauses that are validated by unique literals in Fprime but are not present in Fprime
                    => get the literals
                    => remove the unique literals 
                    => literals from validated clauses but not in F_prime and not a unique clause literal (b)

            3. {validated clauses in F_prime that have no literals from unique literal clauses}:
                . seperate into 
                    - conflict free literals : 
                        => 
                    - conflictual literals :
                        . this is a hitting set problem solve with optimal hitting set with special case of negated literals also present? 
                        . get a number of literals that covers the clauses 
                    => literals from F_prime that need to be  (c)

            4. {validated clauses in F_prime with literals from unique literal clauses} -  {unique literal clauses in F_prime}
                . {get the literals} - {validated literals up until now} - {negation of validated literals up until now}
            
    """

    new_F_prime = set(F_prime)
    
    all_clauses = {i for i in range(len(cnf_clauses))}
    
    # Step 1 : clauses with unique literals
    # clauses with 1 literal 
    unique_literal_validated_clauses = {index for index in new_F_prime if len(cnf_clauses[index]) == 1}
    unique_literals = getLiteralsSubsetClauses(cnf_clauses, unique_literal_validated_clauses) 

    # all clauses validated by current unique literal assignments
    all_validated_clauses = getClausesValidatedByLiterals(cnf_clauses, all_clauses, unique_literals)
    
    # all remaining validated clauses by F_prime assignement not in unique literal assignement
    remaining_validated_clauses = (new_F_prime | all_validated_clauses) - unique_literal_validated_clauses

    remaining_literals_validated_clauses = getLiteralsSubsetClauses(cnf_clauses, remaining_validated_clauses)

    remaining_literals_f_prime = getLiteralsSubsetClauses(cnf_clauses, F_prime)

    remaining_literals_validated_clauses -= unique_literals

    
    # remaining propagatable clauses
    remaining_clauses = all_clauses
    remaining_clauses -= new_F_prime
    remaining_clauses -= all_validated_clauses
    remaining_clauses -= unique_literal_validated_clauses
    
    
    # ppprint({
    #     "cnf_clauses": cnf_clauses, 
    #     "F_prime" : F_prime, 
    #     "unique_literals":unique_literals, 
    #     "all_validated_clauses": all_validated_clauses, 
    #     "remaining_literals_validated_clauses": remaining_literals_validated_clauses,
    #     "remaining_clauses":remaining_clauses
    # })
    
    return new_F_prime

def maxsat_fprime(cnf_clauses, F_prime):
    new_F_prime = set(F_prime)


    return new_F_prime

def extension4(cnf_clauses, F_prime):
    return F_prime
    
def grow(clauses, F_prime, extensions = None):
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
    if not extensions: 
        return complement(clauses, F_prime)

    exts = {
        0 : default_extension,
        1 : extension1,
        2 : extension2,
        3 : extension3,
        4 : extension4
    }
    
    assert all([True if ext in exts else False for ext in extensions]), "extension doest not exist"
    
    for ext in extensions:
        F_prime = exts[ext](clauses, F_prime)
        
    return complement(clauses, F_prime)


# # OMUS algorithm


def omus(cnf: CNF, extensions = [0]):    
    clauses = cnf.clauses
    weights = clauses_weights(clauses)
    H = [] # the complement of a max-sat call

    while(True):
        # compute optimal hitting set
        h = optimalHittingSet(H, weights)
        
        # set with all unique clauses from hitting set
        F_prime = {i for i, hi in enumerate(h) if hi > 0}
        ppprint({
            "h": h,
            # "C": C, 
            # "H": H
        })
        
        # check satisfiability of clauses
        if not checkSatClauses(clauses, F_prime):
            # ppprint({
            #     "OMUS": F_prime,
            #     "H": len(H)
            #     #"H": H
            # })
            return F_prime
        
        # add all clauses ny building complement
        C = grow(clauses, F_prime, extensions=extensions)

        if C in H:
            raise "MCS is already in H'"
        
        H.append(C)
        # printing        



# useless to call mus on cnf files, only on WCNF
#for cnf_name, cnf_dict in cnfs.items():
#    wcnf = CNF(from_file = cnf_dict['path']).weighted()
#    with MUSX(wcnf, verbosity=1) as musx:
#        print(musx.compute())
#wncf = WCNF(from_file = cnf1['path'])
