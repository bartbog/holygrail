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

from OMUS import *
# numpy
#import numpy as np

# configs
import pprint



# # Pysat pre-processing
folderPaths={
    'easyInstances':'/home/crunchmonster/Documents/VUB/02_Research/02_Notes/02_OMUS/B_data/easy_instances/',
    'instance':'/home/crunchmonster/Documents/VUB/02_Research/02_Notes/02_OMUS/B_data/instance/',
    'aaaiInstances':'/home/crunchmonster/Documents/VUB/02_Research/02_Notes/02_OMUS/B_data/hard_instances/aaai_instances',
    'isingModel':'/home/crunchmonster/Documents/VUB/02_Research/02_Notes/02_OMUS/B_data/hard_instances/Generalized_Ising_model',
    'maxSat':'/home/crunchmonster/Documents/VUB/02_Research/02_Notes/02_OMUS/B_data/hard_instances/maxsat_staffscheduling_instances',
    'circuitDebugging':'/home/crunchmonster/Documents/VUB/02_Research/02_Notes/02_OMUS/B_data/hard_instances/ms_industrial/circuit-debugging-problems',
    'safarpour':'/home/crunchmonster/Documents/VUB/02_Research/02_Notes/02_OMUS/B_data/hard_instances/ms_industrial/sean-safarpour'
}

class Difficulty(Enum):
    EASY = 1
    MEDIUM = 2
    HARD = 3
    ALL = 0

def instanceDiff(fileSize):
    
    mb = 10* 1024 ** 1
    mediumUb = 10 * mb
    if fileSize < mb:
        return Difficulty.EASY
    elif fileSize < mediumUb:
        return Difficulty.MEDIUM
    else:
        return Difficulty.HARD

    
def allInstances(difficulty, cnfExtensions=['.cnf', '.wcnf']):
    instances = []
    for folder in folderPaths:
        instanceFolder = Path(folderPaths[folder])
        instances += [x for x in instanceFolder.iterdir() if x.is_file() and x.suffix in cnfExtensions]
    
    if difficulty is Difficulty.ALL:
        return instances

    sizeFilteredInstances = list(filter(lambda x: instanceDiff(x.stat().st_size) is difficulty, instances))

    return sizeFilteredInstances
    
def getDataPaths(cnfExtensions=['.cnf', '.wcnf'], difficulty= Difficulty.EASY):
    
    if difficulty not in Difficulty:
        ppprint('Difficulty must be in ' +str(difficulties) + ' defaulting to easy.')
        difficulty = Difficulty.EASY
    
    instances = allInstances(difficulty, cnfExtensions)

    return instances

def cnfInstances(difficulty=Difficulty.EASY):
    instances = [instance for instance in getDataPaths(cnfExtensions=['.cnf'], difficulty= difficulty)] 
    return instances

def wcnfInstances(difficulty=Difficulty.EASY):
    instances = [instance for instance in getDataPaths(cnfExtensions=['.wcnf'], difficulty= difficulty)] 
    return instances

def CNFisUnsat(instance, verbose=True):
    with Solver() as s:
        cnf = CNF(from_file=instance)
        added = s.append_formula(cnf.clauses, no_return=False)
        solved = s.solve()
    return solved

def WCNFisUnsat(instance, verbose=True):
    with Solver(name = SolverNames.minisat22[0]) as s:
        wcnf = WCNF(from_file=instance)
        added = s.append_formula(wcnf.clauses, no_return=False)
        solved = s.solve()
    return solved

def cnfUnsatInstances():
    return [instance  for instance in cnfInstances() if CNFisUnsat(instance)]


def smus_CNF():
    l = 1
    m = 2
    n = 3
    p = 4
    s = 5
    t = 6
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


def test_flatten_set():
    print("Testing flatten set")
    assert sorted(flatten_set([[1, 2, 3],[4, 1 ,3]])) == [1,2,3, 4], "Should be 6"

def test_extension1():
    input_cnf_clauses = [
        [1],
        [2, 3, 5],
        [3, 6, 7],
        [-4, -1],
        [-4],
        [-4, -8]
    ]
    input_F_prime = {0, 4}
    
    output_F_prime = {0, 3, 4, 5}
    
    ext1_F_prime = extension1(input_cnf_clauses, input_F_prime)
    
    assert sorted(output_F_prime) == sorted(ext1_F_prime), "Should be equal"

def test_extension2():
    input_cnf_clauses = [
        [1],
        [2, 3, 5],
        [3, 6, 7, -8],
        [-4, -1],
        [-4],
        [-4, -8]
    ]
    input_F_prime = {0, 4}
    
    expected_output = {0, 2, 3, 4, 5}
    
    ext1_F_prime = extension2(input_cnf_clauses, input_F_prime)
    
    assert sorted(expected_output) == sorted(ext1_F_prime), f"{ext1_F_prime} == {expected_output}"
    


def test_extension3():

    input_cnf_clauses = [
        [1],
        [2, 3, 5],
        [3, 6, 7, -8],
        [3, 6],
        [5, 9],
        [2, -7],
        [-4, -1],
        [-4],
        [-4, -8]
    ]
    input_F_prime = {0, 1, 7}

    expected_output = {0, 2, 3, 4, 5}

    ext1_F_prime = extension3(input_cnf_clauses, input_F_prime)

def test_getLiteralsSubsetClauses():
    assert True

def test_getClausesValidatedByLiterals():
    assert True

def test_omus():
    # Toy example
    print("\nSMUS Example")
    extesions = []
    smus_cnf = smus_CNF()
    omus(smus_cnf, [0] )
    omus(smus_cnf, [1] )
    omus(smus_cnf, [2] )

def test_cnf_file():
    # CNf Files 
    print("\nCNF File Example")
    cnfs = sorted(cnfUnsatInstances(), key=lambda item: item.stat().st_size)
    c = cnfs[1]
    cnf = CNF(from_file=c)
    print(cnf.clauses)
    omus(cnf, [2] )
    omus(cnf, [1] )
    omus(cnf, [0] )

    #for c in cnfs:
    #    cnf = CNF(from_file=c)
    #    o = omus(cnf)
    #    print(c, c.stat().st_size)
    #    print(cnf.clauses)

def run_tests():
    test_flatten_set()
    test_extension1()
    test_extension2()
    test_extension3()
    test_omus()
    # test_cnf_file()
    # print("Everything passed")

def main():
    run_tests()

if __name__ == "__main__":
    main()