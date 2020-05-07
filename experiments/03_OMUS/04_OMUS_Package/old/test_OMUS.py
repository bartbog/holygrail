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
from pysat.formula import CNF, WCNF, IDPool
from pysat.examples.fm import FM
from pysat.examples.musx import MUSX
from pysat.examples.rc2 import RC2

# or-tools library
from ortools.linear_solver import pywraplp

from OMUS import *
from OMUS_utils import *
# numpy
#import numpy as np

# configs
import pprint

sign = lambda x: (1, -1)[x < 0]

# # Pysat pre-processing
folderPaths={
    'easyInstances':'data/easy_instances/',
    'instance':'data/instance/',
    'aaaiInstances':'data/hard_instances/aaai_instances',
    'isingModel':'data/hard_instances/Generalized_Ising_model',
    'maxSat':'data/hard_instances/maxsat_staffscheduling_instances',
    'circuitDebugging':'data/hard_instances/ms_industrial/circuit-debugging-problems',
    'safarpour':'data/hard_instances/ms_industrial/sean-safarpour'
}

class Difficulty(Enum):
    EASY = 1
    MEDIUM = 2
    HARD = 3
    ALL = 0

    @staticmethod
    def list():
        return list(map(lambda c: c.value, Difficulty))



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
        raise('Difficulty must be in ' +str(Difficulty.list()) + ' defaulting to easy.')
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
    return not solved

def WCNFisUnsat(instance, verbose=True):
    with Solver(name = SolverNames.minisat22[0]) as s:
        wcnf = WCNF(from_file=instance)
        added = s.append_formula(wcnf.clauses, no_return=False)
        solved = s.solve()
    return not solved

def wcnfUnsatInstances():
    return [instance  for instance in wcnfInstances()]

def cnfUnsatInstances():
    return [instance  for instance in cnfInstances(Difficulty.MEDIUM) if CNFisUnsat(instance)]

def smus_CNF():
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

def test_extension1():
    input_cnf_clauses = [[1],[2, 3, 5],[3, 6, 7],[-4, -1],[-4],[-4, -8]]

    input_F_prime = {0, 4}
    output_F_prime = {0, 3, 4, 5}

    ext1_F_prime = extension1(input_cnf_clauses, input_F_prime)

    assert sorted(output_F_prime) == sorted(ext1_F_prime), "Should be equal"

def test_extension2():
    input_cnf_clauses = [[1],[2, 3, 5],[3, 6, 7, -8],[-4, -1],[-4],
        [-4, -8]
    ]
    input_F_prime = {0, 4}
    expected_output = {0, 2, 3, 4, 5}

    ext1_F_prime = extension2(input_cnf_clauses, input_F_prime)

    assert sorted(expected_output) == sorted(ext1_F_prime), f"{ext1_F_prime} == {expected_output}"

def test_extension3():

    input_cnf_clauses = [[1],[2, 3, 5],[3, 6, 7, -8],[3, 6],[5, 9],[2, -7],[-4, -1],[-4],[-4, -8]]
    input_F_prime = {0, 1, 7}

    expected_output = {0, 2, 3, 4, 5}

    ext1_F_prime = extension3(input_cnf_clauses, input_F_prime)

def test_getLiteralsSubsetClauses():
    assert True

def test_getClausesValidatedByLiterals():
    assert True

def test_cnf_file():
    # CNf Files
    print("\nCNF File Example")
    cnfs = sorted(cnfUnsatInstances(), key=lambda item: item.stat().st_size)
    c = cnfs[1]
    cnf = CNF(from_file=c)
    print(cnf.clauses)
    # omus(cnf, [2] )
    # omus(cnf, [1] )
    omus(cnf, [1] )

    #for c in cnfs:
    #    cnf = CNF(from_file=c)
    #    o = omus(cnf)
    #    print(c, c.stat().st_size)
    #    print(cnf.clauses)

def run_tests():
    # test_flatten_set()
    # test_extension1()
    # test_extension2()
    # test_extension3()
    extensions = [2]
    smus_cnf = smus_CNF()
    omus(smus_cnf, extensions )
    # test_cnf_file()
    # print("Everything passed")

def mapping_clauses(clauses):

    union_clauses = frozenset.union(*clauses)
    sorted_vars = sorted(map(abs, union_clauses))

    mapping = {elem:i+1 for i, elem in enumerate(sorted_vars)}
    reversemapping = {i+1:elem for i, elem in enumerate(sorted_vars)}

    return mapping, reversemapping

def map_clauses(clauses, mapping):

    newclauses = [[mapping[abs(literal)]*sign(literal) for literal in clause] for clause in clauses]

    return newclauses


def list_clause_frozen(clauses):

    return [frozenset(clause) for clause in clauses]


def test_checkSatClauses():

    smus_cnf = smus_CNF()
    clauses = list_clause_frozen(smus_cnf.clauses)
    F_prime = [2]

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

def cnf_solvable(cnf_file):

    return solved

def testMaxSat(wcnf_file, max_count = 5):
    wcnf = WCNF(from_file=wcnf_file)

    with RC2(wcnf) as rc2:
        cnt = 1
        for m in rc2.enumerate():
            print('model {0} has cost {1}'.format(m, rc2.cost))
            cnt += 1
            if cnt > max_count:
                break

def unit(x):
    return 1

def myCheckSatClauses(clauses):
    # cnf_clauses = [clauses[i] for i in F_prime]

    mapping, reverse_mapping = mapping_clauses(clauses)
    mapped_clauses = map_clauses(clauses, mapping)

    with Solver() as s:
        added = s.append_formula(mapped_clauses, no_return=False)
        solved = s.solve()
        model = s.get_model()

    if solved:
        mapped_model = frozenset(map(lambda literal: reverse_mapping[abs(literal)]*sign(literal) , model))
        return mapped_model, solved
    else:
        return None, solved

def test_omus(extension):
    smus_cnf = smus_CNF()
    assert sorted(omus(smus_cnf, extension )) == sorted([0, 1, 2]), "SMUS error"

def test_cnf_instances():
    extension = 3

    cnf_files = sorted(cnfUnsatInstances(), key=lambda item: item.stat().st_size)
    cnf_instances = list(map(lambda cnf_file: CNF(from_file=cnf_file), cnf_files))
    cnt = 0
    for i, cnf in enumerate(cnf_instances):
        # print("helllooooo")
        cnf_clauses = []
        [cnf_clauses.append(frozenset(clause)) for clause in cnf.clauses if clause not in cnf_clauses and len(clause) > 0 ]

        model, solved = myCheckSatClauses(cnf_clauses)

        if not solved:
            print("Not solvable", solved )
            print(f"\nCNF File Example: {cnf_files[i].name} ({CNFisUnsat(cnf_files[i])}) - clauses = {len(cnf_clauses)}")
            # ppprint(cnf_clauses)
            omus(cnf = CNF(from_clauses=cnf_clauses), extension =    extension )
            break

def test_unsat_core():
    print(smus_CNF().clauses)
    from pysat.solvers import Minisat22
    with Minisat22() as m:
        for clause in smus_CNF().clauses:
            m.add_clause(clause)

        print(m.solve(assumptions=[-1,-3]))
        print(m.get_core())  # literals 2 and 3 are not in the core
def test_maxsat():
    clauses = smus_CNF().clauses
    print(clauses)
    F_prime = [0]

    with RC2(WCNF()) as rc2:
        for i, clause in enumerate(clauses):
            if i in F_prime:
                rc2.add_clause(clause)
            else:
                rc2.add_clause(clause, weight=1)
        model = rc2.compute()
        print(model, rc2.cost)
def main():
    test_cnf_instances()

if __name__ == "__main__":
    main()
