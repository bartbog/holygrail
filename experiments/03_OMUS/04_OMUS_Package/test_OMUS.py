#!/usr/bin/env python
# coding: utf-8

# standard libraries
from __future__ import print_function
import os
import re
import sys
from pathlib import Path
from enum import Enum
from datetime import datetime, date
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
ppprint = pprint.PrettyPrinter(indent=4).pprint
# # Pysat pre-processing
folderPaths={
    'easyInstances':'data/easy_instances/',
    'instance':'data/instance/',
    'aaaiInstances':'data/hard_instances/aaai_instances',
    'isingModel':'data/hard_instances/Generalized_Ising_model',
    'maxSat':'data/hard_instances/maxsat_staffscheduling_instances',
    'circuitDebugging':'data/hard_instances/ms_industrial/circuit-debugging-problems',
    'safarpour':'data/hard_instances/ms_industrial/sean-safarpour',
    'data/mse19-complete-unweighted/aes': 'data/mse19-complete-unweighted/aes',
    'data/mse19-complete-unweighted/aes-key-recovery': 'data/mse19-complete-unweighted/aes-key-recovery',
    'data/mse19-complete-unweighted/atcoss': 'data/mse19-complete-unweighted/atcoss',
    'data/mse19-complete-unweighted/bcp': 'data/mse19-complete-unweighted/bcp',
    'data/mse19-complete-unweighted/biorepair': 'data/mse19-complete-unweighted/biorepair',
    'data/mse19-complete-unweighted/causal-discovery': 'data/mse19-complete-unweighted/causal-discovery',
    'data/mse19-complete-unweighted/CircuitDebuggingProblems': 'data/mse19-complete-unweighted/CircuitDebuggingProblems',
    'data/mse19-complete-unweighted/CircuitTraceCompaction': 'data/mse19-complete-unweighted/CircuitTraceCompaction',
    'data/mse19-complete-unweighted/close_solutions': 'data/mse19-complete-unweighted/close_solutions',
    'data/mse19-complete-unweighted/ConsistentQueryAnswering': 'data/mse19-complete-unweighted/ConsistentQueryAnswering',
    'data/mse19-complete-unweighted/des': 'data/mse19-complete-unweighted/des',
    'data/mse19-complete-unweighted/drmx-atmostk': 'data/mse19-complete-unweighted/drmx-atmostk',
    'data/mse19-complete-unweighted/drmx-cryptogen': 'data/mse19-complete-unweighted/drmx-cryptogen',
    'data/mse19-complete-unweighted/extension-enforcement': 'data/mse19-complete-unweighted/extension-enforcement',
    'data/mse19-complete-unweighted/fault-diagnosis': 'data/mse19-complete-unweighted/fault-diagnosis',
    'data/mse19-complete-unweighted/frb': 'data/mse19-complete-unweighted/frb',
    'data/mse19-complete-unweighted/gen-hyper-tw': 'data/mse19-complete-unweighted/gen-hyper-tw',
    'data/mse19-complete-unweighted/HaplotypeAssembly': 'data/mse19-complete-unweighted/HaplotypeAssembly',
    'data/mse19-complete-unweighted/hs-timetabling': 'data/mse19-complete-unweighted/hs-timetabling',
    'data/mse19-complete-unweighted/jobshop': 'data/mse19-complete-unweighted/jobshop',
    'data/mse19-complete-unweighted/kbtree': 'data/mse19-complete-unweighted/kbtree',
    'data/mse19-complete-unweighted/logic-synthesis': 'data/mse19-complete-unweighted/logic-synthesis',
    'data/mse19-complete-unweighted/maxclique': 'data/mse19-complete-unweighted/maxclique',
    'data/mse19-complete-unweighted/maxcut': 'data/mse19-complete-unweighted/maxcut',
    'data/mse19-complete-unweighted/MaximumCommonSub-GraphExtraction': 'data/mse19-complete-unweighted/MaximumCommonSub-GraphExtraction',
    'data/mse19-complete-unweighted/maxone': 'data/mse19-complete-unweighted/maxone',
    'data/mse19-complete-unweighted/MaxSATQueriesinInterpretableClassifiers': 'data/mse19-complete-unweighted/MaxSATQueriesinInterpretableClassifiers',
    'data/mse19-complete-unweighted/mbd': 'data/mse19-complete-unweighted/mbd',
    'data/mse19-complete-unweighted/min-fill': 'data/mse19-complete-unweighted/min-fill',
    'data/mse19-complete-unweighted/mqc': 'data/mse19-complete-unweighted/mqc',
    'data/mse19-complete-unweighted/optic': 'data/mse19-complete-unweighted/optic',
    'data/mse19-complete-unweighted/packup': 'data/mse19-complete-unweighted/packup',
    'data/mse19-complete-unweighted/protein_ins': 'data/mse19-complete-unweighted/protein_ins',
    'data/mse19-complete-unweighted/pseudoBoolean': 'data/mse19-complete-unweighted/pseudoBoolean',
    'data/mse19-complete-unweighted/railway-transport': 'data/mse19-complete-unweighted/railway-transport',
    'data/mse19-complete-unweighted/ramsey': 'data/mse19-complete-unweighted/ramsey',
    'data/mse19-complete-unweighted/reversi': 'data/mse19-complete-unweighted/reversi',
    'data/mse19-complete-unweighted/rna-alignment': 'data/mse19-complete-unweighted/rna-alignment',
    'data/mse19-complete-unweighted/routing': 'data/mse19-complete-unweighted/routing',
    'data/mse19-complete-unweighted/scheduling': 'data/mse19-complete-unweighted/scheduling',
    'data/mse19-complete-unweighted/SeanSafarpour': 'data/mse19-complete-unweighted/SeanSafarpour',
    'data/mse19-complete-unweighted/set-covering': 'data/mse19-complete-unweighted/set-covering',
    'data/mse19-complete-unweighted/tpr': 'data/mse19-complete-unweighted/tpr',
    'data/mse19-complete-unweighted/treewidth-computation': 'data/mse19-complete-unweighted/treewidth-computation',
    'data/mse19-complete-unweighted/uaq': 'data/mse19-complete-unweighted/uaq',
    'data/mse19-complete-unweighted/vpa': 'data/mse19-complete-unweighted/vpa',
    'data/mse19-complete-unweighted/wqueens': 'data/mse19-complete-unweighted/wqueens',
    'data/mse19-complete-unweighted/xai-mindset2': 'data/mse19-complete-unweighted/xai-mindset2'

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
    else:
        sizeFilteredInstances = list(filter(lambda x: instanceDiff(x.stat().st_size) is difficulty, instances))
        return sizeFilteredInstances

def getDataPaths(cnfExtensions=['.cnf', '.wcnf'], difficulty= Difficulty.EASY):
    if difficulty not in Difficulty:
        print('Difficulty must be in ' +str(Difficulty.list()) + ' defaulting to easy.')
        difficulty = Difficulty.EASY

    return allInstances(difficulty, cnfExtensions)

def cnfInstances(difficulty=Difficulty.EASY):
    instances = [instance for instance in getDataPaths(cnfExtensions=['.cnf'], difficulty= difficulty)]
    return instances


def CNFisUnsat(instance, verbose=True):
    clauses = []
    for clause in CNF(from_file=instance).clauses:
        if clause not in clauses and len(clause) > 0:
            clauses.append(frozenset(clause))

    mapping, _ = mapping_clauses(clauses)
    mapped_clauses = map_clauses(clauses, mapping)

    with Solver() as s:
        added = s.append_formula(mapped_clauses, no_return=False)
        solved = s.solve()
    return not solved

def cnfUnsatInstances(difficulty=Difficulty.EASY):
    return [instance  for instance in cnfInstances(difficulty) if CNFisUnsat(instance)]

def wcnfInstances(difficulty=Difficulty.EASY):
    instances = [instance for instance in getDataPaths(cnfExtensions=['.wcnf'], difficulty= difficulty)]
    return instances

def WCNFisUnsat(instance, verbose=True):
    with Solver(name = SolverNames.minisat22[0]) as s:
        wcnf = WCNF(from_file=instance)
        added = s.append_formula(wcnf.clauses, no_return=False)
        solved = s.solve()
    return not solved

def wcnfUnsatInstances():
    return [instance  for instance in wcnfInstances()]

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

def mapping_clauses(clauses):

    union_clauses = frozenset.union(*clauses)
    sorted_vars = sorted(map(abs, union_clauses))

    mapping = {elem:i+1 for i, elem in enumerate(sorted_vars)}
    reversemapping = {i+1:elem for i, elem in enumerate(sorted_vars)}

    return mapping, reversemapping

def map_clauses(clauses, mapping):
    return [[mapping[abs(literal)]*sign(literal) for literal in clause] for clause in clauses]

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
    extension = 4

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
            # omus(cnf = CNF(from_clauses=cnf_clauses), extension =    extension )
            break


def benchmark_code_hard():
    # user_folder = '/home/emilio/OMUS/'
    # user_folder = '/home/crunchmonster/Documents/VUB/01_SharedProjects/03_holygrail/experiments/03_OMUS/04_OMUS_Package/'
    # folder = f'{user_folder}/results/{date.today().strftime("%Y_%m_%d")}/'
    folder = f'results/{date.today().strftime("%Y_%m_%d")}v4/'
    gurobiFolder = folder + "Gurobi/"
    gurobiColdFolder = folder + "GurobiCold/"
    orToolsFolder = folder + "OrTools/"

    # solverFolders = [gurobiFolder, gurobiColdFolder, orToolsFolder]
    solverFolders = [gurobiFolder, gurobiColdFolder, orToolsFolder]
    # extensions = [4, 3, 2]
    extensions = [3, 4]

    if not os.path.exists(folder):
        os.mkdir(folder)
    for f in solverFolders:
        if not os.path.exists(f):
            os.mkdir(f)
        for extension in extensions + [2]:
            ext_path = f + f"ext{extension}"
            if not os.path.exists(ext_path):
                os.mkdir(ext_path)

    # easy instances
    # easy_unsatInstances = cnfUnsatInstances(difficulty=Difficulty.EASY)
    # unsatInstances = easy_unsatInstances #+ medium_unsatInstances

    # # medium instances
    # medium_unsatInstances= cnfUnsatInstances(difficulty = Difficulty.MEDIUM)
    # unsatInstances += medium_unsatInstances

    # HARD instances
    hard_unsatInstances= cnfUnsatInstances(difficulty = Difficulty.HARD)
    unsatInstances = hard_unsatInstances

    cnf_files = sorted(unsatInstances, key=lambda item: item.stat().st_size)
    cnf_instances = []
    for cnf_file in cnf_files:
        clauses = []
        t_clauses = []
        for clause in CNF(from_file=cnf_file).clauses:
            if clause not in t_clauses and len(clause) > 0:
                clauses.append(frozenset(clause))
                t_clauses.append(clause)
        cnf_instances.append(CNF(from_clauses=clauses))
        # print(clauses)

    # for i, cnf in enumerate(cnf_instances):
    #     if "bf0432-007" in cnf_files[i].name:
    #         continue

    #     print(f"\nCNF File Example: {cnf_files[i]} - clauses = {len(cnf.clauses)}")

    #     # file name
    #     f_name = cnf_files[i].name.replace('.cnf', '')
    #     basefileName = f'ext{2}/{f_name}'

    #     # output folders
    #     orToolsOutputRandom = orToolsFolder +  basefileName + "_random"+ '.json'
    #     print("OrTools - extension", 2, "output=",orToolsOutputRandom)
    #     omusOrTools(cnf, extension = 2, outputfile=orToolsOutputRandom, random_literal=True, maxcoverage=False)

    #     orToolsOutputBestLiteral = orToolsFolder +  basefileName + "bestliteral"+ '.json'
    #     print("OrTools - extension", 2, "output=",orToolsOutputBestLiteral)
    #     omusOrTools(cnf, extension = 2, outputfile=orToolsOutputBestLiteral, random_literal=False, maxcoverage=False)

    #     orToolsOutputBestLiteralNeg = orToolsFolder +  basefileName + "bestliteral_neg"+ '.json'
    #     print("OrTools - extension", 2, "output=",orToolsOutputBestLiteralNeg)
    #     omusOrTools(cnf, extension = 2, outputfile=orToolsOutputBestLiteralNeg, random_literal=False, maxcoverage=True)

    for extension in extensions:
        for i, cnf in enumerate(cnf_instances):
            # if "bf0432-007" not in cnf_files[i].name:
            #     continue

            print(f"\nCNF File Example: {cnf_files[i]} - clauses = {len(cnf.clauses)}")

            # file name
            f_name = cnf_files[i].name.replace('.cnf', '')
            basefileName = f'ext{extension}/{f_name}'

            # output folders
            gurobiOutput = gurobiFolder +  basefileName + '.json'
            # gurobiColdOutput = gurobiColdFolder  + basefileName + '.json'
            # orToolsOutput = orToolsFolder + basefileName + '.json'

            # run benchmark
            print("Gurobi Warm - extension", extension, "output=",gurobiOutput)
            omusGurobi(cnf, extension = extension, outputfile=gurobiOutput)

            # # run benchmark
            # print("Gurobi Cold - extension", extension, "output=",gurobiColdOutput)
            # omusGurobiCold(cnf, extension = extension, outputfile=gurobiColdOutput)

            # # output folders
            # print("OrTools - extension", extension, "output=",orToolsOutput)
            # omusOrTools(cnf, extension = extension, outputfile=orToolsOutput)

def benchmark_code():
    # user_folder = '/home/emilio/OMUS/'
    # user_folder = '/home/crunchmonster/Documents/VUB/01_SharedProjects/03_holygrail/experiments/03_OMUS/04_OMUS_Package/'
    # folder = f'{user_folder}/results/{date.today().strftime("%Y_%m_%d")}/'
    folder = f'results/{date.today().strftime("%Y_%m_%d")}v4/'
    gurobiFolder = folder + "Gurobi/"
    gurobiColdFolder = folder + "GurobiCold/"
    orToolsFolder = folder + "OrTools/"

    # solverFolders = [gurobiFolder, gurobiColdFolder, orToolsFolder]
    solverFolders = [gurobiFolder, gurobiColdFolder, orToolsFolder]
    # extensions = [4, 3, 2]
    extensions = [2]

    if not os.path.exists(folder):
        os.mkdir(folder)
    for f in solverFolders:
        if not os.path.exists(f):
            os.mkdir(f)
        for extension in extensions + [2]:
            ext_path = f + f"ext{extension}"
            if not os.path.exists(ext_path):
                os.mkdir(ext_path)

    # easy instances
    # easy_unsatInstances = cnfUnsatInstances(difficulty=Difficulty.EASY)
    # unsatInstances = easy_unsatInstances #+ medium_unsatInstances

    # medium instances
    medium_unsatInstances= cnfUnsatInstances(difficulty = Difficulty.MEDIUM)
    unsatInstances = medium_unsatInstances

    # # HARD instances
    # # hard_unsatInstances= cnfUnsatInstances(difficulty = Difficulty.HARD)
    # # unsatInstances += hard_unsatInstances

    cnf_files = sorted(unsatInstances, key=lambda item: item.stat().st_size)
    cnf_instances = []
    for cnf_file in cnf_files:
        clauses = []
        t_clauses = []
        for clause in CNF(from_file=cnf_file).clauses:
            if clause not in t_clauses and len(clause) > 0:
                clauses.append(frozenset(clause))
                t_clauses.append(clause)
        cnf_instances.append(CNF(from_clauses=clauses))
        # print(clauses)

    # for i, cnf in enumerate(cnf_instances):
    #     if "bf0432-007" in cnf_files[i].name:
    #         continue

    #     print(f"\nCNF File Example: {cnf_files[i]} - clauses = {len(cnf.clauses)}")

    #     # file name
    #     f_name = cnf_files[i].name.replace('.cnf', '')
    #     basefileName = f'ext{2}/{f_name}'

    #     # output folders
    #     orToolsOutputRandom = orToolsFolder +  basefileName + "_random"+ '.json'
    #     print("OrTools - extension", 2, "output=",orToolsOutputRandom)
    #     omusOrTools(cnf, extension = 2, outputfile=orToolsOutputRandom, random_literal=True, maxcoverage=False)

    #     orToolsOutputBestLiteral = orToolsFolder +  basefileName + "bestliteral"+ '.json'
    #     print("OrTools - extension", 2, "output=",orToolsOutputBestLiteral)
    #     omusOrTools(cnf, extension = 2, outputfile=orToolsOutputBestLiteral, random_literal=False, maxcoverage=False)

    #     orToolsOutputBestLiteralNeg = orToolsFolder +  basefileName + "bestliteral_neg"+ '.json'
    #     print("OrTools - extension", 2, "output=",orToolsOutputBestLiteralNeg)
    #     omusOrTools(cnf, extension = 2, outputfile=orToolsOutputBestLiteralNeg, random_literal=False, maxcoverage=True)

    for extension in extensions:
        for i, cnf in enumerate(cnf_instances):
            if "zebra_v155_c1135" not in cnf_files[i].name:
                continue

            print(f"\nCNF File Example: {cnf_files[i]} - clauses = {len(cnf.clauses)}")

            # file name
            f_name = cnf_files[i].name.replace('.cnf', '')
            basefileName = f'ext{extension}/{f_name}'

            # output folders
            gurobiOutput = gurobiFolder +  basefileName + '.json'
            # gurobiColdOutput = gurobiColdFolder  + basefileName + '.json'
            # orToolsOutput = orToolsFolder + basefileName + '.json'

            # run benchmark
            print("Gurobi Warm - extension", extension, "output=",gurobiOutput)
            if extension == 2:
                gurobiOutput = gurobiFolder +  basefileName + "bestliteral_neg" + '.json'
                omusGurobi(cnf, extension = 2, outputfile=gurobiOutput, random_literal=False, maxcoverage=True)
            else:
                omusGurobi(cnf, extension = extension, outputfile=gurobiOutput)

            # # run benchmark
            # print("Gurobi Cold - extension", extension, "output=",gurobiColdOutput)
            # omusGurobiCold(cnf, extension = extension, outputfile=gurobiColdOutput)

            # # output folders
            # print("OrTools - extension", extension, "output=",orToolsOutput)
            # omusOrTools(cnf, extension = extension, outputfile=orToolsOutput)


def medium_instance():
    # f_path = "data/easy_instances/bf0432-007.cnf"
    f_path = "data/easy_instances/zebra_v155_c1135.cnf"
    clauses = []
    t_clauses = []
    for clause in CNF(from_file=f_path).clauses:
        if clause not in t_clauses and len(clause) > 0:
            clauses.append(frozenset(clause))
            t_clauses.append(clause)
    return  CNF(from_clauses=clauses)

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
def test_findBestLiteral():
    clauses = [frozenset(clause) for clause in bacchus_cnf().clauses]
    literals = frozenset.union(*clauses)
    ppprint(bacchus_cnf().clauses)
    print(literals)
    best_literal = findTopBestLiterals(clauses, set(), literals, 10)
    print(best_literal)

def benchmark_parameter_omus():
    # user_folder = '/home/emilio/OMUS/'
    # user_folder = '/home/crunchmonster/Documents/VUB/01_SharedProjects/03_holygrail/experiments/03_OMUS/04_OMUS_Package/'
    # folder = f'{user_folder}/results/{date.today().strftime("%Y_%m_%d")}/'
    folder = f'results/{date.today().strftime("%Y_%m_%d")}/'
    gurobiFolder = folder + "Gurobi/"

    solverFolders = [gurobiFolder]
    extensions = [3]

    # easy instances
    easy_unsatInstances = cnfUnsatInstances(difficulty=Difficulty.EASY)
    unsatInstances = easy_unsatInstances #+ medium_unsatInstances

    # medium instances
    medium_unsatInstances= cnfUnsatInstances(difficulty = Difficulty.MEDIUM)
    unsatInstances += medium_unsatInstances

    # # HARD instances
    # # hard_unsatInstances= cnfUnsatInstances(difficulty = Difficulty.HARD)
    # # unsatInstances += hard_unsatInstances

    cnf_files = sorted(unsatInstances, key=lambda item: item.stat().st_size)
    cnf_instances = []
    for cnf_file in cnf_files:
        clauses = []
        t_clauses = []
        for clause in CNF(from_file=cnf_file).clauses:
            if clause not in t_clauses and len(clause) > 0:
                clauses.append(frozenset(clause))
                t_clauses.append(clause)
        cnf_instances.append(CNF(from_clauses=clauses))

    if not os.path.exists(folder):
        os.mkdir(folder)

    for f in solverFolders:
        if not os.path.exists(f):
            os.mkdir(f)
        for extension in extensions:
            ext_path = f + f"ext{extension}"
            if not os.path.exists(ext_path):
                os.mkdir(ext_path)
            for fpath in cnf_files:
                f_name = fpath.name.replace('.cnf', '')
                if "bf0432-007" in f_name:
                    continue
                f_ext_path = f + f"ext{extension}/{f_name}/"
                if not os.path.exists(f_ext_path):
                    os.mkdir(f_ext_path)

    extension = 3
    for i, cnf in enumerate(cnf_instances):
        counter = 0
        if "bf0432-007" in cnf_files[i].name:
            continue
        print(f"\nCNF File Example: {cnf_files[i]} - clauses = {len(cnf.clauses)}")

        # file name
        f_name = cnf_files[i].name.replace('.cnf', '')
        basefileName = f'ext{extension}/{f_name}/'

        # run benchmark
        for clause_counting in ClauseCounting:
                for clause_sorting in ClauseSorting:
                    for unit_prop in UnitLiteral:
                        for best_literal in BestCounterLiteral:
                            for sat_model in SatModel:
                                # output folders
                                gurobiOutput = gurobiFolder +  basefileName+f"{counter}.json"
                                print("OMUS - extension {extension}", "output=",gurobiOutput)
                                parameters = {
                                    'count_clauses' : clause_counting,
                                    'sorting':clause_sorting,
                                    'best_unit_literal': unit_prop,
                                    'best_counter_literal': best_literal,
                                    'sat_model' :sat_model,
                                    'extension': 3,
                                    'output': gurobiOutput
                                }
                                # ppprint(parameters)

                                omus(cnf, parameters)
                                counter+=1

def test_extension():

    # Execution parameters
    parameters = {
        # clause counting
        'count_clauses' : ClauseCounting.WEIGHTED_UNASSIGNED,
        # 'count_clauses' : ClauseCounting.WEIGHTS,
        # 'count_clauses' : ClauseCounting.VALIDATED,
        # clause sorting
        # 'sorting':ClauseSorting.IGNORE,
        # 'sorting':ClauseSorting.WEIGHTS,
        'sorting':ClauseSorting.UNASSIGNED,
        # 'sorting':ClauseSorting.WEIGHTED_UNASSIGNED,
        # Unit Literal propagation
        'best_unit_literal': UnitLiteral.IMMEDIATE,
        # 'best_unit_literal': UnitLiteral.INGORE,
        # 'best_unit_literal': UnitLiteral.RANDOM,
        # 'best_unit_literal': UnitLiteral.PURE,
        # 'best_unit_literal': UnitLiteral.POLARITY,
        'best_counter_literal': BestLiteral.COUNT_POLARITY,
        # 'best_counter_literal': BestLiteral.COUNT_PURE_ONLY,
        'sat_model' :SatModel.BEST_WEIGHTED_UNASSIGNED_CLAUSE_COVERAGE,
        # 'top_k_models': 10,
        # 'bestModel' :SatModel.RANDOM,
        'extension': 3,
        'output': 'log.json'
    }
    # f_path = "data/easy_instances/bf0432-007.cnf"
    # f_path = "data/easy_instances/aim-100-1_6-no-1.cnf"
    f_path = "data/easy_instances/zebra_v155_c1135.cnf"
    clauses = []
    t_clauses = []
    for clause in CNF(from_file=f_path).clauses:
        if clause not in t_clauses and len(clause) > 0:
            clauses.append(frozenset(clause))
            t_clauses.append(clause)
    cnf = CNF(from_clauses=clauses)
    print(omus(bacchus_cnf(), parameters=parameters))
    print(omus(omus_cnf(), parameters=parameters))
    print(omus(cnf, parameters=parameters))

def main():
    test_extension()
    # d = [('a', 1), ('b', 2), ('c', 1.5)]
    # d.sort()
    # test_extension()
    # for c in ClauseCounting:
    #     if c == ClauseCounting.WEIGHTED_UNASSIGNED:
    #         print(c)
        # print(c)
    # test_getAllModels()
    # test_instance()
    # omusGurobiCold(smus_CNF(),extension=3 )
    # omusOrTools("")
    # benchmark_code()
    # benchmark_code_hard()
    # test_findBestLiteral()
    # print(Difficulty.EASY < Difficulty.MEDIUM)

if __name__ == "__main__":
    main()
