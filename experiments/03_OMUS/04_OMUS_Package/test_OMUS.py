#!/usr/bin/env python
# coding: utf-8

# standard libraries
from __future__ import print_function
import os
import re
import sys
from pathlib import Path
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

ppprint = pprint.PrettyPrinter(indent=4).pprint

# CNF Paper Instances
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

def instanceDiff(fileSize):

    kb =  1024 ** 1
    easyUb = 100*kb
    mediumUb = 1000 * kb

    if fileSize < easyUb:
        return Difficulty.EASY
    elif fileSize < mediumUb:
        return Difficulty.MEDIUM
    else:
        return Difficulty.HARD

def CNFisUnsat(instance):
    cnf = CNF(from_file=instance)
    with Solver() as s:
        added = s.append_formula(cnf, no_return=False)
        solved = s.solve()
        model = s.get_model()
    return not solved

def WCNFisUnsat(instance):
    cnf = WCNF(from_file=instance).unweighted()
    with Solver() as s:
        added = s.append_formula(cnf, no_return=False)
        solved = s.solve()
        model = s.get_model()
    return not solved

def cnfInstances(difficulty= Difficulty.EASY):
    cnf_unsat_files = []
    folder_path = 'data/cnf-instances/'
    for r, d, f in os.walk(folder_path):
        for file in f:
            f_path = os.path.join(r, file)
            f_size = os.stat(f_path).st_size
            f_difficulty = instanceDiff(f_size )
            if difficulty == Difficulty.ALL and '.cnf' in file and CNFisUnsat(f_path) :
                cnf_unsat_files.append(f_path)
            elif instanceDiff(f_size) != difficulty:
                continue
            elif '.cnf' in file and CNFisUnsat(f_path):
                cnf_unsat_files.append(f_path)
    return cnf_unsat_files

def wcnfInstances(difficulty= Difficulty.EASY):
    wcnf_unsat_files = []
    folder_path = 'data/wcnf-instances/'
    for r, d, f in os.walk(folder_path):
        for file in f:
            f_path = os.path.join(r, file)
            f_size = os.stat(f_path).st_size
            f_difficulty = instanceDiff(f_size )
            if difficulty == Difficulty.ALL and '.wcnf' in file and CNFisUnsat(f_path):
                wcnf_unsat_files.append(f_path)
            elif f_difficulty != difficulty:
                continue
            elif '.wcnf' in file and WCNFisUnsat(f_path):
                wcnf_unsat_files.append(f_path)
    wcnf_unsat_files.sort(key=lambda file_path: os.path.getsize(file_path))
    # for f in wcnf_unsat_files:
    #     print("File=", f, "size=", os.path.getsize(f))
    return wcnf_unsat_files

def benchmark_code():

    folder = f'results/{date.today().strftime("%Y_%m_%d")}v4/'
    gurobiFolder = folder + "Gurobi/"
    gurobiColdFolder = folder + "GurobiCold/"
    orToolsFolder = folder + "OrTools/"

    solverFolders = [gurobiFolder] # [gurobiFolder, gurobiColdFolder, orToolsFolder]
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

def benchmark_parameter_omus():
    folder = f'results/{date.today().strftime("%Y_%m_%d")}/'
    gurobiFolder = folder + "Gurobi/"

    solverFolders = [gurobiFolder]
    extensions = [3]

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

    easy_cnf_instances = cnfInstances(difficulty= Difficulty.EASY)
    medium_cnf_instances = cnfInstances(difficulty= Difficulty.MEDIUM)
    cnf_instances = easy_cnf_instances + medium_cnf_instances

    for instance in cnf_instances:
        counter = 0
        # file name
        cnf = CNF(from_file=instance)
        f_name = instance.replace('.cnf', '')
        basefileName = f'ext{extension}/{f_name}/'

        # run benchmark
        for clause_counting in ClauseCounting:
                for clause_sorting in ClauseSorting:
                    for unit_prop in UnitLiteral:
                        for best_literal in BestLiteral:
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



def benchmark_cnf_files():
    folder = f'results/{date.today().strftime("%Y_%m_%d")}/'
    gurobiFolder = folder + "Gurobi/"

    solverFolders = [gurobiFolder]
    # extensions = [3, 5, 6]

    if not os.path.exists(folder):
        os.mkdir(folder)

    for f in solverFolders:
        if not os.path.exists(f):
            os.mkdir(f)

    # num_instances = 7
    easy_cnf_instances = cnfInstances(difficulty= Difficulty.EASY) + cnfInstances(difficulty= Difficulty.MEDIUM)#[:num_instances] + 
    folder_path = f"{gurobiFolder}"
    if not os.path.exists(folder_path):
        raise f"path = {folder_path} does not exist"
    for instance in easy_cnf_instances:
        if 'bf0432-007' not in instance :
            continue
        # instance variables
        instance_name = instance.replace('data/cnf-instances/','')
        instance_name = instance_name.replace('.cnf','')

        # # convert instance file to WCNF
        cnf = CNF(from_file=instance)
        # clauses = cnf.clauses
        # print(f"nv={cnf.nv} #clauses={len(clauses)}")

        # ## execution extension 6 (tias code)
        # parameters = {
        #     'extension': 'greedy_no_param',
        #     'output':f"{folder_path}{instance_name}_greedy_no_param.json",
        #     'cutoff_main': 120 * 60,
        # }

        # print(f"Greedy no parameters: {folder_path}{instance_name}_greedy_no_param.json")
        # omus(cnf, parameters=parameters)

        ## execution extension 3 with different parameters combinations
        # variables
        cnt = 1
        # for sorting in ClauseSorting:
        for clause_counting in [ClauseCounting.WEIGHTED_UNASSIGNED, ClauseCounting.VALIDATED]:
            for unit_literal in [UnitLiteral.IMMEDIATE]:
                for best_literal in [BestLiteral.COUNT_POLARITY, BestLiteral.COUNT_PURE_ONLY]:
                    outputfile = f"{folder_path}{instance_name}_greedy_param_hard_{cnt}.json"
                    print(f"Greedy with parameters: {outputfile}")
                    print("---- ClauseCounting=", clause_counting, "UnitLiteral=", unit_literal, "BestLiteral=", best_literal)
                    parameters = {
                        # clause counting
                        'count_clauses' : clause_counting,
                        'best_unit_literal': unit_literal,
                        'best_counter_literal': best_literal,
                        'sorting': ClauseSorting.IGNORE,
                        'extension': 'greedy_param',
                        'cutoff_main': 120 * 60,
                        'output': outputfile,
                    }
                    omus(cnf, parameters=parameters)
                    cnt += 1

    # for instance in easy_cnf_instances:

    #     # instance variables
    #     instance_name = instance.replace('data/cnf-instances/','')
    #     instance_name = instance_name.replace('.cnf','')

    #     # convert instance file to WCNF
    #     cnf = CNF(from_file=instance)
    #     clauses = cnf.clauses
    #     print(f"nv={cnf.nv} #clauses={len(clauses)}")
    #     ## Maxprop with or with unit prop
    #     cnt = 1
    #     for unit_literal in UnitLiteral:
    #         for best_literal in BestLiteral:
    #             print("UnitLiteral=", unit_literal, "BestLiteral=", best_literal)
    #             parameters = {
    #                 'extension': 'maxprop',
    #                 'output': f"{folder_path}{instance_name}_maxprop_{cnt}.json",
    #                 'cutoff_main': 15 * 60,
    #                 'best_counter_literal': best_literal,
    #                 'best_unit_literal': unit_literal
    #             }
    #             print(f"{folder_path}{instance_name}_maxprop_{cnt}.json")
    #             omus(cnf, parameters=parameters)
    #             cnt +=1

    # for instance in easy_cnf_instances:
    #     # instance variables
    #     instance_name = instance.replace('data/cnf-instances/','')
    #     instance_name = instance_name.replace('.cnf','')

    #     # convert instance file to WCNF
    #     cnf = CNF(from_file=instance)
    #     clauses = cnf.clauses
    #     print(f"nv={cnf.nv} #clauses={len(clauses)}")
    #     ## Local Search : SATLike
    #     ## parameters found in code
    #     # if mean(weights[i] for i in range(len(wcnf.soft))) > 10000:
    #     #     h_inc=300
    #     #     softclause_weight_threshold=500
    #     # else:
    #     h_inc=3
    #     softclause_weight_threshold=0

    #     parameters = {
    #         'extension': 'satlike',
    #         'output': f"{folder_path}{instance_name}_satlike.json",
    #         'cutoff' : 15,
    #         'h_inc' : 3,
    #         'max_restart':5,
    #         's_inc' : softclause_weight_threshold,
    #         'pb_restarts': 0.001,
    #         # 'pb_restarts': 0,
    #         'cutoff_main': 30 * 60,
    #         'sp': 0.01 # smooth probability found in code.... not realy the one in the paper
    #     }
    #     print(f"SATLike: {folder_path}{instance_name}_satlike.json")
    #     omus(cnf, parameters=parameters)


def benchmark_wcnf_files():
    folder = f'results/{date.today().strftime("%Y_%m_%d")}/'
    gurobiFolder = folder + "Gurobi/"

    solverFolders = [gurobiFolder]
    # extensions = [3, 5, 6]

    if not os.path.exists(folder):
        os.mkdir(folder)

    for f in solverFolders:
        if not os.path.exists(f):
            os.mkdir(f)

    num_instances = 7
    easy_cnf_instances = wcnfInstances(difficulty= Difficulty.EASY)[:num_instances]
    folder_path = f"{gurobiFolder}"
    if not os.path.exists(folder_path):
        raise f"path = {folder_path} does not exist"
    # for instance in easy_cnf_instances:
    #     # instance variables
    #     instance_name = instance.replace('data/wcnf-instances/','')
    #     instance_name = instance_name.replace('.wcnf','')

    #     # convert instance file to WCNF
    #     wcnf = WCNF(from_file=instance)
    #     weights = wcnf.wght
    #     clauses = [clause for clause in wcnf.unweighted().clauses if len(clause) > 0]
    #     cnf = CNF(from_clauses=clauses)
    #     print(f"nv={cnf.nv} #clauses={len(clauses)} #hard={len(WCNF(from_file=instance).hard)} #soft={len(WCNF(from_file=instance).soft)}")

    #     ## execution extension 6 (tias code)
    #     parameters = {
    #         'extension': 'greedy_no_param',
    #         'output':f"{folder_path}{instance_name}_greedy_no_param.json",
    #         'cutoff_main': 15 * 60,
    #     }
    #     print(f"Greedy no parameters: {folder_path}{instance_name}_greedy_no_param.json")
    #     omus(cnf, parameters=parameters, weights=weights)

    #     ## execution extension 3 with different parameters combinations
    #     # variables
    #     cnt = 1
    #     for sorting in ClauseSorting:
    #         for clause_counting in ClauseCounting:
    #             for unit_literal in UnitLiteral:
    #                 for best_literal in BestLiteral:
    #                     outputfile = f"{folder_path}{instance_name}_greedy_param_{cnt}.json"
    #                     print(f"Greedy with parameters: {outputfile}")
    #                     print("---- ClauseCounting=", clause_counting, "UnitLiteral=", unit_literal, "BestLiteral=", best_literal)
    #                     parameters = {
    #                         # clause counting
    #                         'count_clauses' : clause_counting,
    #                         'best_unit_literal': unit_literal,
    #                         'best_counter_literal': best_literal,
    #                         'sorting': sorting,
    #                         'extension': 'greedy_param',
    #                         'cutoff_main': 15 * 60,
    #                         'output': outputfile,
    #                     }
    #                     omus(cnf, parameters=parameters, weights=weights)
    #                     cnt += 1


    # for instance in easy_cnf_instances:
    #     # instance variables
    #     instance_name = instance.replace('data/wcnf-instances/','')
    #     instance_name = instance_name.replace('.wcnf','')
    #     # convert instance file to WCNF
    #     wcnf = WCNF(from_file=instance)
    #     weights = wcnf.wght
    #     clauses = [clause for clause in wcnf.unweighted().clauses if len(clause) > 0]
    #     cnf = CNF(from_clauses=clauses)
    #     print(f"nv={cnf.nv} #clauses={len(clauses)} #hard={len(WCNF(from_file=instance).hard)} #soft={len(WCNF(from_file=instance).soft)}")
    #     ## Local Search : SATLike
    #     ## parameters found in code
    #     print(wcnf.soft)
    #     if mean(weights[i] for i in range(len(wcnf.soft))) > 10000:
    #         h_inc=300
    #         softclause_weight_threshold=500
    #     else:
    #         h_inc=3
    #         softclause_weight_threshold=0

    #     parameters = {
    #         'extension': 'satlike',
    #         'output': f"{folder_path}{instance_name}_satlike.json",
    #         'cutoff' : 15,
    #         'h_inc' : 3,
    #         'max_restart':5,
    #         's_inc' : softclause_weight_threshold,
    #         'pb_restarts': 0.001,
    #         # 'pb_restarts': 0,
    #         'cutoff_main': 60 * 60,
    #         'sp': 0.01 # smooth probability found in code.... not realy the one in the paper
    #     }
    #     print(f"SATLike: {folder_path}{instance_name}_satlike.json")
    #     omus(cnf, parameters=parameters, weights=weights)

    # for instance in easy_cnf_instances:
    #     # instance variables
    #     instance_name = instance.replace('data/wcnf-instances/','')
    #     instance_name = instance_name.replace('.wcnf','')
    #     # convert instance file to WCNF
    #     wcnf = WCNF(from_file=instance)
    #     weights = wcnf.wght
    #     clauses = [clause for clause in wcnf.unweighted().clauses if len(clause) > 0]
    #     cnf = CNF(from_clauses=clauses)
    #     print(f"nv={cnf.nv} #clauses={len(clauses)} #hard={len(WCNF(from_file=instance).hard)} #soft={len(WCNF(from_file=instance).soft)}")
    #     ## Maxprop with or with unit prop
    #     cnt = 1
    #     for unit_literal in UnitLiteral:
    #         for best_literal in BestLiteral:
    #             print("UnitLiteral=", unit_literal, "BestLiteral=", best_literal)
    #             parameters = {
    #                 'extension': 'maxprop',
    #                 'output': f"{folder_path}{instance_name}_maxprop_{cnt}.json",
    #                 'cutoff_main': 15 * 60,
    #                 'best_counter_literal': best_literal,
    #                 'best_unit_literal': unit_literal
    #             }
    #             print(f"{folder_path}{instance_name}_maxprop_{cnt}.json")
    #             omus(cnf, parameters=parameters, weights=weights)
    #             cnt +=1

def test_wcnf_instance():
    parameters = {
        # clause counting
        'count_clauses' : ClauseCounting.WEIGHTED_UNASSIGNED,
        # 'count_clauses' : ClauseCounting.WEIGHTS,
        # 'count_clauses' : ClauseCounting.VALIDATED,
        # clause sorting
        'sorting':ClauseSorting.IGNORE,
        # 'sorting':ClauseSorting.WEIGHTS,
        # 'sorting':ClauseSorting.UNASSIGNED,
        # 'reverse_sorting': True,
        # 'sorting':ClauseSorting.WEIGHTED_UNASSIGNED,
        # Unit Literal propagation
        'best_unit_literal': UnitLiteral.IMMEDIATE,
        # 'best_unit_literal': UnitLiteral.INGORE,
        # 'best_unit_literal': UnitLiteral.RANDOM,
        # 'best_unit_literal': UnitLiteral.PURE,
        # 'best_unit_literal': UnitLiteral.POLARITY,
        'best_counter_literal': BestLiteral.COUNT_POLARITY,
        # 'best_counter_literal': BestLiteral.COUNT_PURE_ONLY,
        # 'sat_model' :SatModel.BEST_WEIGHTED_UNASSIGNED_CLAUSE_COVERAGE,
        # 'top_k_models': 10,
        # 'bestModel' :SatModel.RANDOM,
        'max_steps_main': 1000,
        'extension': 5,
        'output': 'log.json',
        'cutoff' : 1,
        'h_inc' : 3,
        's_inc' : 1,
        'sp': 0.0001
        }
    instance = 'data/wcnf-instances/wBF_100_400.wcnf'
    weights = WCNF(from_file=instance).wght
    clauses = [clause for clause in WCNF(from_file=instance).unweighted().clauses if len(clause) > 0]
    cnf = CNF(from_clauses=clauses)
    print("nv:", cnf.nv, "#clauses=", len(clauses), "hard=", len(WCNF(from_file=instance).hard), "soft=",len(WCNF(from_file=instance).soft)  )
    print(omus(cnf, parameters=parameters, weights=weights))

def test_extension():
    easy_cnf_instances = wcnfInstances(difficulty= Difficulty.EASY)

    # easy_wcnf_instances = wcnfInstances(difficulty= Difficulty.EASY)
    # print(len(easy_cnf_instances) + len(easy_wcnf_instances))
    # medium_cnf_instances = cnfInstances(difficulty= Difficulty.MEDIUM)
    # print(medium_cnf_instances)
    # medium_wcnf_instances = wcnfInstances(difficulty= Difficulty.MEDIUM)
    # cnf_instances = easy_cnf_instances
    # print(medium_wcnf_instances)
    parameters = {
        # clause counting
        'count_clauses' : ClauseCounting.WEIGHTED_UNASSIGNED,
        # 'count_clauses' : ClauseCounting.WEIGHTS,
        # 'count_clauses' : ClauseCounting.VALIDATED,
        # clause sorting
        'sorting':ClauseSorting.IGNORE,
        # 'sorting':ClauseSorting.WEIGHTS,
        # 'sorting':ClauseSorting.UNASSIGNED,
        # 'reverse_sorting': True,
        # 'sorting':ClauseSorting.WEIGHTED_UNASSIGNED,
        # Unit Literal propagation
        'best_unit_literal': UnitLiteral.IMMEDIATE,
        # 'best_unit_literal': UnitLiteral.INGORE,
        # 'best_unit_literal': UnitLiteral.RANDOM,
        # 'best_unit_literal': UnitLiteral.PURE,
        # 'best_unit_literal': UnitLiteral.POLARITY,
        'best_counter_literal': BestLiteral.COUNT_POLARITY,
        # 'best_counter_literal': BestLiteral.COUNT_PURE_ONLY,
        # 'sat_model' :SatModel.BEST_WEIGHTED_UNASSIGNED_CLAUSE_COVERAGE,
        # 'top_k_models': 10,
        # 'bestModel' :SatModel.RANDOM,
        'max_steps_main': 1000,
        'extension': 3,
        'output': 'log.json',
        'local_search': False,
        'cutoff' : 3,
        'h_inc' : 3,
        's_inc' : 1,
        'sp': 0.0001
            }
    # print(omus(omus_cnf(), parameters=parameters))
    print(omus(bacchus_cnf(), parameters=parameters))

    for instance in easy_cnf_instances[:10]:
        # print(instance)
        if instance in ['data/cnf-instances/zebra_v155_c1135.cnf', 'data/cnf-instances/bf0432-007.cnf']:
            continue
        # wcnf = 
        # print(WCNF(from_file=instance).unweighted().clauses )
        weights = WCNF(from_file=instance).wght
        clauses = [clause for clause in WCNF(from_file=instance).unweighted().clauses if len(clause) > 0]
        cnf = CNF(from_clauses=clauses)
        print("nv:", cnf.nv, "#clauses=", len(clauses), "hard=", len(WCNF(from_file=instance).hard), "soft=",len(WCNF(from_file=instance).soft)  )
        print(omus(cnf, parameters=parameters, weights=weights))
        # print(len(WCNF(from_file=instance).wght))
        # print(len(WCNF(from_file=instance).unweighted().clauses))
        # cnf = CNF(from_clauses=clauses)

    # print(omus(medium_instance, parameters=parameters))

def add_nv_json_files():
    results_folder = 'data/benchmark/'
    cnf_path = 'data/cnf-instances/'
    wcnf_path = 'data/wcnf-instances/'
    f_paths = None

    # extension
    if os.path.exists(results_folder):
        f_paths = [f"{results_folder}{f}" for f in os.listdir(results_folder) if f.endswith('.json')]

    cnf_files = [f.replace('.cnf', '') for f in os.listdir(cnf_path) if f.endswith('.cnf')]
    wcnf_files = [f.replace('.wcnf', '') for f in os.listdir(wcnf_path) if f.endswith('.wcnf')]

    cnf_problems = [f for f in f_paths if any(cnf_file in f for cnf_file in cnf_files)]
    wcnf_problems = [f for f in f_paths if any(wcnf_file in f for wcnf_file in wcnf_files)]

    # for r, d, f in os.walk(folder_path):
    #     for file in f:
    #         if file.endswith('.json'):
    #             with open(file) as f_pt:
                        # if f_path in cnf_problems:
    data_instance_nv = {}
    easy_wcnf_instances = wcnfInstances(difficulty= Difficulty.EASY)[:7]
    for instance in easy_wcnf_instances:
        wcnf = WCNF(from_file=instance)
        clauses = [clause for clause in wcnf.unweighted().clauses if len(clause) > 0]
        cnf = CNF(from_clauses=clauses)
        data_instance_nv[instance.replace('data/wcnf-instances/','').replace('.wcnf', '')] = cnf.nv
    easy_cnf_instances = cnfInstances(difficulty= Difficulty.EASY) + cnfInstances(difficulty= Difficulty.MEDIUM)#[:num_instances] + 
    for instance in easy_cnf_instances:
        cnf = CNF(from_file=instance)
        data_instance_nv[instance.replace('data/cnf-instances/','').replace('.cnf', '')] = cnf.nv
    # ppprint(data_instance_nv)


    for f_path in f_paths:
        p_name = f_path.replace('data/benchmark/','') 
        matching_problem = [cnf_file for cnf_file in cnf_files + wcnf_files if cnf_file in f_path][0]

        # print(p_name, matching_problem)
        with open(f_path) as f:
            parsed_json = json.load(f)

        parsed_json['nv'] = data_instance_nv[matching_problem]

        with open(f_path, 'w') as f:
            f.write(json.dumps(parsed_json)) # use `json.loads` to do the reverse
        # print()
        # nv = 0
        # if f_path in cnf_problems:
        #     # data['type'].append('cnf')
        #     # data['p'].append([cnf_file for cnf_file in cnf_files if cnf_file in f_path][0])
        # else:
        #     # data['type'].append('wcnf')
        #     # data['p'].append([wcnf_file for wcnf_file in wcnf_files if wcnf_file in f_path][0])


def main():
    # benchmark_wcnf_files()
    benchmark_cnf_files()

if __name__ == "__main__":
    main()