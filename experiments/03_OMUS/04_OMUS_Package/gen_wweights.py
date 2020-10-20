import json
import random
import time
from datetime import date, datetime
from pathlib import Path
import sys

# pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

# omus imports
import pprint

from omus import OMUS, OMUSBase

from test_explain import originProblem

from csp_explain import omusExplain, maxPropagate, optimalPropagate, cost

sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
sys.path.append('/home/emilio/Documents/cppy_src/')
# from cppy.solver_interfaces.pysat_tools import
from cppy.model_tools.to_cnf import *
from cppy import BoolVarImpl, Comparison, Model, Operator, cnf_to_pysat

import pandas as pd

import matplotlib.pyplot as plt
import numpy as np


def generate_weights(instance):
    clauses = CNF(from_file=instance).clauses
    weights = random.choices(list(range(1, 21)), k=len(clauses))
    return weights

explanation_dir = '/home/crunchmonster/Documents/VUB/01_SharedProjects/03_holygrail/experiments/03_OMUS/04_OMUS_Package/data/experiment1/SW100-8-0'
pexp1 = Path(explanation_dir)

for x in pexp1.iterdir():
    d = {
        'weights':generate_weights(x)
    }
    # weights = generate_weights(x)
    # print(weights)
    with open('/home/crunchmonster/Documents/VUB/01_SharedProjects/03_holygrail/experiments/03_OMUS/04_OMUS_Package/data/experiment1/' + x.stem + ".json" , 'w') as fp:
        json.dump(d, fp)