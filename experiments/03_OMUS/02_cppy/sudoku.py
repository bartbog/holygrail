#!/usr/bin/python3
"""
Sudoku problem in CPpy

Based on the Numberjack model of Hakan Kjellerstrand
"""
import sys
sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
from cppy import *
import numpy

# there is at least one numer in each entry
v = BoolVar()
v.name = 111
print(v)