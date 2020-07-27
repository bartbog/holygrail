#!/usr/bin/python3
"""
Logic grid puzzle: 'origin' in CPpy

Based on... to check originally, currently part of ZebraTutor
Probably part of Jens Claes' master thesis, from a 'Byron...' booklet
"""
import sys
sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
from cppy import *
from pathlib import Path
import re
# import numpy
# import pandas as pd

# model2 = Model([ implies( ((BoolVar() | BoolVar()) & BoolVar()) , ~BoolVar() )   ])
# print(model2)
# cnf2, new_vars = model2.to_cnf()
# print(new_vars)
# for i, formula in enumerate(cnf2):
#     print(i, formula, formula.to_cnf())
print("\nCNF:")
p, q, r, s = BoolVar(), BoolVar(), BoolVar(), BoolVar()
p.name, q.name, r.name, s.name = "p", "q", "r", "s"
# p, q, r = BoolVar(), BoolVar(), BoolVar()
# p.name, q.name, r.name = "p", "q", "r"
# m3 = (p | q) & r
# print(tseitin_transform(m3))
# print(tseitin_transform(m2))
# m1 = implies( (( p| q ) & r) , s )
# m1 =  p& q 
m1 = ((p & q) & r) | s
# m1 = implies( ( p| q ) & r)
print(tseitin_transform(m1))


# # q = 

# p, q = BoolVar(), BoolVar()



# print(ts)