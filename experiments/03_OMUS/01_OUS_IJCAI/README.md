# Welcome to OUS

OUS uses [CPpy](https://github.com/tias/cppy) to model and translate constraint problems into CNF to be explained using the OMUS class and the OMUS2 class.
OMUS aims to find the optimal unsatisfiable subset of clauses for a given literal and a given cost function or given clause weights.

## Usage requirements

The *OMUS package* requires:

- CPpy found at [CPPY](https://github.com/tias/cppy)
- PySAT:
        pip install python-sat

- Gurobi found at [GUROBI install link](https://www.gurobi.com/documentation/9.0/quickstart_mac/the_grb_python_interface_f.html)

## Explaining how to solve a constraint satisfaction problem

The ```explain.py``` file contains 2 examples of generating the explanations of each of the steps required to solve a constraint satisfaction problem:

- ```test_frietkot```  contains test cases for explaining the frietkot problem, defined by [frietkot-problem](http://homepages.vub.ac.be/~tiasguns/frietkot/). The frietkot problem is defined as the set of possible french fries sauce choices for every person. However, 1 sauce can only be attributed to 1 specific person. The purpose to find a satisfying assignment.
- ```explain_origin``` contains a test case for explaining how to solve the origin puzzle defined in [originPuzle](https://bartbog.github.io/zebra/origin/)


## Implementation details

The overall code needs refractoring and will be made available at the following github repository [OUS](https://github.com/sourdough-bread/OUS).
