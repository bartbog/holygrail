# from pysat.formula import CNF, WCNF
# from pysat.solvers import Solver

# l = [
#     [1, 9, 10, 11], 
#     [2, 9, 10, -11], 
#     [3, 9, -10, 11], 
#     [4, 9, -10, -11], 
#     [5, -9, 10, 11], 
#     [6, -9, 10, -11], 
#     [7, -9, -10, 11], 
#     [8, -9, -10, -11]
#     ]
# with Solver() as s:
#     s.append_formula(l, no_return=False)
#     solved = s.solve(assumptions=[-1, -2, -3, -4, -5, 6, 7, 8])
#     model = s.get_model()
#     print(model, solved)


#!/usr/bin/python
class Point:
   def __init__( self, x=0, y=0):
      self.x = x
      self.y = y
   def __del__(self):
      class_name = self.__class__.__name__
      print (class_name, "destroyed")
pt1 = Point()
pt2 = pt1
pt3 = pt1
print (id(pt1), id(pt2), id(pt3)) # prints the ids of the obejcts
# del pt1
# del pt2
# del pt3