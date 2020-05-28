import json
from enum import Enum

sign = lambda x: (1, -1)[x < 0]

class HittingSetSolver(Exception):
    """Exception raised for errors in the input.

    Attributes:
        status -- status of the solver
        message -- explanation of the error
    """

    def __init__(self, status, data):
        self.status = status
        self.message = 'Hitting Set linear Solver returned status:' + str(status) + "\n\n"

        self.message += "min " + " + ".join(  [f"x[{idx}] x {data['obj_coeffs'][idx]}" for idx in data['indices']]) + "\n\n"
        for i in range(data['num_constraints']):
            self.message += " ".join([f"{data['constraint_coefficients'][i][j]} * x[{idx}]" for j, idx in enumerate(data['indices'])])
            self.message + " >= " + str(data['bounds'][i]) + "\n\n"

class Difficulty(Enum):
    EASY = 1
    MEDIUM = 2
    HARD = 3
    ALL = 0

    @staticmethod
    def list():
        return list(map(lambda c: c.value, Difficulty))

class ClauseCounting(IntEnum):
    VALIDATED = 1
    WEIGHTS = 2
    WEIGHTED_UNASSIGNED = 3

class ClauseSorting(IntEnum):
    IGNORE = 0
    WEIGHTS = 1
    UNASSIGNED = 2
    WEIGHTED_UNASSIGNED = 3
    LITERAL_ORDERING = 4

class BestLiteral(IntEnum):
    COUNT_PURE_ONLY = 1
    COUNT_POLARITY = 2

class UnitLiteral(IntEnum):
    IGNORE = 0
    RANDOM = 1
    SINGLE_POLARITY = 2
    POLARITY = 3
    IMMEDIATE = 4

class SatModel(IntEnum):
    RANDOM = 1
    BEST_CLAUSES_VALIDATED = 2
    BEST_CLAUSE_WEIGHTS_COVERAGE = 3
    BEST_WEIGHTED_UNASSIGNED_CLAUSE_COVERAGE = 4
    ALL = 5


# def mapping_clauses(clauses):

#     union_clauses = frozenset.union(*clauses)

#     sorted_vars = frozenset(sorted(map(abs, union_clauses)))

#     mapping = {elem:i+1 for i, elem in enumerate(sorted_vars)}
#     reversemapping = {i+1:elem for i, elem in enumerate(sorted_vars)}

#     return mapping, reversemapping

# def map_clauses(clauses, mapping):

#     newclauses = [[mapping[abs(literal)]*sign(literal) for literal in clause] for clause in clauses]

#     return newclauses


# def checkConflict(literals):
#     for l in literals:
#         assert -l not in literals, f"conflicting literals are present {l}, {-l}"

# def getLiteralsSubsetClauses(cnf_clauses, subsetClauses):

#     s = set()

#     for c in subsetClauses:
#         clause = cnf_clauses[c]
#         for literal in clause:
#             s.add(literal)
#     return s

# def getClausesValidatedByLiterals(cnf_clauses, subset_clauses, literals):
#     validated_clauses = set()

#     for literal in literals:
#         for c in subset_clauses:
#             clause = cnf_clauses[c]
#             if literal in clause:
#                 validated_clauses.add(c)
#     return validated_clauses

