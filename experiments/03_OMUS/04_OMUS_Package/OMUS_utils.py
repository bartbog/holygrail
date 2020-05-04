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

def mapping_clauses(clauses):

    union_clauses = frozenset.union(*clauses)

    sorted_vars = frozenset(sorted(map(abs, union_clauses)))

    mapping = {elem:i+1 for i, elem in enumerate(sorted_vars)}
    reversemapping = {i+1:elem for i, elem in enumerate(sorted_vars)}

    return mapping, reversemapping

def map_clauses(clauses, mapping):

    newclauses = [[mapping[abs(literal)]*sign(literal) for literal in clause] for clause in clauses]

    return newclauses


def checkConflict(literals):
    for l in literals:
        assert -l not in literals, f"conflicting literals are present {l}, {-l}"

def getLiteralsSubsetClauses(cnf_clauses, subsetClauses):

    s = set()
    
    for c in subsetClauses:
        clause = cnf_clauses[c]
        for literal in clause:
            s.add(literal)
    return s

def getClausesValidatedByLiterals(cnf_clauses, subset_clauses, literals):
    validated_clauses = set()

    for literal in literals:
        for c in subset_clauses:
            clause = cnf_clauses[c]
            if literal in clause:
                validated_clauses.add(c)
    return validated_clauses

def maxsat_fprime(cnf_clauses, F_prime):
    new_F_prime = set(F_prime)

    return new_F_prime

# def extension4(clauses, F_prime, model):

#     if not F_prime :
#         return [], True

#     with  RC2(WCNF()) as rc2:
#         wcnf = WCNF()
#         for idx, clause in enumerate(clauses):
#             if idx in F_prime:
#                 wcnf.append(list(clause))
#             else:
#                 wcnf.append(list(clause), weight = len(clause))  
        
#         rc2.init(formula=wcnf)
#         for maxsatModel in rc2.enumerate():
#             print(maxsatModel, rc2.cost)
#             print("maxsat model", maxsatModel, "cost=", rc2.cost )

#     return F_prime, model

# def hitman_hittingset(clauses):

#     with Hitman(solver='m22', htype='lbx') as h:

#         for clause in clauses:
#             h.hit(clause)
#         hs = h.get()
#     return hs

# def extension4(clauses, F_prime, model):

#     if not F_prime :
#         return [], True

#     # cnf_clauses = [clauses[i] for i in F_prime]

#     # mapping, reverse_mapping = mapping_clauses(cnf_clauses)
#     # mapped_clauses = map_clauses(cnf_clauses, mapping)


#     with  RC2(formula = WCNF()) as rc2:
#         for idx, clause in enumerate(clauses):
#             if idx in F_prime:
#                 rc2.add_clause(list(clause))
#             else:
#                 rc2.add_clause(list(clause), weight = len(clause))  
        
#         maxsatModel = rc2.compute()
#         print("clauses", clauses, "F_prime:", F_prime, "model", model,"maxsatmodel:", maxsatModel )
#     #     ppprint(mapping)
#     #     ppprint(reverse_mapping)

#     #     for clause in mapped_clauses:
#     #         rc2.add_clause(clause, weight=len(clause))

#     #     model = rc2.compute()
#     #         print("model:", model, "cost:",  rc2.cost)
#     # for literal, pos in mapping.items():       

#     return F_prime, maxsatModel