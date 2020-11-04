
# def explain(params, cnf, user_vars, user_vars_cost, initial_interpretation):
#     # ous = COUS(params=params, cnf)
   

# class ExplainCSP:
#     def __init__(self, wcnf: WCNF, user_vars: list, user_vars_cost: list, initial_interpretation: list = list()):

#         # Build clauses from CNF
#         self.clauses = Clauses(wcnf, user_vars, user_vars_cost, initial_interpretation)

#     def explain(self, params=OusParams()):
#         """
#         Internal state
#         --------------
#             :params = Execution parameters
#             :COUS object = central object linked to different components (sat/opt solvers+clauses+grower):
#             - :clauses (Clauses) = Clause object to manipulate (add/remove/get inidices) clauses
#             - :sat solver = Init SAT solver bootstrapped with **cnf** (hard clauses)
#             - :opt_solver = Init optimisation solver with Given input
#             - :grower = set extension when growing
#         """
#         # TODO: setup optSolver
#         self.ous = COUS(params=params, clauses=self.clauses)


#         if params.warmstart:
#             self.ous.warm_start()

#         while(len(self.facts - self.I) > 0):
#             hs, explanation, _ = self.ous.cOUS()

#             # TODO: explaining facts - use indices instead of the clause
#             E_i = [ci for ci in explanation if ci in self.I_cnf]

#             # constraint used ('and not ci in E_i': dont repeat unit clauses)
#             # TODO: constraints - use indices instead of the clause
#             S_i = [ci for ci in explanation if ci in self.clauses.soft and ci not in E_i]

#             # TODO: Correct NEW facts derivation
#             New_info = self.ous.clauses.optProp(I=self.I, expl=E_i + S_i)
#             N_i = New_info.intersection(self.facts) - self.I

#             # add new info
#             self.I |= N_i
#             self.I_cnf += [[lit] for lit in N_i if [lit] not in self.I_cnf]

#             self.clauses.add_derived_Icnf(N_i)
#             self.ous.optSolver.set_objective()
#             self.expl_seq.append((E_i, S_i, N_i))
#             # print(New_info)
#             print(f"\nOptimal explanation \t\t {E_i} /\\ {S_i} => {N_i}\n")

#         return self.expl_seq

#     def explain_lit(self, lit):
#         pass
