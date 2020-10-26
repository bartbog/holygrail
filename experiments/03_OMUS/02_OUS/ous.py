from collections import Counter

from ous_utils import BenchmarkInfo, Clauses, OusParams, profileFunc
from gurobipy import GRB


class OUS(object):
    def __init__(self, optSolver=None, params=OusParams(), clauses=Clauses(), grower=None, satSolver=None):
        # OUS active objects
        self.params = params
        self.clauses = clauses
        self.satSolver = satSolver
        self.optSolver = optSolver
        self.grower = grower

        # OUS active variables
        self.h_counter = Counter()
        self.SS = set()
        self.H = []

    def __str__(self):
        return f"""
        params={str(self.params)},
        clauses={str(self.clauses)},
        """

    # # Clause properties
    # @property
    # def clauses(self): return self.clauses.all_clauses

    # @property
    # def soft_clauses(self): return self.clauses.soft_clauses

    # @property
    # def hard_clauses(self): return self.clauses.hard_clauses

    # @property
    # def weights(self): return self.clauses.weights

    # @property
    # def obj_weights(self):
    #     return self.clauses.obj_weights

    # @property
    # def soft_idxs(self):
    #     return self.clauses.soft_idxs

    # @property
    # def I_idxs(self):
    #     if self.params.constrained:
    #         return self.clauses.I_idxs
    #     else:
    #         raise NotImplementedError()

    # @property
    # def nClauses(self):
    #     if self.params.constrained:
    #         return len(self.clauses.all_soft_clauses)
    #     else:
    #         return self.clauses.nSoft + self.clauses.nDerived + 1

    # @property
    # def clause_idxs(self):
    #     if self.params.constrained:
    #         # Clause indexes covers all soft indexes + Icnf_all + (-Icnf_all)
    #         return self.clauses.all_soft_clauses_idxs
    #     else:
    #         # Clause indexes covers all soft indexes + Icnf_derived + (-lit)
    #         return self.clauses.soft_I_lit_clause_idxs

    # def add_hardClauses(self, added_clauses: list):
    #     self.clauses.add_hardclauses(added_clauses)

    # def add_softClauses(self, added_clauses: list, added_weights: list):
    #     self.clauses.add_soft_clauses(added_clauses, added_weights)

    # def add_IndicatorVars(self, added_weights=None):
    #     # if added_weights is None:
    #     return self.clauses.add_indicatorVars(added_weights)

    # def add_I(self, added_I):
    #     self.clauses.add_I(added_I, self.params.constrained)

    # def add_derived_I(self, derived_I):
    #     # print("Derived i:", derived_I)
    #     self.clauses.add_derived_Icnf(derived_I)
    #     if self.params.constrained:
    #         self.gurobi_set_objective()

    def warm_start(self):
        pass

    def seed_MSS(self, H):
        F = self.clause_idxs
        SSofF = set()
        for S, model in self.SS:
            S_F = S & F

            if any(True if S_F.issubset(Sp) else False for Sp in SSofF):
                continue

            S_F, _ = self.grower.grow(S_F, model)
            C = F - S_F
            H.append(C)
            self.h_counter.update(list(C))
            SSofF.add(S_F)

    def cost(self, Fp):
        return 0
        # raise "NotImplemented"

    def postpone_greedyHS(self):
        soft_weights = self.clauses.all_soft_weights
        if len(self.H) == 0:
            return set()

        # the hitting set
        C = set()

        # build vertical sets
        V = dict()  # for each element in H: which sets it is in

        for i, hi in enumerate(self.H):
            h = [e for e in hi if soft_weights[e] < GRB.INFINITY]
            # special case: only one element in the set, must be in hitting set
            if len(h) == 1:
                C.add(next(iter(h)))
            else:
                for e in h:
                    if not e in V:
                        V[e] = set([i])
                    else:
                        V[e].add(i)

        # special cases, remove from V so they are not picked again
        for c in C:
            if c in V:
                del V[c]

        while len(V) > 0:
            # special case, one element left
            if len(V) == 1:
                C.add(next(iter(V.keys())))
                break

            # get element that is in most sets, using the vertical views
            (c, cover) = max(V.items(), key=lambda tpl: len(tpl[1]))
            c_covers = [tpl for tpl in V.items() if len(tpl[1]) == len(cover)]

            if len(c_covers) > 1:
                # OMUS : find set of unsatisfiable clauses in hitting set with least total cost
                # => get the clause with the most coverage but with the least total weight
                # print(c_covers, weights)
                (c, cover) = min(c_covers, key=lambda tpl: soft_weights[tpl[0]])

            del V[c]
            C.add(c)

            # update vertical views, remove covered sets
            for e in list(V):
                # V will be changed in this loop
                V[e] -= cover
                # no sets remaining with this element?
                if len(V[e]) == 0:
                    del V[e]

        return C

    def postponeOpt(self, C, Fp):
        soft_weights = self.clauses.all_soft_weights
        F = self.clause_idxs

        if C is None:
            return self.H

        while(True):
            while (len(self.H) > 0 and self.params.post_opt_incremental):
                Csoft = C & (self.soft_idxs)
                Crest = C - Csoft

                # add sets-to-hit incrementally until unsat then continue with optimal method
                # given sets to hit 'CC', a hitting set thereof 'hs' and a new set-to-hit added 'C'
                # then hs + any element of 'C' is a valid hitting set of CC + C
                # choose element from C with smallest weight
                if len(Csoft) == 0:
                    c = max(self.soft_idxs, key=lambda i: self.h_counter[i])
                else:
                    c = min(Crest, key=lambda i: soft_weights[i])

                Fp.add(c)

                sat, model = self.checkSat(Fp)

                if not sat:
                    break

                Fpp, Fpp_model = self.grow(Fp, model)
                C = F - Fpp
                self.H.append(C)
                self.gurobi_addCorrectionSet(C)
                self.h_counter.update(list(C))

            if(not self.params.post_opt_greedy):
                break

            Fp = self.postpone_greedyHS()
            sat, model = self.checkSat(Fp)

            if not sat:
                break

            self.H.append(C)
            self.gurobi_addCorrectionSet(C)
            self.h_counter.update(list(C))
        # return H

    def OUS(self, best_cost=None, lit=None):
        F = self.clause_idxs
        H, C, Fp = [], None, None
        self.lit = frozenset({lit})

        #TODO: modify gurobi model
        self.gurobi_OUSModel()
        # record this as part of the object

        while(True):
            # print("\n\n")
            if best_cost is not None and best_cost < self.cost(Fp):
                return None, None, self.cost(Fp)

            if self.params.post_opt:
                H = self.postponeOpt(H, C, Fp)

            # compute optimal hitting set
            Fp = self.optHS()
            # print("Fp=", Fp)
            # print(Fp, ":", [list(self.clauses.all_soft_clauses[idx]) for idx in Fp])

            # check satisfiability of the hitting set
            sat, model = self.satSolver.checkSat(Fp)
            # print("sat=", sat)
            # print("model=", model)

            # OUS
            if not sat:
                # print(Fp, [self.clauses.all_soft_clauses[idx] for idx in Fp])
                self.cleanOUS()
                return Fp, [self.clauses.all_soft_clauses[idx] for idx in Fp], self.cost(Fp)

            # grow satisfiable set into (maximally) satisfiable subset
            Fpp, Fpp_model = self.grow(Fp, model)

            if self.params.incremental and not self.params.constrained:
                self.storeMSS(F, Fpp)

            # Add MCS to collection of MCSes
            C = F - Fpp
            H.append(C)
            self.optSolver.addCorrectionSet(C)
            self.h_counter.update(list(C))

    @profileFunc(sort_by='cumulative', lines_to_print=20, strip_dirs=True)
    def cOUS(self):
        F = self.clause_idxs
        C, Fp = None, None

        while(True):

            if self.params.post_opt:
                self.postponeOpt(C, Fp)

            # compute optimal hitting set
            Fp = self.optSolver.optHS()

            # check satisfiability of the hitting set
            sat, model = self.satSolver.checkSat(Fp)

            # OUS
            if not sat:
                # print(Fp, [self.clauses.all_soft_clauses[idx] for idx in Fp])
                return Fp, [self.clauses.all_soft_clauses[idx] for idx in Fp], self.cost(Fp)

            # grow satisfiable set into (maximally) satisfiable subset
            Fpp, _ = self.grower.grow(Fp, model)

            # Add MCS to collection of MCSes
            C = F - Fpp
            self.H.append(C)
            self.optSolver.addCorrectionSet(C)
            self.h_counter.update(list(C))

    def cleanMSS(self):
        keep = set()
        for (m1, m1_model) in self.SS:
            keep_m1 = True
            for (m2, _) in self.SS:
                if m1 != m2 and m1 < m2:
                    keep_m1 = False
            if keep_m1:
                keep.add((m1, m1_model))
        self.SS = keep

    def print_clauses(self):
        c = self.clauses.all_clauses
        for cl in c:
            print(cl)
