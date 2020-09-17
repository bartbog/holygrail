from collections import Counter

# Gurobi utilities
import gurobipy as gp
from gurobipy import GRB
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

from ous_utils import BenchmarkInfo, Clauses, OusParams, Steps, Timings


class OUS(object):

    def __init__(self, logging=False, params=OusParams()):
        self.params = params
        self.do_logging(logging)
        self.__clauses = Clauses()
        self.h_counter = Counter()
        self.SS = set()
        self.__satsolver = None
        self.grow_extension = None
        self.f_cost = f_cost

        if self.params.constrained:
            self.opt_model = self.gurobi_cOUSModel()

    @property
    def clauses(self): return self.__clauses.clauses

    @property
    def weights(self): return self.__clauses.weights

    @property
    def clauses_idxs(self): return self.__clauses.clause_idxs

    def add_hardClauses(self, added_clauses: list):
        self.__clauses.add_hardclauses(added_clauses)
        if self.__satsolver is not None:
            self.__satsolver.append_formula(added_clauses, no_return=False)
        #TODO: add clasues to satsolver

    def add_softClauses(self, added_clauses: list, added_weights: list):
        self.__clauses.add_soft_clauses(added_clauses, added_weights)
        if self.__satsolver is not None:
            self.__satsolver.append_formula(added_clauses, no_return=False)
        #TODO: add clasues to satsolver

    def do_logging(self, logging: bool = True):
        if logging:
            self.params.benchmark = True
            self.benchmark_info = BenchmarkInfo()

    def reuse_satSolver(self, use_sat: bool = True):
        if use_sat:
            self.params.incremental_sat = True
            self.__satsolver = Solver()

    def set_extension(self, ext: str = 'default'):

        extensions = {
            'default': self.grow_default,
            'maxsat': self.grow_maxsat
            # 'unitprop': self.unitprop,
            # 'maxprop': self.maxprop,
            # 'greedy_param': self.greedy_param,
            # 'greedy_no_param': self.greedy_no_param,
            # 'greedy_sat': self.greedy_sat,
            # 'maxsat': self.maxsat_test,
            # 'greedy_vertical': self.greedy_vertical,
            # 'greedy_hardsoft': self.greedy_hardsoft,
            # 'grow_singlepass': self.grow_singlepass,
        }

        if ext not in extensions:
            print("Available extensions:")
            [print(e) for e in extensions]
            raise f"Wrong extension {ext}"

        self.grow_extension = extensions[ext]

    def cost(self):
        # return 0
        raise "NotImplemented"

    def gurobi_optHS(self):
        self.gurobi_model.optimize()

        x = self.g_model.getVarByName("x")
        hs = set(i for i in self.clauses_idxs if x[i].x == 1)

        return hs

    def gurobi_OUSModel(self):
        self.gurobi_model = gp.Model('MipOptimalHittingSet')

        # model parameters
        self.gurobi_model.Params.OutputFlag = 0
        self.gurobi_model.Params.LogToConsole = 0
        self.gurobi_model.Params.Threads = 1

        #TODO add variables
        raise "NotImplemented"

    def gurobi_cOUSModel(self):
        self.gurobi_model = gp.Model('MipOptimalHittingSet')

        # model parameters
        self.gurobi_model.Params.OutputFlag = 0
        self.gurobi_model.Params.LogToConsole = 0
        self.gurobi_model.Params.Threads = 1

        # update the model
        #TODO add variables
        # exactly one of the -literals
        # vals = range(self.nSoftClauses + self.nLiterals, self.nClauses)
        # self.g_model.addConstr(x[vals].sum() == 1)
        raise "NotImplemented"

        self.g_model.update()

    def gurobi_addCorrectionSet(self, C):
        x = self.g_model.getVarByName("x")

        # add new constraint sum x[j] * hij >= 1
        self.gurobi_model.addConstr(gp.quicksum(x[i] for i in C) >= 1)

    def gurobi_updObjWeights(self, I):
        x = self.g_model.getVarByName("x")

        # for i in I:
            # i_idx = self.softClauseIdxs[frozenset({i})]
            # self.obj_weights[i_idx] = 1

            # not_i_idx = self.softClauseIdxs[frozenset({-i})]
            # self.obj_weights[not_i_idx] = GRB.INFINITY

        # self.g_model.setObjective(gp.quicksum(x[i] * self.obj_weights[i] for i in range(self.nClauses)), GRB.MINIMIZE)
        raise "NotImplemented error"

    def postpone_greedyHS(self, H):
        if len(H) == 0:
            return set()

        # the hitting set
        C = set()

        # build vertical sets
        V = dict()  # for each element in H: which sets it is in

        for i, hi in enumerate(H):
            # TODO: this needs to be checked!!
            h = [e for e in hi if self.obj_weights[e] < 1e50]
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
                (c, cover) = min(c_covers, key=lambda tpl: self.obj_weights[tpl[0]])

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

    def OUS_checkSat(self, assumptions: list = []):
        if self.__satsolver is not None:
            solved = self.__satsolver.solve(assumptions=assumptions)
            model = self.__satsolver.get_model()
            return solved, model

        with Solver() as s:
            # TODO: is this correct ? 
            s.append_formula(self.clauses, no_return=False)
            solved = s.solve(assumptions=assumptions)
            model = s.get_model()
            return solved, model

    def grow_default(self, f_prime, model):
        return f_prime, model

    def grow_maxsat(self, f_prime, model):
        raise "NotImplemented"
        # wcnf = WCNF()
        # wcnf.extend(self.hard_clauses)
        # for i, clause in enumerate(self.clauses):
        #     if i in f_prime:
        #         wcnf.append(list(clause))
        #     else:
        #         wcnf.append(list(clause), weight=self.weights[i])
        
        # with RC2(wcnf) as rc2:
        #     t_model = rc2.compute()

        # for i, clause in enumerate(self.clauses):
        #     if i not in t_F_prime and len(clause.intersection(t_model)) > 0:
        #         t_F_prime.add(i)

        # return t_F_prime, t_model

    def OUS_grow(self, f_prime: set, model: set):
        grown_set, grown_model = self.grow_extension(f_prime, model)

        return grown_set, grown_model

    def OUS_postponeOpt(self, H, C, Fp):
        F = self.clauses_idxs

        while(True):
            while(H > set() and self.params.post_opt_incremental):
                # add sets-to-hit incrementally until unsat then continue with optimal method
                # given sets to hit 'CC', a hitting set thereof 'hs' and a new set-to-hit added 'C'
                # then hs + any element of 'C' is a valid hitting set of CC + C
                # choose element from C with smallest weight
                c = min(C, key=lambda i: self.weights[i])
                # find all elements with smallest weight
                m = [ci for ci in C if self.weights[ci] == self.weights[c]]
                # choose clause with smallest weight appearing most in H
                # TODO: can be problem here, because we might need to ignore some of the literals
                c_best = max(m, key=lambda ci: self.h_counter[ci])
                Fp.add(c_best)

                sat, model = self.checkSat(Fp)

                if not sat:
                    break
                C = F - self.grow(Fp, model)
                H.append(C)
                self.gurobiAddCorrectionSet(C)
                self.h_counter.update(list(C))

            if(not self.params.post_opt_greedy):
                break

            Fp = self.GreedyHS()
            sat, model = self.checkSat(Fp)

            if not sat:
                break

            H.append(C)

            self.gurobiAddCorrectionSet(C)
            self.h_counter.update(list(C))
        return H

    def OUS(self, best_cost=None):

        F = self.clauses_idxs
        H, C, Fp = set(), None, None

        # record this as part of the object
        if not self.params.constrained:
            self.gurobi_model = gurobi_OUSModel()

        if self.params.incremental and self.params.constrained:
            SSofF = set()
            for S, model in self.SS:
                S_F = S & F
                if any(True if S_F.issubset(Sp) else False for Sp in SSofF):
                    continue
                S_F, _ = self.grow(S_F, model)
                C = F - S_F
                H.append(C)
                self.h_counter.update(list(C))
                SSofF.add(S_F)

        while(True):
            if best_cost is not None and best_cost < self.cost(Fp):
                return None, None, self.cost(Fp)

            if self.params.post_opt:
                H = self.postponeOpt(H, C, Fp)

            # compute optimal hitting set 
            Fp = self.optHS()

            # check satisfiability of the hitting set
            sat, model = self.checkSat(Fp)

            # OUS
            if not sat:
                self.clean()
                return Fp, [self.clauses[idx] for idx in Fp], self.cost(Fp)

            # grow satisfiable set into (maximally) satisfiable subset
            Fpp = self.grow(Fp, model)

            if self.params.incremental and not self.params.constrained:
                self.storeMSS(F, Fpp)

            # Add MCS to collection of MCSes
            C = F - Fpp
            H.append(C)
            self.gurobiAddCorrectionSet(C)
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

    def clean(self):
        if not self.params.constrained:
            self.h_counter = Counter()
            self.__satsolver.delete()
            self.gurobi_model.dispose()

            if self.params.incremental:
                self.cleanMSS()
