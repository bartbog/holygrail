from collections import Counter

# Gurobi utilities
import gurobipy as gp
from gurobipy import GRB

from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
from pysat.examples.rc2 import RC2

from ous_utils import BenchmarkInfo, Clauses, OusParams, Steps, Timings, profile


class OUS(object):
    def __init__(self, logging=False, params=OusParams(), clauses=Clauses(), fullI=None):
        self.params = params
        self.do_logging(logging)
        self.__clauses = clauses
        self.h_counter = Counter()
        self.SS = set()
        self.__satsolver = None
        self._grow_extension = None
        self.lit = None

        if fullI is not None:
            self.__clauses.add_I(fullI)

        if self.params.constrained:
            self.gurobi_cOUSModel()

        if params.extension is not None and params.extension != '':
            self.grow_extension = 'maxsat'

    @property
    def grow_extension(self):
        return self._grow_extension

    @grow_extension.setter
    def grow_extension(self, value):

        grow_extensions = {
            'default': self.grow_default,
            'maxsat': self.grow_maxsat,
        }

        assert value in grow_extensions

        self._grow_extension = grow_extensions[value]

    def __str__(self):
        return f"""
        params={str(self.params)},
        clauses={str(self.__clauses)},
        """

    # Clause properties
    @property
    def clauses(self): return self.__clauses.all_clauses

    @property
    def soft_clauses(self): return self.__clauses.soft_clauses

    @property
    def hard_clauses(self): return self.__clauses.hard_clauses

    @property
    def weights(self): return self.__clauses.weights

    @property
    def obj_weights(self):
        return self.__clauses.obj_weights

    @property
    def soft_idxs(self):
        return self.__clauses.soft_idxs

    @property
    def I_idxs(self):
        if self.params.constrained:
            return self.__clauses.I_idxs
        else:
            raise NotImplementedError()

    @property
    def nClauses(self):
        if self.params.constrained:
            return len(self.__clauses.all_soft_clauses)
        else:
            return self.__clauses.nSoft + self.__clauses.nDerived + 1

    @property
    def clause_idxs(self):
        if self.params.constrained:
            # Clause indexes covers all soft indexes + Icnf_all + (-Icnf_all)
            return self.__clauses.all_soft_clauses_idxs
        else:
            # Clause indexes covers all soft indexes + Icnf_derived + (-lit)
            return self.__clauses.soft_I_lit_clause_idxs

    def add_hardClauses(self, added_clauses: list):
        self.__clauses.add_hardclauses(added_clauses)

    def add_softClauses(self, added_clauses: list, added_weights: list):
        self.__clauses.add_soft_clauses(added_clauses, added_weights)

    def add_IndicatorVars(self, added_weights=None):
        # if added_weights is None:
        return self.__clauses.add_indicatorVars(added_weights)

    def add_I(self, added_I):
        self.__clauses.add_I(added_I, self.params.constrained)

    def add_derived_I(self, derived_I):
        # print("Derived i:", derived_I)
        self.__clauses.add_derived_Icnf(derived_I)
        if self.params.constrained:
            self.gurobi_set_objective()

    def gurobi_set_objective(self):
        x = self.opt_model.getVars()

        self.opt_model.setObjective(gp.quicksum(x[i] * self.obj_weights[i] for i in self.clause_idxs), GRB.MINIMIZE)

    def do_logging(self, logging: bool = True):
        if logging:
            self.params.benchmark = True
            self.benchmark_info = BenchmarkInfo()

    def reuse_satSolver(self, use_sat: bool = True):
        if use_sat:
            self.params.incremental_sat = True
            self.__satsolver = Solver(bootstrap_with=self.hard_clauses)

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

    def cost(self, Fp):
        return 0
        # raise "NotImplemented"

    def gurobi_optHS(self):
        self.opt_model.optimize()
        x = self.opt_model.getVars()
        hs = set(i for i in range(self.nClauses) if x[i].x == 1)

        return hs

    def gurobi_OUSModel(self):
        self.opt_model = gp.Model('OptHS')

        # model parameters
        self.opt_model.Params.OutputFlag = 0
        self.opt_model.Params.LogToConsole = 0
        self.opt_model.Params.Threads = 8

        #TODO add variables
        raise "NotImplemented"

    def gurobi_cOUSModel(self):
        assert self.__clauses.nSoft + 2 * self.__clauses.nCNFLits == self.nClauses, "check nclauses"
        assert len(self.__clauses.obj_weights) == self.nClauses, "#weights != #clauses"

        self.opt_model = gp.Model('constrOptHS')

        # model parameters
        self.opt_model.Params.OutputFlag = 0
        self.opt_model.Params.LogToConsole = 0
        self.opt_model.Params.Threads = 8
        # update the model
        x = self.opt_model.addMVar(
            shape=self.nClauses,
            vtype=GRB.BINARY,
            obj=self.__clauses.obj_weights,
            name="x")

        # exactly one of the -literals
        vals = range(self.__clauses.nSoft + self.__clauses.nCNFLits, self.nClauses)
        self.opt_model.addConstr(x[vals].sum() == 1)

        # at least one of the soft clauses
        vals2 = range(self.__clauses.nSoft  + self.__clauses.nCNFLits)
        self.opt_model.addConstr(x[vals2].sum() >= 1)

        self.opt_model.update()

    def gurobi_addCorrectionSet(self, C):
        # x = self.opt_model.getVarByName("x")
        x = self.opt_model.getVars()

        # add new constraint sum x[j] * hij >= 1
        self.opt_model.addConstr(gp.quicksum(x[i] for i in C) >= 1)

    def postpone_greedyHS(self, H):
        soft_weights = self.__clauses.all_soft_weights
        if len(H) == 0:
            return set()

        # the hitting set
        C = set()

        # build vertical sets
        V = dict()  # for each element in H: which sets it is in

        for i, hi in enumerate(H):
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

    def grow_default(self, f_prime, model):
        return f_prime, model

    def grow_maxsat(self, hs_in, model):
        hs = set(hs_in) # take copy!!

        wcnf = WCNF()
        wcnf.extend(self.hard_clauses)
        soft_clauses = self.__clauses.all_soft_clauses
        soft_weights = self.__clauses.all_soft_weights

        # for i in hs:
        #     clause = soft_clauses[i]
        wcnf.extend([list(soft_clauses[i]) for i in hs])
        wcnf.extend(
            [list(clause) for i, clause in enumerate(soft_clauses) if i not in hs],
            [soft_weights[i] for i in range(len(soft_clauses)) if i not in hs])

        # for i, clause in enumerate(soft_clauses):
        #     if i not in hs:
        #         wcnf.append(list(clause), weight=soft_weights[i])

        with RC2(wcnf) as rc2:
            t_model = rc2.compute()
            if t_model is None:
                return hs, model
            # TODO: This might not be correct
            for i, clause in enumerate(soft_clauses):
                if i not in hs and len(clause.intersection(t_model)) > 0:
                    hs.add(i)

            return hs, t_model

    def grow(self, f_prime: set, model: set):
        grown_set, grown_model = self.grow_extension(f_prime, model)

        return grown_set, grown_model

    def postponeOpt(self, H, C, Fp):
        soft_weights = self.__clauses.all_soft_weights
        F = self.clause_idxs
        print(self.h_counter)

        if C is None:
            return H

        while(True):
            while (len(H) > 0 and self.params.post_opt_incremental):
                Csoft = C & (self.soft_idxs)
                Crest = C - Csoft

                if len(Csoft) == 0:
                    c = max(self.soft_idxs, key=lambda i: self.h_counter[i])
                else:
                    c = min(Crest, key=lambda i: soft_weights[i])

                # add sets-to-hit incrementally until unsat then continue with optimal method
                # given sets to hit 'CC', a hitting set thereof 'hs' and a new set-to-hit added 'C'
                # then hs + any element of 'C' is a valid hitting set of CC + C
                # choose element from C with smallest weight
                # c = min(C, key=lambda i: self.weights[i])
                # # find all elements with smallest weight
                # m = [ci for ci in C if self.weights[ci] == self.weights[c]]
                # # choose clause with smallest weight appearing most in H
                # # TODO: can be problem here, because we might need to ignore some of the literals
                # c_best = max(m, key=lambda ci: self.h_counter[ci])
                Fp.add(c)

                sat, model = self.checkSat(Fp)

                if not sat:
                    break

                Fpp, Fpp_model = self.grow(Fp, model)
                C = F - Fpp
                H.append(C)
                self.gurobi_addCorrectionSet(C)
                self.h_counter.update(list(C))

            if(not self.params.post_opt_greedy):
                break

            Fp = self.postpone_greedyHS(H)
            sat, model = self.checkSat(Fp)

            if not sat:
                break

            H.append(C)
            self.gurobi_addCorrectionSet(C)
            self.h_counter.update(list(C))
        return H

    def checkSat(self, assumptions: list = []):
        # print(assumptions)
        if self.__satsolver is not None:
            polarities = []
            if self.params.constrained:
                all_soft = self.__clauses.all_soft_clauses
                for i in assumptions:
                    cl = all_soft[i]
                    # if len(cl) == 1:
                    # print(next(iter(cl)))
                    polarities.append(next(iter(cl)))
            else:
                raise NotImplementedError("Checksat not constrained not implemented")

            solved = self.__satsolver.solve(assumptions=polarities)
            model = self.__satsolver.get_model()
            return solved, model

        print("creating new solver")
        with Solver() as s:
            s.append_formula(self.clauses, no_return=False)
            solved = s.solve(assumptions=assumptions)
            model = s.get_model()
            return solved, model

    def optHS(self):
        return self.gurobi_optHS()

    @profile(sort_by='cumulative', lines_to_print=None, strip_dirs=True)
    def OUS(self, best_cost=None, lit=None):
        assert self.params.constrained == self.__clauses.constrainedOUS, "Parameters must be equal."
        F = self.clause_idxs
        H, C, Fp = [], None, None

        # record this as part of the object
        if not self.params.constrained:
            assert lit is not None, "Lit not given for OUS"
            self.gurobi_OUSModel()
            self.lit = frozenset({lit})

            if self.params.incremental:
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
        # print(self.checkSat([0, 232]))
        # return
        # print(F)
        # print(self.__clauses)
        while(True):
            # print("\n\n")
            if best_cost is not None and best_cost < self.cost(Fp):
                return None, None, self.cost(Fp)

            if self.params.post_opt:
                H = self.postponeOpt(H, C, Fp)

            # compute optimal hitting set
            Fp = self.optHS()
            # print("Fp=", Fp)
            # print(Fp, ":", [list(self.__clauses.all_soft_clauses[idx]) for idx in Fp])

            # check satisfiability of the hitting set
            sat, model = self.checkSat(Fp)
            # print("sat=", sat)
            # print("model=", model)

            # OUS
            if not sat:
                # print(Fp, [self.__clauses.all_soft_clauses[idx] for idx in Fp])
                self.cleanOUS()
                return Fp, [self.__clauses.all_soft_clauses[idx] for idx in Fp], self.cost(Fp)

            # grow satisfiable set into (maximally) satisfiable subset
            Fpp, Fpp_model = self.grow(Fp, model)
            # print("Fpp=", Fpp)
            # print("Fpp_model=", Fpp_model)

            if self.params.incremental and not self.params.constrained:
                self.storeMSS(F, Fpp)

            # Add MCS to collection of MCSes
            C = F - Fpp
            H.append(C)
            self.gurobi_addCorrectionSet(C)
            self.h_counter.update(list(C))
            # print("C=", C)
            # print("F=", F)

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

    def cleanOUS(self):
        # self.h_counter = Counter()
        # self.__satsolver.delete()

        if self.params.incremental and not self.params.contrained:
            self.cleanMSS()

    def print_clauses(self):
        c = self.__clauses.all_clauses
        for cl in c:
            print(cl)

    def clean(self):
        self.__satsolver.delete()
        self.opt_model.dispose()

        self.__clauses.clean()
        del self.__clauses
