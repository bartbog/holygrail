# system utilities
from collections import Counter
from enum import Enum, IntEnum
import time
import random

# Gurobi utilities
import gurobipy as gp
from gurobipy import GRB

<<<<<<< HEAD
=======

>>>>>>> omus-explain-lb
# Pysat Utilities
from pysat.examples.rc2 import RC2
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

# interval computation
import portion as P

import json
# GLOBAL VARIABELS
MODE_OPT, MODE_INCR, MODE_GREEDY = (1, 2, 3)


def bacchus():
    cnf = CNF()
    cnf.append([6, 2])    # c1: ¬s
    cnf.append([-6, 2])    # c1: ¬s
    cnf.append([-2, 1])    # c1: ¬s
    cnf.append([-1])    # c1: ¬s
    cnf.append([-6, 8])    # c1: ¬s
    cnf.append([6, 8])    # c1: ¬s
    cnf.append([2, 4])    # c1: ¬s
    cnf.append([-4, 5])    # c1: ¬s
    cnf.append([7, 5])    # c1: ¬s
    cnf.append([-7, 5])    # c1: ¬s
    cnf.append([-5, 3])    # c1: ¬s
    cnf.append([-3])    # c1: ¬s
    parameters = {
        'extension': 'greedy_no_param',
        'output': "bacchus_log.json",
    }
    o = OMUS(from_CNF=cnf, parameters=parameters)
    print(o.omus())
    print(o.omusIncr(), o.H)


def smus():
    l = 1
    m = 2
    n = 3
    p = 4
    s = 5
    cnf = CNF()
    cnf.append([-s])    # c1: ¬s
    cnf.append([s, -p]) # c2: s or ¬p
    cnf.append([p])     # c3: p
    cnf.append([-p, m]) # c4: ¬p or m
    cnf.append([-m, n]) # c5: ¬m or n
    cnf.append([-n])    # c6: ¬n
    cnf.append([-m, l]) # c7 ¬m or l
    cnf.append([-l])    # c8 ¬l

    parameters = {
        'extension': 'greedy_no_param',
        'output': "smus_log.json"
    }
    o = OMUS(from_CNF=cnf, parameters=parameters)
    print(o.omus())
    print(o.omusIncr())


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


class BenchmarkInfo(object):
    def __init__(self):
        self.steps = Steps()
        # self.timings = Timings()


class Steps(object):
    def __init__(self, incremental=0, greedy=0, optimal=0, sat=0, grow=0):
        self.incremental = incremental
        self.greedy = greedy
        self.optimal = optimal
        self.sat = sat
        self.grow = grow

    def __sub__(self, other):
        s = Steps()
        s.incremental = self.incremental - other.incremental
        s.greedy = self.greedy - other.greedy
        s.optimal = self.optimal - other.optimal
        s.sat = self.sat - other.sat
        s.grow = self.grow - other.grow
        return s

    def __add__(self, other):
        s = Steps() 
        s.incremental = self.incremental + other.incremental
        s.greedy = self.greedy + other.greedy
        s.optimal = self.optimal + other.optimal
        s.sat = self.sat + other.sat
        s.grow = self.grow + other.grow
        return s

    def __repr__(self):
        return f"Steps:\n------\nIncremental=\t{self.incremental}\nGreedy=\t\t{self.greedy}\nOptimal=\t{self.optimal}"


class Timings(object):
    def __init__(self):
        self.greedy = []
        self.optimal = []
        self.incremental = []
        self.sat = []
        self.growMss = []


class OMUS(object):
    def __init__(self, hard_clauses=None, soft_clauses=None, I=None, soft_weights=None, parameters={}, f=None, logging=True, reuse_mss=True,clues=None,trans=None,bij=None, modelname='MIPOptHS'):
        # checking input
        assert (f is not None) or (soft_weights is not None), "No mapping function or weights supplied."
        assert (hard_clauses is not None), "No clauses or CNF supplied."
        assert I is not None, "No interpretation provided"

        # parameters of the solver
        self.extension = parameters['extension'] if 'extension' in parameters else 'maxsat'
        self.output = parameters['output'] if 'output' in parameters else 'log.json'
        self.parameters = parameters
        self.reuse_mss = reuse_mss

        # Logging / benchmark info
        self.logging = logging
        if logging:
            self.steps = Steps()
            # self.timing = Timings()
            self.total_timings = []
            self.optimal_steps = []
            self.greedy_steps = []
            self.incremental_steps = []
            self.sat_steps = []
            self.grow_steps = []
            self.optimal_timing = []
            self.greedy_timing = []
            self.incremental_timing = []
            self.sat_timing = []
            self.grow_timing = []

        # clauses
        self.hard_clauses = [frozenset(clause) for clause in hard_clauses]
        self.soft_clauses = [frozenset(clause) for clause in soft_clauses]
        self.all_soft_clauses = [c for c in self.soft_clauses] + [frozenset({lit}) for lit in I] + [frozenset({-lit}) for lit in I]
        self.I = set(I)
        # self.I_lits = frozenset(set(abs(lit) for lit in I) | set(-abs(lit) for lit in I))
        self.soft_weights = [w for w in soft_weights]
        
        self.nSoftClauses = len(self.soft_clauses)
        self.nClauses = len(self.all_soft_clauses)
        self.nLiterals = len(I)
        # indicator variables
        self.clues = set(c for c in clues) if clues is not None else set()
        self.bij = set(b for b in bij) if bij is not None else set()
        self.trans = set(t for t in trans) if trans is not None else set()

        self.weights = [w for w in soft_weights] + [1] * 2 * self.nLiterals

        # self.nWeights = len(self.soft_weights)
        self.obj_weights = [w for w in soft_weights]
        self.obj_weights += [GRB.INFINITY for _ in range(self.nLiterals)]
        self.obj_weights += [0 for _ in range(self.nLiterals)]
        # self.obj_weights += [0] * (self.nLiterals)

        self.soft_idx = frozenset(range(self.nSoftClauses))
        self.all_soft_idx = frozenset(range(self.nClauses))
        self.softClauseIdxs = dict()
        # matching table clause to fixed id
        for idx, clause in enumerate(self.all_soft_clauses):
            self.softClauseIdxs[clause] = idx

        self.hs_sizes = []
        # MSS
        # if joint:
        # decision variable for gurobi model
        self.x = None
        self.gp_model = self.gurobiOmusConstrModel(modelname)

        self.MSSes = set()

    def checkSatNoSolver(self, f_prime=None):

        validated_clauses = [self.all_soft_clauses[i] for i in f_prime]
        validated_clauses += self.hard_clauses

        lits = set(abs(lit) for lit in frozenset.union(*validated_clauses))

        with Solver() as s:
            s.append_formula(validated_clauses, no_return=False)
            solved = s.solve()
            model = s.get_model()

        if solved:
            mapped_model = set(lit for lit in model if abs(lit) in lits)
            return mapped_model, solved
        else:
            return None, solved

    def checkSat(self, f_prime):

        satsolver = Solver(bootstrap_with=self.hard_clauses)

        if len(f_prime) == 0:
            return set(), True, satsolver
        # print(self.clauses, self.hard_clauses)
        validated_clauses = [self.all_soft_clauses[i] for i in f_prime]
        # print(f_prime, validated_clauses)
        satsolver.append_formula(validated_clauses, no_return=False)

        # set polarities
        # semi-hack for indicators:
        #  all 'softs' that are unit, add as polarity
        polarities = []
        for cl in self.soft_clauses:
            if len(cl) == 1:
                polarities.append( next(iter(cl)) )
        satsolver.set_phases(literals=polarities)

        solved = satsolver.solve()
        model = satsolver.get_model()

        if solved:
            return model, solved, satsolver
        else:
            return None, solved, satsolver

    def checkSatIncr(self, satsolver, hs, c):

        #validated_clauses = [self.all_soft_clauses[i] for i in hs] + self.hard_clauses
        # print(validated_clauses, self.clauses, self.hard_clauses)
        #lits = set(abs(lit) for lit in frozenset.union(*validated_clauses))
        clause = self.all_soft_clauses[c]

        satsolver.add_clause(clause, no_return=False)
        solved = satsolver.solve()
        model = satsolver.get_model()

        if solved:
            return model, solved, satsolver
        else:
            satsolver.delete()
            return None, solved, satsolver

    def greedyHittingSet(self, H):
        # trivial case: empty
        # print(H)
        if len(H) == 0:
            return set()

        # the hitting set
        C = set()

        # build vertical sets
        V = dict()  # for each element in H: which sets it is in

        for i, hi in enumerate(H):
            # TIAS: only take soft clauses
            h = [e for e in hi if self.obj_weights[e] < 1e50 and self.obj_weights[e] > 0]
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

        if self.logging:
            # tend = time.time()
            # self.timing.greedy.append(tend-tstart)
            self.steps.greedy += 1

        return C

    def gurobiModel(self):

        # if self.logging:
        #     tstart = time.time()
        # create gurobi model
        g_model = gp.Model('MipOptimalHittingSet')

        # model parameters
        g_model.Params.OutputFlag = 0
        g_model.Params.LogToConsole = 0
        g_model.Params.Threads = 1

        # create the variables (with weights in one go)
        x = g_model.addMVar(shape=self.nSoftClauses, vtype=GRB.BINARY, obj=self.weights, name="x")

        # set objective : min sum xi*wi
        #g_model.setObjective(sum(x[i] * self.weights[i] for i in range(self.nSoftClauses)), GRB.MINIMIZE)
        # done earlier, automatically minimisation...

        # update the model
        g_model.update()

        # if self.logging:
        #     tend = time.time()
        #     self.timing.optimal.append(tend - tstart)

        return g_model

    def addSetGurobiModel(self, gurobi_model, C):
        # variables
        x = gurobi_model.getVars()

        # add new constraint sum x[j] * hij >= 1
        # gurobi_model.addConstr(gp.quicksum(x[i] * h[i] for i in range(len(clauses))) >= 1)
        gurobi_model.addConstr(gp.quicksum(x[i] for i in C) >= 1)

    def gurobiOptimalHittingSet(self, gurobi_model):
        # if self.logging:
        #     tstart = time.time()

        # trivial case
        # if len(C) == 0:
        #     return set()

        # add new constraint sum x[j] * hij >= 1
        # self.addSetGurobiModel(gurobi_model, C)

        # solve optimization problem
        gurobi_model.optimize()

        # output hitting set
        x = gurobi_model.getVars()
        hs = set(i for i in range(self.nSoftClauses) if x[i].x == 1)

        if self.logging:
            # tend = time.time()
            # self.timing.optimal.append(tend - tstart)
            self.steps.optimal += 1

        return hs

    def gurobiOptimalHittingSetCold(self, H):
        # if self.logging:
        #     tstart = time.time()

        gurobi_model = self.gurobiModel()
        # trivial case
        if len(H) == 0:
            return []

        # add new constraint sum x[j] * hij >= 1
        for C in H:
            self.addSetGurobiModel(gurobi_model, C)

        # solve optimization problem
        gurobi_model.optimize()

        # output hitting set
        x = gurobi_model.getVars()
        hs = set(i for i in range(self.nSoftClauses) if x[i].x == 1)
        gurobi_model.dispose()

        # if self.logging:
        #     tend = time.time()
        #     self.timing.greedy.append(tend - tstart)

        return hs

    def grow(self, F_prime, model, clauses=None):
        """

            Procedure to efficiently grow the list clauses in ``F_prime``. The complement of F_prime is a correction
            set.

            :param cnf_clauses: a collection of clauses (list of literals).
            :param F_prime: hitting set : a list of clauses.
            :param extensions: list of extensions activated

            The ``extensions`` argument is a list of extensions on the default grow procedure to optimize
            the building of the minimum correction set.


            :type cnf_clauses: iterable(iterable(int))
            :type F_prime: iterable(int)
            :type extensions: iterable(int)

            Extension 1 :

                add all clauses that are true based on the assignment by the model of Fprime

            Extension 2 :

                for all variables not in variables assigned by model of Fprime
                give random values => manually check wether any clause is satisfied by this and
                add it to Fprime.

            Extension 3:

                greedy

            Extension 4:

                Maxsat
        """
        # if self.logging:
        #     tstart = time.time()
        extension = self.extension

        extensions = {
            'complement': self.defaultExtension,
            'unitprop': self.unitprop,
            'maxprop': self.maxprop,
            'greedy_param': self.greedy_param,
            'greedy_no_param': self.greedy_no_param,
            'greedy_sat': self.greedy_sat,
            # 'maxsat': self.maxsat_fprime,
            'maxsat': self.maxsat_test,
            'greedy_vertical': self.greedy_vertical,
            'greedy_hardsoft': self.greedy_hardsoft,
            'grow_singlepass': self.grow_singlepass,
            # 'satlike': SATLike
        }

        new_F_prime, new_model = extensions[extension](F_prime, model)

        if self.logging:
            # tend = time.time()
            # self.timing.growMss.append(tend - tstart)
            self.steps.grow += 1
            # print("Grow:", round(tend-tstart))

        return new_F_prime, new_model

    def defaultExtension(self, F_prime, model, clauses):
        return F_prime

    def greedy_no_param(self,  F_prime, model):
        # XXX Tias thinks it has to be over all clause (filter back alter)
        # XXX Tias: SHIT! 'grow' assumes all clauses are soft...
        # XXX so it returns a solution with a violated hard constraint
        # so F - that_thing = empty.
        # how to overcome? 
        # -> we should first grow the hard clauses (or call a SAT solver to be sure)
        # -> only then 'grow' the soft clauses as we do!
        grow_clauses = self.clauses + self.hard_clauses
        cl_true = set(F_prime)
        cl_unk = set( range(len(grow_clauses)) ) - cl_true

        lit_true = set(model)
        lit_false = set(-l for l in model)
        lit_unk = set(frozenset.union(*grow_clauses)) - lit_true - lit_false

        # init counter
        cnt = Counter({literal:0 for literal in lit_unk})
        for i in cl_unk:
            cnt.update(grow_clauses[i])

        # as long as some clauses are unassigned
        while len(cl_unk) > 0:
            # check single polarity literals
            tofix = set()
            for lit in set(abs(lit) for lit in lit_unk):
                if not lit in cnt or cnt[lit] == 0:
                    tofix.add(-lit)
                elif not -lit in cnt or cnt[-lit] == 0:
                    tofix.add(lit)

            #print(cl_unk, tofix, lit_true, lit_false)
            if len(tofix) > 0:
                #print("Tofix", tofix)
                # fix all single polarity literals
                lit_true |= tofix
                lit_unk -= tofix
                tofix_neg = set(-l for l in tofix)
                lit_false |= tofix_neg
                lit_unk -= tofix_neg
            elif len(lit_unk) > 0:
                # print(cnt, lit_unk, cl_unk)
                # choose best
                # bestlit = max(lit_unk, key=lambda i: cnt[i])
                # other definition of 'best'
                bestlit = max(lit_unk, key=lambda i: cnt[i] - cnt[-i])
                #print("Best", bestlit, cnt[bestlit], cnt[-bestlit])
                lit_true.add(bestlit)
                lit_unk.remove(bestlit)
                lit_false.add(-bestlit)
                lit_unk.remove(-bestlit)
                del cnt[bestlit]
                del cnt[-bestlit]

            # update clauses (cl_unk will be modified in place)
            for idx in list(cl_unk):
                clause = grow_clauses[idx]
                unassgn = clause - lit_false
                if len(unassgn) == 0:
                    # false, no need to check again
                    cl_unk.remove(idx)
                # print(idx, clause, cl_unk, clause.intersection(lit_false))
                elif len(clause.intersection(lit_true)) > 0:
                    # true, store and remove from counter
                    cl_unk.remove(idx)
                    cl_true.add(idx)
                    cnt = cnt - Counter(clause)
                elif len(unassgn) == 1:
                    # unit...
                    # print(lit_true, unassgn)
                    bestlit = next(iter(unassgn))
                    lit_true.add(bestlit)
                    lit_unk.remove(bestlit)
                    lit_false.add(-bestlit)
                    lit_unk.remove(-bestlit)
                    del cnt[bestlit]
                    del cnt[-bestlit]
                    cl_unk.remove(idx)
                    cl_true.add(idx)

        return cl_true, lit_true

    def greedy_param(self, F_prime, model):
        # parameters
        count_clauses = self.parameters['count_clauses']
        sorting = self.parameters['sorting']
        best_unit_literal = self.parameters['best_unit_literal']
        best_literal_counter = self.parameters['best_counter_literal']

        # preprocessing
        lit_true = set(model)
        lit_false = set(-l for l in model)
        cl_true = set(F_prime)
        lit_unk = set(frozenset.union(*self.clauses)) - lit_true - lit_false
        # Pre-processing is necessary
        if sorting != ClauseSorting.IGNORE:
            cl_unk = list(set(range(self.nSoftClauses)) - cl_true)
        else:
            cl_unk = set(range(self.nSoftClauses)) - cl_true

        # literal- clause counter
        cnt = {lit:0 for lit in lit_unk}

        for i in list(cl_unk):
            clause = self.clauses[i]
            unassign_lits = clause - lit_false - lit_true
            # clause is false, remove it
            if len(unassign_lits) == 0:
                cl_unk.remove(i)
            # validated clause
            elif len(lit_true.intersection(clause)) > 0:
                cl_true.add(i)
                cl_unk.remove(i)
            else:
                for lit in unassign_lits:
                    if count_clauses == ClauseCounting.VALIDATED:
                        # check if count number of clauses
                        cnt[lit] += 1
                    elif count_clauses == ClauseCounting.WEIGHTS:
                        # clause weight
                        cnt[lit] += self.weights[i]
                    elif count_clauses == ClauseCounting.WEIGHTED_UNASSIGNED:
                        # clause weight/# litterals assigned
                        cnt[lit] += self.weights[i]/len(unassign_lits)

        while(len(cl_unk) > 0):
            # check if clauses need reordering (only useful for unit literal)
            if isinstance(sorting, ClauseSorting):
                # clause sorting based on weights
                if sorting == ClauseSorting.WEIGHTS:
                    cl_unk.sort(reverse=True, key= lambda i: self.weights[i])
                # clause sorting based on # unassigned literals
                elif sorting == ClauseSorting.UNASSIGNED:
                    cl_unk.sort(reverse=True, key= lambda i: len(self.clauses[i] - lit_true - lit_false))
                # clause sorting based on # unassigned literals
                elif sorting == ClauseSorting.WEIGHTED_UNASSIGNED:
                    cl_unk.sort(reverse=True, key= lambda i: self.weights[i] / len(self.clauses[i] - lit_true - lit_false) if len(self.clauses[i] - lit_true - lit_false) > 0 else 0 )
                elif sorting == ClauseSorting.LITERAL_ORDERING:
                    cl_unk.sort(reverse=False, key= lambda cl_id: min(abs(lit) for lit in self.clauses[cl_id]))

            # check single polarity literals
            tofix = set()
            for lit in set(abs(lit) for lit in lit_unk):
                if not lit in cnt or cnt[lit] == 0:
                    tofix.add(-lit)
                elif not -lit in cnt or cnt[-lit] == 0:
                    tofix.add(lit)

            if len(tofix) > 0:
                # fix all single polarity literals
                lit_true |= tofix
                lit_unk -= tofix
                tofix_neg = set(-l for l in tofix)
                lit_false |= tofix_neg
                lit_unk -= tofix_neg

            # Validated all pure literals
            pure_lits = {lit for lit in lit_unk if -lit not in lit_unk}

            for lit in pure_lits:
                lit_true.add(lit)
                lit_false.add(-lit)
                lit_unk.remove(lit)
                del cnt[lit]

            if len(lit_unk) > 0:
                # 4. Literal choice
                # 4.1 Literal with highest [clause count] / [sum clause weights] / [ (sum of clause weights)/#unassigned]
                if best_literal_counter == BestLiteral.COUNT_PURE_ONLY:
                    best_lit = max(lit_unk, key=lambda i: cnt[i])
                    # print(lit_unk)
                    # print(cnt)
                    # lit_max_val = max(lit_unk, key=lambda i: cnt[i])
                    # best_lit = random.choice([lit for lit in lit_unk if cnt[lit] == cnt[lit_max_val]])
                else:
                    # 4.2 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                    best_lit = max(lit_unk, key=lambda i: cnt[i] - cnt[-i])
                    # lit_max_val = max(lit_unk, key=lambda i: cnt[i] - cnt[-i])
                    # best_lit = random.choice([lit for lit in lit_unk if (cnt[lit] - cnt[-lit]) == (cnt[lit_max_val] - cnt[-lit_max_val])])

                del cnt[best_lit]
                del cnt[-best_lit]

                lit_unk.remove(best_lit)
                lit_unk.remove(-best_lit)

                lit_true.add(best_lit)
                lit_false.add(-best_lit)

            cnt = {lit:0 for lit in lit_unk}

            unit_literals = set()

            for i in set(cl_unk):
                clause = self.clauses[i]
                unassign_lits = clause - lit_false

                # clause is false, remove it
                if len(unassign_lits) == 0:
                    cl_unk.remove(i)
                # validated clause
                elif len(lit_true.intersection(clause)) > 0:
                    cl_unk.remove(i)
                    cl_true.add(i)
                # validate unit literals
                elif len(unassign_lits) == 1 and best_unit_literal != UnitLiteral.IGNORE:
                    lit = next(iter(unassign_lits))
                    if best_unit_literal == UnitLiteral.IMMEDIATE:
                        cl_true.add(i)
                        # cl_unk
                        cl_unk.remove(i)
                        # literal
                        lit_true.add(lit)
                        lit_false.add(-lit)
                        lit_unk.remove(lit)
                        del cnt[lit]
                        lit_unk.remove(-lit)
                        del cnt[-lit]
                    else:
                        unit_literals.add(lit)
                        # for lit in unassign_lits:
                        # check if count number of clauses
                        if count_clauses == ClauseCounting.VALIDATED:
                            cnt[lit] += 1
                        # clause weight
                        elif count_clauses == ClauseCounting.WEIGHTS:
                            cnt[lit] += self.weights[i]
                        # clause weight/# litterals assigned
                        elif count_clauses == ClauseCounting.WEIGHTED_UNASSIGNED:
                            cnt[lit] += self.weights[i]/len(unassign_lits)
                else:
                    for lit in unassign_lits:
                        # check if count number of clauses
                        if count_clauses == ClauseCounting.VALIDATED:
                            cnt[lit] += 1
                        # clause weight
                        elif count_clauses == ClauseCounting.WEIGHTS:
                            cnt[lit] += self.weights[i]
                        # clause weight/# litterals assigned
                        elif count_clauses == ClauseCounting.WEIGHTED_UNASSIGNED:
                            cnt[lit] += self.weights[i]/len(unassign_lits)

            while len(unit_literals) > 0:
                # 4. Literal choice
                # 4.2 Literal with highest [clause count] / [sum clause weights] / [ (sum of clause weights)/#unassigned]
                if best_unit_literal == UnitLiteral.SINGLE_POLARITY:
                    best_lit = max(unit_literals, key=lambda i: cnt[i])
                    # lit_max_val = max(unit_literals, key=lambda i: cnt[i])
                    # best_lit = random.choice([lit for lit in unit_literals if cnt[lit] == cnt[lit_max_val]])
                    # best_lit = min(unit_literals, key=lambda i: cnt[-i])
                elif best_unit_literal == UnitLiteral.POLARITY:
                # 4.3 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                    # lit_max_val = max(unit_literals, key=lambda i: cnt[i] - cnt[-i])
                    # best_lit = random.choice([lit for lit in unit_literals if (cnt[lit] - cnt[-lit]) == (cnt[lit_max_val] - cnt[-lit_max_val])])
                    best_lit = max(unit_literals, key=lambda i: cnt[i] - cnt[-i])
                else:
                    best_lit = next(iter(unit_literals))
                # literal
                lit_true.add(best_lit)
                lit_false.add(-best_lit)
                lit_unk.remove(best_lit)
                lit_unk.remove(-best_lit)
                unit_literals.remove(best_lit)
                if -best_lit in unit_literals:
                    unit_literals.remove(-best_lit)
                del cnt[best_lit]
                del cnt[-best_lit]

        # print(lit_true)
        # print(cl_true)
        # print( set(i for i, clause in enumerate(clauses) if len(clause.intersection(lit_true)) > 0))
        # assert all(False if -lit in lit_true else True for lit in lit_true)
        cl_true = set(i for i, clause in enumerate(self.clauses) if len(clause.intersection(lit_true)) > 0)
        return cl_true, lit_true

    def greedy_sat(self, F_prime, model):
        F = set(range(self.nSoftClauses))
        C = list(F - F_prime)
        new_F_prime = set(F_prime)
        new_model = set(model)
        random.shuffle(C)
        with Solver() as s:
            for i in F_prime:
                s.add_clause(self.clauses[i])
            solved = s.solve()
            while(solved):
                c = C[0]
                del C[0]
                s.add_clause(self.clauses[c])
                solved = s.solve()
                if solved:
                    new_F_prime.add(c)
                    new_model = s.get_model()
        return new_F_prime, new_model

    def greedy_hardsoft(self, F_prime, model):
        # keep it simple:
        # repeat:
        # prop hard constraints
        # choose highest cost all_soft_clauses and set arbitrary literal to true
        print("greedy_hardsoft",F_prime,model)
        ts = time.time()

        print(self.all_soft_clauses)
        #print(self.hard_clauses)

        soft_true = set(F_prime)
        soft_unk = set( range(len(self.all_soft_clauses)) ) - soft_true
        hard_unk = set( range(len(self.hard_clauses)) )

        lit_true = set(model)
        lit_known = lit_true | set(-l for l in lit_true)
        #lit_unk = set(frozenset.union(*all_clauses)) - lit_true - lit_false

        while True:
            print(" h/s: new loop",lit_true,time.time()-ts)

            # propagate hard units
            changed = True
            while changed:
                changed = False
                for cl in list(hard_unk):
                    # true?
                    if len(self.hard_clauses[cl].intersection(lit_true)) > 0:
                        hard_unk.remove(cl)
                        continue

                    # unit?
                    unks = self.hard_clauses[cl] - lit_known
                    if len(unks) == 1:
                        # unit
                        lit = next(iter(unks))
                        print(" h/s: hard unit,",lit,self.hard_clauses[cl])
                        assert (not -lit in lit_true)
                        lit_true.add(lit)
                        lit_known.add(lit)
                        lit_known.add(-lit)
                        hard_unk.remove(cl)
                        changed = True
                    assert len(unks) > 0, "Err in greedy_hardsoft, clause false:"+str(self.hard_clauses[cl])+str(lit_true)
            print(" h/s: done hard",lit_true,time.time()-ts)

            # check if done...
            if len(soft_unk) == 0:
                print(" h/s: no softs left",lit_true,time.time()-ts)
                break

            # assign a literal in highest weight soft clause
            for cl in sorted(soft_unk, key=lambda i: self.weights[i], reverse=True):
                print(" h/s: soft",cl,self.weights[cl],lit_true,self.all_soft_clauses[cl],time.time()-ts)

                # true?
                if len(self.all_soft_clauses[cl].intersection(lit_true)) > 0:
                    print(" h/s: soft",cl,"already true")
                    soft_unk.remove(cl)
                    soft_true.add(cl)
                    continue

                # choose a literal
                unks = self.all_soft_clauses[cl] - lit_known
                if len(unks) == 0:
                    # false
                    soft_unk.remove(cl)
                else:
                    lit = next(iter(unks)) # the 'first' in the unordered set
                    print(" h/s: soft choice:",lit,cl,self.all_soft_clauses[cl])
                    assert (not -lit in lit_true)
                    lit_true.add(lit)
                    lit_known.add(lit)
                    lit_known.add(-lit)
                    soft_unk.remove(cl)
                    soft_true.add(cl)
                    break # back to hard
                    # FUCK! it could be that setting this soft is NOT
                    # possible with the current assignment...
                    # so in fact, we should check wether 'hard' is possible
                    # when setting the soft to true, and if not, to remove
                    # it again...

            # skips last hard_clause check
            #if len(soft_unk) == 0:
            #    print(" h/s: no softs left",lit_true,time.time()-ts)
            #    break

        print("OK, done",soft_true,lit_true,time.time()-ts)
        (model, sat) = self.checkSatNoSolver(soft_true)
        #assert sat, "greedy_hardsoft found non-sat soft_true"+str(soft_true)
        if not sat:
            print("Errr... non-sat!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
        return soft_true, lit_true

    def greedy_vertical(self, F_prime, model):
        print("greedy_vert",F_prime,model)
        print(self.soft_clauses)
        # soft and hard, only soft indexes really matter but all need
        # to be unit-propagated
        grow_clauses = self.soft_clauses # not the literals in (all_soft_cl) which are unit!
        all_clauses = grow_clauses + self.hard_clauses

        ts = time.time()
        cl_true = set(F_prime)
        cl_unk = set( range(len(grow_clauses)) ) - cl_true
        #print("cl_:", time.time()-ts, len(cl_unk))
        #print("cl t",cl_true)

        lit_true = set(model)
        lit_false = set(-l for l in model)
        lit_unk = set(frozenset.union(*all_clauses)) - lit_true - lit_false
        #print("lit_:", time.time()-ts, len(lit_unk))
        #print("lt t",lit_true)

        new_true = set()
        hard_unk = set( range(len(self.hard_clauses)) ) # hard clauses that are true
        def unitprop_hard():
            # TODO: add an index
            changed = True
            while changed:
                changed = False
                for cl in list(hard_unk):
                    # true?
                    if len(self.hard_clauses[cl].intersection(lit_true)) > 0:
                        hard_unk.remove(cl)
                        continue

                    # unit?
                    unks = self.hard_clauses[cl].intersection(lit_unk)
                    if len(unks) == 1:
                        # unit
                        lit = next(iter(unks))
                        print("hard unit:",lit,cl,self.hard_clauses[cl])
                        assert (not -lit in new_true) and (not -lit in lit_true)
                        new_true.add(lit)
                        hard_unk.remove(cl)
                        changed = True
        unitprop_hard()

        ts2 = time.time()
        # build vertical sets
        V = dict((e,set()) for e in lit_unk)  # for each unknown literal
        for i in list(cl_unk):
            # special case: already true
            if len(grow_clauses[i].intersection(lit_true)) > 0:
                cl_true.add(i)
                cl_unk.remove(i)
                continue

            # special case: unit literal unknown
            unks = grow_clauses[i].intersection(lit_unk)
            if len(unks) == 1:
                # unit
                lit = next(iter(unks))
                #print("pre: unit",i, unks)
                if not -lit in new_true:
                    print("unit",i,lit)
                    new_true.add(lit)
                    cl_true.add(i)
                    cl_unk.remove(i)
            else:
                for lit in unks:
                    V[lit].add(i)
        print("unk",lit_unk)
        print(V)
        # check for single polarity, add to new_true
        singpolar = [-k for (k,v) in V.items() if len(v) == 0]
        print("singpolar", singpolar)
        for k in singpolar:
            if not -k in new_true:
                new_true.add(k)
        print("new_true", new_true)
        print("Built vertical:", time.time()-ts2)

        while(len(V) > 0):
            # if new_true is empty, add best one
            if len(new_true) == 0:
                # get most frequent literal
                (lit, cover) = max(V.items(), key=lambda tpl: len(tpl[1]))
                new_true.add(lit)
                print("best new_true", new_true, len(cover))

            # prep
            # cl_newtrue = take union of new_true's in V (remove from V)
            cl_newtrue = frozenset(e for k in new_true for e in V[k])
            print("cl_newtrue", cl_newtrue)
            cl_true |= cl_newtrue
            print("cl_true", cl_true)
            # cl_newfalse = take union of -new_true's in V (remove from V)
            cl_newfalse = frozenset(e for k in new_true for e in V[-k])
            print("cl_newfalse", cl_newfalse)
            for k in new_true:
                del V[k]
                if -k in V:
                    del V[-k]

            # update known literals, reset new_true
            lit_true |= new_true
            lit_unk -= new_true
            new_false = frozenset(-k for k in new_true)
            lit_false |= new_false
            lit_unk -= new_false
            new_true = set()
            #print(V, lit_true, lit_unk)
            unitprop_hard()

            for cl in sorted(cl_newfalse - cl_newtrue, reverse=True):
                # check for unit, add to new_true
                unks = grow_clauses[cl].intersection(lit_unk)
                if len(unks) == 1:
                    # unit
                    lit = next(iter(unks))
                    print("unit:",lit)
                    if not -lit in new_true:
                        new_true.add(lit)
            # update vertical views (remove true clauses)
            for e in list(V):
                V[e] -= cl_newtrue
                if len(V[e]) == 0 and not e in new_true:
                    # single polarity
                    print("single polar:",-e)
                    new_true.add(-e)
            unitprop_hard()
            #print(V, lit_true, lit_unk)
        #print("greedy_tias, t: ", time.time() - ts)
        #print("remaining unks:", cl_unk)
        for i in range(len(self.soft_clauses),len(self.all_soft_clauses)):
            # the literal clauses
            #print("in?",self.all_soft_clauses[i], lit_true)
            if len(self.all_soft_clauses[i] & lit_true) > 0:
                cl_true.add(i)
        return cl_true, lit_true

    def grow_singlepass(self, F_prime, model):
        model = frozenset(model)
        # filter out -I's that are in model
        I_unassgn = set(-lit for lit in self.I)
        I_unassgn -= model
        # flip remaining and filter out I's that are in model
        I_unassgn = set(-lit for lit in I_unassgn)
        I_unassgn -= model
        #print("I_unassgn",I_unassgn)
        # add to the model, then check which softs are satisfied
        model |= I_unassgn

        cl_true = F_prime
        cl_false = set() # this will be the F-C, the 'set-to-hit'!
        cl_unk = set()
        for (i,clause) in enumerate(self.all_soft_clauses):
            if i in cl_true:
                continue #skip
            #print(clause, model)
            if len(clause & model) > 0:
                # true
                #print("true")
                cl_true.add(i)
                continue
            negclause = set(-l for l in clause)
            if len(negclause - model) == 0:
                #print("false",clause,model)
                # false
                cl_false.add(i)
                continue
            #print("unk")
            cl_unk.add(i)
        #print("T",cl_true)
        #print("F",cl_false)
        #C = cl_false
        #print("U",cl_unk)
        return (cl_true, model)

    def maxprop(self, F_prime, model):
        # parameters
        # best_unit_literal = self.parameters['best_unit_literal']
        best_literal_counter = self.parameters['best_counter_literal']

        # init counter
        all_literals = frozenset.union(*self.clauses)
        t_F_prime, t_model = self.unitprop(F_prime, model)
        lit_true = set(t_model)
        lit_false = set(-l for l in t_model)

        # alternative, over all literals
        remaining_literals = all_literals - lit_true - lit_false
        conflict_free_literals = remaining_literals - set(-l for l in remaining_literals)

        cnt = Counter({literal:0 for literal in remaining_literals})
        for i,clause in enumerate(self.clauses):
            if i not in t_F_prime:
                lit_intersect_cl = remaining_literals.intersection(clause)
                cnt.update(lit_intersect_cl)

        while(len(conflict_free_literals) > 0):

            if best_literal_counter == BestLiteral.COUNT_PURE_ONLY:
                best_lit = max(conflict_free_literals, key=lambda i: cnt[i])
            else:
                # 4.2 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                best_lit = max(conflict_free_literals, key=lambda i: cnt[i] - cnt[-i])

            lit_true.add(best_lit)
            lit_false.add(-best_lit)

            t_F_prime, t_model = self.unitprop(t_F_prime, lit_true)

            lit_true = set(t_model)
            lit_false = set(-l for l in t_model)

            remaining_literals = all_literals - lit_true - lit_false
            conflict_free_literals = remaining_literals - set(-l for l in remaining_literals if -l in remaining_literals)

            cnt = Counter({literal:0 for literal in conflict_free_literals})
            for i, clause in enumerate(self.clauses):
                if i not in t_F_prime:
                    lit_intersect_cl = conflict_free_literals.intersection(clause)
                    cnt.update(lit_intersect_cl)

        conflictual_literals = set(remaining_literals)

        cnt = Counter({literal:0 for literal in conflictual_literals})
        for i,clause in enumerate(self.clauses):
            if i not in t_F_prime:
                lit_intersect_cl = conflictual_literals.intersection(clause)
                cnt.update(lit_intersect_cl)

        assert all([True if -l in conflictual_literals else False for l in conflictual_literals])

        # propagate all remaining literals
        while len(conflictual_literals) > 0:
            if best_literal_counter == BestLiteral.COUNT_PURE_ONLY:
                best_lit = max(conflictual_literals, key=lambda i: cnt[i])
            else:
                # 4.2 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                best_lit = max(conflictual_literals, key=lambda i: cnt[i] - cnt[-i])

            conflictual_literals.remove(best_lit)
            # because the unit prop created a conflict-free one, we must check
            if -best_lit in conflictual_literals:
                conflictual_literals.remove(-best_lit)

            lit_true.add(best_lit)
            lit_false.add(-best_lit)

            # unit propagate new literal
            t_F_prime, t_model = self.unitprop(t_F_prime, lit_true)

            lit_true = set(t_model)
            lit_false = set(-l for l in t_model)

            # code was probably not finished because the latter was missing
            remaining_literals = all_literals - lit_true - lit_false
            conflictual_literals = set(remaining_literals)

            cnt = Counter({literal:0 for literal in conflictual_literals})
            for i,clause in enumerate(self.clauses):
                if i not in t_F_prime:
                    lit_intersect_cl = conflictual_literals.intersection(clause)
                    cnt.update(lit_intersect_cl)

        assert all([True if -l not in lit_true else False for l in lit_true])

        return t_F_prime, lit_true

    def maxsat_fprime_n(self, F_prime, n):
        t_F_prime = set(F_prime)

        wcnf = WCNF()
        wcnf.extend(self.hard_clauses)
        for i, clause in enumerate(self.clauses):
            if i in F_prime:
                wcnf.append(list(clause))
            else:
                wcnf.append(list(clause), weight=self.weights[i])

        list_msses = []
        with RC2(wcnf) as rc2:
            for id, model in enumerate(rc2.enumerate()):
                if id == n:
                    break

                t_F_prime = set(F_prime)
                t_model = set(model)
                for i, clause in enumerate(self.clauses):
                    if i not in t_F_prime and len(clause.intersection(t_model)) > 0:
                        t_F_prime.add(i)

                list_msses.append((frozenset(t_F_prime), frozenset(t_model)))

        return list_msses

    def maxsat_fprime(self, F_prime, model):
        # print()
        t_F_prime = set(F_prime)

        wcnf = WCNF()
        wcnf.extend(self.hard_clauses)
        for i, clause in enumerate(self.clauses):
        # for i, clause in enumerate(self.all_soft_clauses):
            if i in F_prime:
                wcnf.append(list(clause))
            else:
                wcnf.append(list(clause), weight=self.weights[i])

        with RC2(wcnf) as rc2:
            t_model = rc2.compute()

        for i, clause in enumerate(self.clauses):
            if i not in t_F_prime and len(clause.intersection(t_model)) > 0:
                t_F_prime.add(i)

        return t_F_prime, t_model

    def unitprop(self, F_prime, model):
        """`Extension1' unit propagate the model to find all clauses hit by the current
        assignment of F_prime.

        Arguments:
            clauses {iterable(iterable(int))} -- collection of clauses (sets of literals)
            F_prime {iterable(int)} -- Hitting set, optimal set of clauses hitting H
            model {iterable(int)} -- model of clauses in F_prime

        Returns:
            iterable(int), iterable(int) -- Grown hitting set, new model of hitting set
        """
        # parameters
        best_unit_literal = self.parameters['best_unit_literal'] if 'best_unit_literal' in parameters else UnitLiteral.IMMEDIATE

        new_F_prime = set(F_prime)
        # precompute both
        lit_true = set(model)
        lit_false = set(-l for l in model)

        clause_added = True
        while(clause_added):
            clause_added = False
            t_F_prime = set(new_F_prime)
            for i, clause in enumerate(self.clauses):
                if i in new_F_prime:
                    continue # already in F_prime

                # Similar alternative:
                if len(clause.intersection(lit_true)) > 0:
                    # a true literal, clause is true
                    t_F_prime.add(i)
                    clause_added = True

                else:
                    unassigned = clause - lit_false
                    if len(unassigned) == 1 and best_unit_literal == UnitLiteral.IMMEDIATE:
                        t_F_prime.add(i)
                        # add literal to the model
                        lit = next(iter(unassigned))
                        lit_true.add(lit)
                        lit_false.add(-lit)
                        clause_added = True
            if len(t_F_prime) > len(new_F_prime):
                new_F_prime = t_F_prime
                # check for unit propagation

        assert all([True if -l not in lit_true else False for l in lit_true]), f"Conflicting literals {lit_true}"
        return new_F_prime, lit_true

    def gurobiOmusConstrModel(self, modelname):
        # create gurobi model
        self.g_model = gp.Model(modelname)

        # model parameters
        self.g_model.Params.OutputFlag = 0
        self.g_model.Params.LogToConsole = 0
        self.g_model.Params.Threads = 8

        # create the variables (with weights in one go)
        x = self.g_model.addMVar(shape=self.nClauses, vtype=GRB.BINARY, obj=self.obj_weights, name="x")
        # self.x = self.g_model.addMVar(shape=self.nClauses, vtype=GRB.BINARY, name="x")

        # # |B| = # bijectivity + #transitivity constraints
        # # W = {0, 1} if |S| > 1 then 1 else 0
        # # Y = {0, 1} if nClues = 0 then 1 else 0
        # # THeta = W * Y:
        # #       if nclues = 0 and nConstraints > 1: Y =1 and W = 1 => 1
        # #       rest 0
        # W = self.g_model.addMVar(shape=1, vtype=GRB.BINARY, name="W")
        # Y = self.g_model.addMVar(shape=1, vtype=GRB.BINARY, name="Y")
        # THETA = self.g_model.addMVar(shape=1, vtype=GRB.BINARY, name="THETA")

        # # 
        # self.g_model.addConstr(THETA <= W)
        # self.g_model.addConstr(THETA <= Y)
        # self.g_model.addConstr(THETA >= W + Y - 1)

        # B = len(self.bij | self.trans)
        # nClues = len(self.clues)
        # implicit_constraints = self.bij | self.trans
        # n_all_constr = len(self.bij) + len(self.trans) + len(self.clues)
        # print(n_all_constr)
        # print(nClues)
        # print(len(self.bij))
        # print(len(self.trans))

        # # obj_w = [0 for i in range(0, n_all_constr)] + [self.obj_weights[i] for i in range(n_all_constr, self.nClauses)]
        # # obj_expr = gp.LinExpr()
        # # obj_expr.addTerms(obj_w, x )
        # # obj_expr.addTerms(sum(x[i] for i in self.clues) * 100)
        # # obj_expr.addTerms(100, THETA)
        # obj_expr = 100 * THETA + self.x[list(self.clues)].sum() * 100
        # for i in range(n_all_constr, self.nClauses):
        #     obj_expr += self.x[i] * self.obj_weights[i]
        # # obj_expr = x[range(n_all_constr, self.nClauses)].sum() * [self.obj_weights[i] for i in range(n_all_constr, self.nClauses)]
        # self.g_model.setObjective(obj_expr, GRB.MINIMIZE)
        # # print(implicit_constraints)
        # print(self.nClauses)

        # self.g_model.addConstr(self.x[list(implicit_constraints)].sum() - 1 >= W * B)
        # self.g_model.addConstr(self.x[list(self.clues)].sum()  <= nClues * (1 - Y))
        # # self.g_model.addConstr(gp.quicksum(x[i] for i in implicit_constraints) - 1 >= W * B)
        # # self.g_model.addConstr(gp.quicksum(x[i] for i in self.clues) <= nClues * (1 - Y))
        # # self.g_model.setObjective(
        # #     100 * THETA + gp.quicksum(x[i]*self.obj_weights[i] for i in range(n_all_constr, self.nClauses))
        # #     , GRB.MINIMIZE)
        # exactly one of the -literals
        vals = range(self.nSoftClauses + self.nLiterals, self.nClauses)

        # exactly one of the -literals...
        self.g_model.addConstr(x[vals].sum() == 1)

        # update the model
        self.g_model.update()

    def addSetGurobiOmusConstr(self, C):
        # variables
        # x = self.g_model.getVarByName("x")
        # print(self.g_model.getVars())
        # print(x)
        x = self.g_model.getVars()
        # add new constraint sum x[j] * hij >= 1
        self.g_model.addConstr(gp.quicksum(x[i] for i in C) >= 1)
        # self.g_model.addConstr(self.x[list(C)].sum()  >= 1)

    def gurobiOmusConstrHS(self):
        # solve optimization problem
        self.g_model.optimize()

        # output hitting set
        x = self.g_model.getVars()
        # x = self.g_model.getVarByName("x")

        hs = set(i for i in range(self.nClauses) if x[i].x == 1)

        return hs

    def updateObjWeightsInterpret(self, I):
        # for i in range(self.nSoftClauses, self.nSoftClauses + self.nLiterals):
        #     self.obj_weights[i] = GRB.INFINITY

        # for i in range(self.nSoftClauses + self.nLiterals, self.nClauses):
        #     self.obj_weights[i] = 0

        # B = len(self.bij | self.trans)
        # nClues = len(self.clues)
        # implicit_constraints = self.bij | self.trans
        # n_all_constr = len(self.bij) + len(self.trans) + len(self.clues)
        x = self.g_model.getVars()

        for i in I:
            i_idx = self.softClauseIdxs[frozenset({i})]
            self.obj_weights[i_idx] = 1

            not_i_idx = self.softClauseIdxs[frozenset({-i})]
            self.obj_weights[not_i_idx] = GRB.INFINITY

        # x = self.g_model.getVarByName("x")
        # W = self.g_model.getVarByName("W")
        # Y = self.g_model.getVarByName("Y")
        # THETA = self.g_model.getVarByName("THETA")

        self.g_model.setObjective(gp.quicksum(x[i] * self.obj_weights[i] for i in range(self.nClauses)), GRB.MINIMIZE)
        # self.g_model.update()
        # obj_expr = gp.LinExpr(gp.quicksum(x[i] for i in self.clues) * 100)
        # obj_expr.addTerms(100, THETA)
        # obj_w = [0 for i in range(0, n_all_constr)] + [self.obj_weights[i] for i in range(n_all_constr, self.nClauses)]
        # obj_expr.addTerms(obj_w, x )
        # # obj_expr = 100 * THETA + gp.quicksum(x[i] for i in self.clues) * 100 + gp.quicksum(x[i]*self.obj_weights[i] for i in range(n_all_constr, self.nClauses))
        # self.g_model.setObjective(obj_expr, GRB.MINIMIZE)


    def maxsat_test(self, hs_in, model):
        hs = set(hs_in) # take copy!!
        mss_model = set(model)

        wcnf = WCNF()
        wcnf.extend(self.hard_clauses)

        for i in hs:
            clause = self.all_soft_clauses[i]
            wcnf.append(list(clause))

        for i , clause in enumerate(self.soft_clauses):
            if i not in hs:
                # wcnf.append(list(clause))
                wcnf.append(list(clause), weight=self.weights[i])

        with RC2(wcnf) as rc2:
            t_model = rc2.compute()
            if t_model is None:
                return hs, model

            for i, clause in enumerate(self.all_soft_clauses):
                if i not in hs and len(clause.intersection(t_model)) > 0:
                    hs.add(i)

            return hs, t_model

    def deleteModel(self):
        self.g_model.dispose()
        del self.g_model

    def omusConstr(self, do_incremental=False, greedy=False, timeout=None):

        nopt = 0
        nincr = 0
        ngreedy = 0
        hs = None

        F = frozenset(range(self.nClauses))

        H, C = [], []
        hs = None
        t_start = time.time()
        h_counter = Counter()
        # print(self.obj_weights)
        satsolver = None
        mode = MODE_OPT

        do_greedy = do_incremental and greedy

        while(True):
            # print(hs)
            if timeout is not None and time.time() - t_start > timeout:
                self.optimal_steps.append(nopt)
                self.greedy_steps.append(ngreedy)
                self.incremental_steps.append(nincr)
                self.hs_sizes.append(len(H))
                return None, None
            while(do_incremental):
                if timeout is not None and time.time() - t_start > timeout:
                    self.optimal_steps.append(nopt)
                    self.greedy_steps.append(ngreedy)
                    self.incremental_steps.append(nincr)
                    self.hs_sizes.append(len(H))
                    return None, None
                if mode == MODE_INCR:
                    # add sets-to-hit incrementally until unsat then continue with optimal method
                    # given sets to hit 'CC', a hitting set thereof 'hs' and a new set-to-hit added 'C'
                    # then hs + any element of 'C' is a valid hitting set of CC + C
                    # choose element from C with smallest weight
                    # TODO: Can we remove some clauses from the sets to hit in H?
                    C_softie = [e for e in C if self.obj_weights[e] < 1e50 and self.obj_weights[e] > 0]
                    if len(C_softie) == 0:
                        mode = MODE_OPT
                        satsolver.delete()
                        break
                    ## find all elements with smallest weight
                    c = min(C_softie, key=lambda i: self.obj_weights[i])
                    # m = [ci for ci in C_softie if self.obj_weights[ci] == self.obj_weights[c]]
                    # ## choose clause with smallest weight appearing most in H
                    # c_best = max(m, key=lambda ci: h_counter[ci])
                    hs.add(c)
                    nincr +=1
                    # hs.add(c_best)
                    # print("incr choose",c,self.obj_weights[c])
                elif mode == MODE_GREEDY and do_greedy:
                   # ----- Greedy compute hitting set
                   hs = self.greedyHittingSet(H)
                   ngreedy +=1
                elif mode == MODE_OPT:
                    break

                # ----- check satisfiability of hitting set
                if mode == MODE_INCR:
                    (model, sat, satsolver) = self.checkSatIncr(satsolver=satsolver, hs=hs, c=c)
                    #(model, sat, satsolver) = self.checkSat(hs)
                elif mode == MODE_GREEDY  and do_greedy:
                  (model, sat, satsolver) = self.checkSat(hs)

                # print(hs, sat)
                if not sat:
                    # incremental hs is unsat, switch to optimal method
                    hs = None
                    if mode == MODE_INCR:
                        satsolver.delete()
                        if do_greedy:
                            mode = MODE_GREEDY
                        #    satsolver.delete()
                            continue
                        else:
                            mode = MODE_OPT
                            break
                    elif mode == MODE_GREEDY:
                        mode = MODE_OPT
                        satsolver.delete()
                        break
                    # break # skip grow
                # if (best_cost is not None and best_cost <= my_cost):
                # ------ Grow

                t_grow = time.time()
                MSS, MSS_model = self.grow(hs, model)
                # print("Time grow=:", round(time.time() - t_grow, 3))

                C = F - MSS
                h_counter.update(list(C))
                self.addSetGurobiOmusConstr(C)
                H.append(C)
                mode = MODE_INCR

            #     mode = MODE_INCR
            t_grow = time.time()
            hs = self.gurobiOmusConstrHS()
            # print("got hs\t\t\t\t",hs,round(time.time() - t_grow, 3))
            nopt +=1
            # ------ Sat check
            t_grow = time.time()
            (model, sat, satsolver) = self.checkSat(hs)
            # print("Time sat=:", round(time.time() - t_grow, 3))

            if not sat:
                self.optimal_steps.append(nopt)
                self.greedy_steps.append(ngreedy)
                self.incremental_steps.append(nincr)
                self.hs_sizes.append(len(H))
                satsolver.delete()
                # print("hs-omus=", hs)
                # print("hs-omus",hs)
                # print("OMUS=", [self.all_soft_clauses[idx] for idx in hs])
                return hs, [self.all_soft_clauses[idx] for idx in hs]

            # ------ Grow
            # print()
            t_grow = time.time()
            MSS, MSS_model = self.grow(hs, model)
            # print("Time grow=:", round(time.time() - t_grow, 3))
            C = F - MSS

            self.addSetGurobiOmusConstr(C)
            assert len(C) > 0, f"Opt: C empty\nhs={hs}\nmodel={model}"

            if do_incremental: 
                mode = MODE_INCR
            else:
                satsolver.delete()

    def omusIncr(self, I_cnf, explained_literal, add_weights=None, best_cost=None, hs_limit=None, postponed_omus=True, timeout=1000):
        # Benchmark info
        t_start_omus = time.time()
        if self.logging:
            n_msses = len(self.MSSes)
            n_greedy = self.steps.greedy
            n_sat = self.steps.sat
            n_grow = self.steps.grow
            n_optimal = self.steps.optimal
            n_incremental = self.steps.incremental

        # Build clauses and additional weights
        self.clauses = self.soft_clauses + I_cnf + [frozenset({-explained_literal})]
        self.nSoftClauses = len(self.clauses)

        if add_weights is not None:
            self.weights = self.soft_weights + add_weights
        elif self.f is not None:
            self.weights = self.soft_weights + [f(clause) for clause in I_cnf + [frozenset({-explained_literal})]]

        # ---- getting more steps when reusing the models
        self.nWeights = len(self.weights)

        assert self.nSoftClauses == self.nWeights, "Weights must be the same"
        F = frozenset(range(self.nSoftClauses))

        self.hs_sizes = []
        H, C = [], []
        h_counter = Counter()

        gurobi_model = self.gurobiModel()
        satsolver, sat, hs = None, None, None
        my_cost = None

        # WARNING: self.MSSes is a tuple (mss, model)
        # XXX: the models are HUGE! can save memory if only on grid vars?
        if self.reuse_mss:
            added_MSSes = []
            # map global 'softClauseIdx' to local 'pos'
            F_idxs = {self.softClauseIdxs[clause]: pos for pos, clause in enumerate(self.clauses)}

            for mss_idxs, MSS_model in self.MSSes:

                # part of fullMSS
                if mss_idxs.issubset(self.fullMss):
                    # print("MSS is subset")
                    continue

                # if literal not in the model then we can skip it
                if explained_literal not in MSS_model and -explained_literal not in MSS_model:
                    continue

                # get local pos from global idx
                mss = set(F_idxs[mss_idx] for mss_idx in mss_idxs&F_idxs.keys())
                # print(mss, )

                if any(mss.issubset(MSS) for MSS in added_MSSes):
                    continue

                # grow model over hard clauses first, must be satisfied
                # Timing: grow is rather slow
                # XXX Model if literal inside then add it to the MSS and C = F-MSS
                # XXX remove grow
                # MSS, model = self.grow(mss, MSS_model)
                C = F - mss

                if C not in H:
                    h_counter.update(list(C))
                    H.append(C)
                    added_MSSes.append(mss&F)
                    self.addSetGurobiModel(gurobi_model, C)

        mode = MODE_OPT
        #print("\n")
        while(True):
            if (time.time() -t_start_omus) > timeout:
                gurobi_model.dispose()
                satsolver.delete()
                return None, my_cost
            # print(f"\t\topt steps = {self.steps.optimal - n_optimal}\t greedy steps = {self.steps.greedy - n_greedy}\t incremental steps = {self.steps.incremental - n_incremental}")
            while(True and postponed_omus):
                if (time.time() -t_start_omus) > timeout:
                    gurobi_model.dispose()
                    satsolver.delete()
                    return None, my_cost
                # print("Starting with optimal!")
                # print(f"\t\topt steps = {self.steps.optimal - n_optimal}\t greedy steps = {self.steps.greedy - n_greedy}\t incremental steps = {self.steps.incremental - n_incremental}")
                if mode == MODE_INCR:

                    # add sets-to-hit incrementally until unsat then continue with optimal method
                    # given sets to hit 'CC', a hitting set thereof 'hs' and a new set-to-hit added 'C'
                    # then hs + any element of 'C' is a valid hitting set of CC + C
                    # choose element from C with smallest weight
                    c = min(C, key=lambda i: self.weights[i])
                    # find all elements with smallest weight
                    m = [ci for ci in C if self.weights[ci] == self.weights[c]]
                    # choose clause with smallest weight appearing most in H
                    c_best = max(m, key=lambda ci: h_counter[ci])
                    hs.add(c_best)
                    # self.hs_sizes.append(len(hs))
                elif mode == MODE_GREEDY:
                    # ----- Greedy compute hitting set
                    hs = self.greedyHittingSet(H)
                    # self.hs_sizes.append(len(hs))
                elif mode == MODE_OPT:
                    break
                # ----- check satisfiability of hitting set
                if mode == MODE_INCR:
                    (model, sat, satsolver) = self.checkSatIncr(satsolver=satsolver, hs=hs, c=c_best)
                elif mode == MODE_GREEDY:
                    (model, sat, satsolver) = self.checkSat(hs)

                E_i = [ci for ci in hs if self.clauses[ci] in I_cnf]

                # constraint used ('and not ci in E_i': dont repeat unit clauses)
                S_i = [ci for ci in hs if self.clauses[ci] in self.soft_clauses]
                # S_i = [ci for ci in hs if self.clauses[ci] in self.soft_clauses and self.clauses[ci] not in I_cnf]

                my_cost = self.cost((E_i, S_i))
                # print(my_cost, "vs ", best_cost)
                # if(len())

                if not sat or (best_cost is not None and best_cost <= my_cost):
                    # incremental hs is unsat, switch to optimal method
                    hs = None
                    if mode == MODE_INCR:
                        mode = MODE_GREEDY
                        satsolver.delete()
                        continue
                    elif mode == MODE_GREEDY:
                        mode = MODE_OPT
                        break
                    # break # skip grow
                # if (best_cost is not None and best_cost <= my_cost):
                # ------ Grow
                if True or self.extension == 'maxsat':
                    # grow model over hard clauses first, must be satisfied
                    # MSS, MSS_model = self.grow(hs, model)
                    MSS, MSS_model = self.maxsat_fprime(hs, model)
                else:
                    # grow model over hard clauses first, must be satisfied
                    MSS, MSS_model = self.grow(hs, model, self.hard_clauses)
                    # print("hard grow:",len(MSS),model,"->",MSS_model)
                    # grow model over as many as possible soft clauses next 
                    MSS, MSS_model = self.grow(hs, MSS_model, self.clauses)
                    # print("soft grow:",MSS,MSS_model)

                C = F - MSS
                assert len(C) > 0, f"Greedy: hs={hs}, model={model}"

                # Store the MSSes
                if self.reuse_mss:
                    mssIdxs = frozenset(self.softClauseIdxs[self.clauses[id]] for id in MSS&F)
                    # mssIdxs = frozenset(self.softClauseIdxs[self.clauses[id]] for id in MSS)
                    # self.MSSes = self.MSSes.filter()
                    storeMss= not mssIdxs.issubset(self.fullMss) and \
                              not any(True if mssIdxs.issubset(m[0]) else False for m in self.MSSes)
                    if(storeMss):
                        self.MSSes.add((mssIdxs, frozenset(MSS_model)))

                h_counter.update(list(C))
                self.addSetGurobiModel(gurobi_model, C)
                H.append(C)

                if hs_limit is not None and len(H) > hs_limit:
                    gurobi_model.dispose()
                    satsolver.delete()
                    return C, my_cost

                # Sat => Back to incremental mode 
                mode = MODE_INCR

            # ----- Compute Optimal Hitting Set
            hs = self.gurobiOptimalHittingSet(gurobi_model)
            # print(hs)
            # self.hs_sizes.append(len(hs))

            # check cost, return premptively if worse than best
            E_i = [ci for ci in hs if self.clauses[ci] in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in hs if self.clauses[ci] in self.soft_clauses]

            # opti = optimalPropagate(hard_clauses + E_i + S_i, I)
            my_cost = self.cost((E_i, S_i))
            # print(my_cost, "vs", best_cost)
            if best_cost is not None and my_cost >= best_cost:
                gurobi_model.dispose()
                satsolver.delete()
                return None, my_cost

            # ------ Sat check
            (model, sat, satsolver) = self.checkSat(hs)

            if not sat:
                #
                gurobi_model.dispose()
                satsolver.delete()

                # Benchmark info
                if self.reuse_mss:
                    self.MSS_sizes.append(len(self.MSSes) - n_msses)
                if self.logging:
                    exec_time = time.time() - t_start_omus
                    self.total_timings.append(exec_time)
                    self.optimal_steps.append(self.steps.optimal - n_optimal)
                    self.greedy_steps.append(self.steps.greedy - n_greedy)
                    self.incremental_steps.append(self.steps.incremental - n_incremental)
                    self.sat_steps.append(self.steps.sat - n_sat)
                    self.grow_steps.append(self.steps.grow - n_grow)
                #print("\n")
                return hs, [self.clauses[idx] for idx in hs]

            # ------ Grow
            if self.extension == 'maxsat':
                # grow model over hard clauses first, must be satisfied
                # MSS, MSS_model = self.grow(hs, model, self.hard_clauses)
                MSS, MSS_model = self.grow(hs, model)
            else:
                # grow model over hard clauses first, must be satisfied
                MSS, MSS_model = self.grow(hs, model, self.hard_clauses)
                # print("hard grow:",len(MSS),model,"->",MSS_model)
                # grow model over as many as possible soft clauses next 
                MSS, MSS_model = self.grow(hs, MSS_model, self.clauses)

            if self.reuse_mss:
                mssIdxs = frozenset(self.softClauseIdxs[self.clauses[id]] for id in MSS&F)
                # mssIdxs = frozenset(self.softClauseIdxs[self.clauses[id]] for id in MSS)
                storeMss= not mssIdxs.issubset(self.fullMss) and \
                            not any(True if mssIdxs < m[0] else False for m in self.MSSes)
                if(storeMss):
                    self.MSSes.add((mssIdxs, frozenset(MSS_model)))

            C = F - MSS
            self.addSetGurobiModel(gurobi_model, C)
            assert len(C) > 0, f"Opt: C empty\nhs={hs}\nmodel={model}"

            h_counter.update(list(C))
            H.append(C)
            mode = MODE_INCR

            if hs_limit is not None and len(H) > hs_limit:
                gurobi_model.dispose()
                satsolver.delete()
                return C, my_cost

    def omus(self, add_clauses, add_weights=None):
        # ---------- build clauses and additional weights
        self.clauses = self.base_clauses + add_clauses
        self.nSoftClauses = len(self.clauses)

        if add_weights is not None:
            self.weights = self.base_weights + add_weights
        elif self.f is not None:
            self.weights = self.base_weights + [f(clause) for clause in add_clauses]
        else:
            self.weights = self.base_weights + [len(clause) for clause in add_clauses]

        assert len(self.clauses) == len(self.weights)

        # benchmark variables
        F = frozenset(range(self.nSoftClauses))
        gurobi_model = self.gurobiModel()
        H = []
        C = [] # last added 'set-to-hit'
        hs = None # last computed hitting set
        # t_start_omus = time.time()
        while(True):

            hs = self.gurobiOptimalHittingSet(gurobi_model, C)
            # print(hs)
            model, sat = self.checkSatNoSolver(hs)

            # if not sat or steps > max_steps_main:
            if not sat:
                gurobi_model.dispose()
                satsolver.delete()
                # return hs
                return hs, [set(self.clauses[idx]) for idx in hs]

            MSS, _ = self.grow(hs, model)
            C = F - MSS
            # print(MSS, C)

            self.addSetGurobiModel(gurobi_model, C)
            H.append(C)

    def export_results(self, outputDir, outputFile):
        # import pathlib
        from pathlib import Path
        p = Path(outputDir)
        if not p.exists():
            p.mkdir()

        results = dict()

        # global 
        results['execution_times'] = self.total_timings
        results['MSS_sizes'] = self.MSS_sizes
        results['MSSes'] = [ (list(MSS), list(model)) for MSS, model in self.MSSes]
        results['nSoftClauses'] = self.nSoftClauses
        results['nWeights'] = self.nWeights

        # n steps for every OMUS call
        results['optimal_steps'] = self.optimal_steps
        results['greedy_steps'] = self.greedy_steps
        results['incremental_steps'] = self.incremental_steps
        results['sat_steps'] = self.sat_steps
        results['grow_steps'] = self.grow_steps

<<<<<<< HEAD
class Steps(object):
    def __init__(self, incremental=0, greedy=0, optimal=0, sat=0, grow=0):
        self.incremental = incremental
        self.greedy = greedy
        self.optimal = optimal
        self.sat = sat
        self.grow = grow

    def __sub__(self, other):
        s = Steps()
        s.incremental = self.incremental - other.incremental
        s.greedy = self.greedy - other.greedy
        s.optimal = self.optimal - other.optimal
        s.sat = self.sat - other.sat
        s.grow = self.grow - other.grow
        return s

    def __add__(self, other):
        s = Steps()
        s.incremental = self.incremental + other.incremental
        s.greedy = self.greedy + other.greedy
        s.optimal = self.optimal + other.optimal
        s.sat = self.sat + other.sat
        s.grow = self.grow + other.grow
        return s
=======
        # Individual timings of the calls
        # results['timing.optimal'] = self.timing.optimal
        # results['timing.greedy'] = self.timing.greedy
        # results['timing.sat'] = self.timing.sat
        # results['timing.incremental'] = self.timing.incremental
        # results['timing.growMss'] = self.timing.growMss

        with open(outputDir + outputFile, 'w') as file:
            file.write(json.dumps(results)) # use `json.loads` to do the reverse

>>>>>>> omus-explain-lb

    def basecost(self, constraints):
        # nClues = len(constraints.intersection(clues))
        if self.clues is not None:
            nClues = sum([1 if id in self.clues else 0 for id in constraints])
        else:
            nClues = 0
        nOthers = len(constraints) - nClues
        # print("constraints = ", constraints)
        if nClues == 0 and nOthers == 1:
            return 0
        elif nClues == 0 and nOthers > 1:
            return 20
        else:
            return nClues * 20


    def cost(self, explanation):
        facts, constraints = explanation
        return self.basecost(constraints) + len(facts) + len(constraints)

<<<<<<< HEAD
class OMUS(object):
    def __init__(self, hard_clauses=None, soft_clauses=None, I=None, bv=None, soft_weights=None, parameters={}, f=lambda x: len(x), logging=True, reuse_mss=True):
=======


class OMUSBase(object):
    def __init__(self, hard_clauses=None, soft_clauses=None, I=None, bv=None, soft_weights=None, parameters={}, f=lambda x: len(x), logging=True, reuse_mss=True,clues=None,trans=None,bij=None):
>>>>>>> omus-explain-lb
        # checking input
        assert (f is not None) or (soft_weights is not None), "No mapping function or weights supplied."
        assert (hard_clauses is not None), "No clauses or CNF supplied."
        assert I is not None, "No interpretation provided"

        # parameters of the solver
        self.extension = parameters['extension'] if 'extension' in parameters else 'maxsat'
        self.output = parameters['output'] if 'output' in parameters else 'log.json'
        self.parameters = parameters

        # Logging / benchmark info
        self.logging = logging
        if logging:
            self.steps = Steps()
            # self.timing = Timings()
            self.total_timings = []
            self.optimal_steps = []
            self.greedy_steps = []
            self.incremental_steps = []
            self.sat_steps = []
            self.grow_steps = []
<<<<<<< HEAD
=======
            self.optimal_timing = []
            self.greedy_timing = []
            self.incremental_timing = []
            self.sat_timing = []
            self.grow_timing = []
>>>>>>> omus-explain-lb

        # clauses
        self.hard_clauses = [frozenset(clause) for clause in hard_clauses]
        self.soft_clauses = [frozenset(clause) for clause in soft_clauses]
        self.clauses = self.soft_clauses  # soft + omus 'added' ones
        self.nSoftClauses = len(self.soft_clauses)
        self.fullMss = frozenset(i for i in range(self.nSoftClauses + len(I)))
        self.I_lits = frozenset(set(abs(lit) for lit in I) | set(-abs(lit) for lit in I))
        self.clues = clues
        self.trans = trans
        self.bij = bij
        self.hs_sizes = []

        # indicator variables

        # weights
        self.f = f
        if f is not None:
            self.soft_weights = [f(clause) for clause in soft_clauses]
        else:
            self.soft_weights = soft_weights

        self.weights = None
        self.nWeights = len(self.soft_weights)

        assert self.nSoftClauses == self.nWeights, f"# clauses ({self.nSoftClauses}) != #weights ({self.nSoftClauses})"

        # MSS
        self.reuse_mss = reuse_mss
        if reuse_mss:
            self.MSSes = set()
            self.MSS_sizes = []

        # Keep track of soft clauses troughout the different omus/omusIncr calls
        self.softClauseIdxs = dict()
        # matching table clause to fixed id
        all_soft_clauses = self.soft_clauses + [frozenset({lit}) for lit in I] + [frozenset({-lit}) for lit in I]

        for idx, clause in enumerate(all_soft_clauses):
            self.softClauseIdxs[clause] = idx

    def checkSatNoSolver(self, f_prime=None):
<<<<<<< HEAD
        if self.logging:
            self.steps.sat += 1
            tstart = time.time()
=======
        # if self.logging:
        #     tstart = time.time()
>>>>>>> omus-explain-lb

        if f_prime is None:
            validated_clauses = self.clauses + self.hard_clauses
        else:
            validated_clauses = [self.clauses[i] for i in f_prime]

        lits = set(abs(lit) for lit in frozenset.union(*validated_clauses))

        with Solver() as s:
            s.append_formula(validated_clauses, no_return=False)
            solved = s.solve()
            model = s.get_model()

        if solved:
            mapped_model = set(lit for lit in model if abs(lit) in lits)
            return mapped_model, solved
        else:
            return None, solved

    def checkSat(self, f_prime):
        if self.logging:
            self.steps.sat += 1
<<<<<<< HEAD
            tstart = time.time()
=======
            # tstart = time.time()
>>>>>>> omus-explain-lb

        satsolver = Solver()

        if len(f_prime) == 0:
            return set(), True, satsolver

        validated_clauses = [self.clauses[i] for i in f_prime] + self.hard_clauses
        lits = set(abs(lit) for lit in frozenset.union(*validated_clauses))

        satsolver.append_formula(validated_clauses, no_return=False)
        solved = satsolver.solve()
        model = satsolver.get_model()

        if solved:
            mapped_model = set(lit for lit in model if abs(lit) in lits)
            return mapped_model, solved, satsolver
        else:
            return None, solved, satsolver

    def checkSatIncr(self, satsolver, hs, c):
        if self.logging:
            self.steps.sat += 1
<<<<<<< HEAD
            tstart = time.time()
=======
>>>>>>> omus-explain-lb

        validated_clauses = [self.clauses[i] for i in hs] + self.hard_clauses
        lits = set(abs(lit) for lit in frozenset.union(*validated_clauses))
        clause = self.clauses[c]

        satsolver.add_clause(clause, no_return=False)
        solved = satsolver.solve()
        model = satsolver.get_model()

        if solved:
            mapped_model = set(lit for lit in model if abs(lit) in lits)
            return mapped_model, solved, satsolver
        else:
            satsolver.delete()
            return None, solved, satsolver

    def greedyHittingSet(self, H):
        # if self.logging:
        #     tstart = time.time()
        # trivial case: empty
        # print(H)
        if len(H) == 0:
            if self.logging:
                self.steps.greedy += 1
            return set()

        # the hitting set
        C = set()

        # build vertical sets
        V = dict()  # for each element in H: which sets it is in

        for i, h in enumerate(H):
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
                (c, cover) = min(c_covers, key=lambda tpl: self.weights[tpl[0]])

            del V[c]
            C.add(c)

            # update vertical views, remove covered sets
            for e in list(V):
                # V will be changed in this loop
                V[e] -= cover
                # no sets remaining with this element?
                if len(V[e]) == 0:
                    del V[e]

        if self.logging:
            # tend = time.time()
            # self.timing.greedy.append(tend-tstart)
            self.steps.greedy += 1

        return C

    def gurobiModel(self):
        # if self.logging:
        #     tstart = time.time()
        # create gurobi model
        g_model = gp.Model('MipOptimalHittingSet')

        # model parameters
        g_model.Params.OutputFlag = 0
        g_model.Params.LogToConsole = 0
        g_model.Params.Threads = 1

        # create the variables (with weights in one go)
        x = g_model.addMVar(shape=self.nSoftClauses, vtype=GRB.BINARY, obj=self.weights, name="x")

        # set objective : min sum xi*wi
        #g_model.setObjective(sum(x[i] * self.weights[i] for i in range(self.nSoftClauses)), GRB.MINIMIZE)
        # done earlier, automatically minimisation...

        # update the model
        g_model.update()

        # if self.logging:
        #     tend = time.time()
        #     self.timing.optimal.append(tend - tstart)

        return g_model

    def addSetGurobiModel(self, gurobi_model, C):
        # variables
        x = gurobi_model.getVars()

        # add new constraint sum x[j] * hij >= 1
        # gurobi_model.addConstr(gp.quicksum(x[i] * h[i] for i in range(len(clauses))) >= 1)
        gurobi_model.addConstr(gp.quicksum(x[i] for i in C) >= 1)

    def gurobiOptimalHittingSet(self, gurobi_model):
        # if self.logging:
        #     tstart = time.time()

        # trivial case
        # if len(C) == 0:
        #     return set()

        # add new constraint sum x[j] * hij >= 1
        # self.addSetGurobiModel(gurobi_model, C)

        # solve optimization problem
        gurobi_model.optimize()

        # output hitting set
        x = gurobi_model.getVars()
        hs = set(i for i in range(self.nSoftClauses) if x[i].x == 1)

        if self.logging:
            # tend = time.time()
            # self.timing.optimal.append(tend - tstart)
            self.steps.optimal += 1

        return hs

    def gurobiOptimalHittingSetCold(self, H):
        # if self.logging:
        #     tstart = time.time()

        gurobi_model = self.gurobiModel()
        # trivial case
        if len(H) == 0:
            return []

        # add new constraint sum x[j] * hij >= 1
        for C in H:
            self.addSetGurobiModel(gurobi_model, C)

        # solve optimization problem
        gurobi_model.optimize()

        # output hitting set
        x = gurobi_model.getVars()
        hs = set(i for i in range(self.nSoftClauses) if x[i].x == 1)
        gurobi_model.dispose()

        # if self.logging:
        #     tend = time.time()
        #     self.timing.greedy.append(tend - tstart)

        return hs

    def grow(self, F_prime, model, clauses=None):
        """

            Procedure to efficiently grow the list clauses in ``F_prime``. The complement of F_prime is a correction
            set.

            :param cnf_clauses: a collection of clauses (list of literals).
            :param F_prime: hitting set : a list of clauses.
            :param extensions: list of extensions activated

            The ``extensions`` argument is a list of extensions on the default grow procedure to optimize
            the building of the minimum correction set.


            :type cnf_clauses: iterable(iterable(int))
            :type F_prime: iterable(int)
            :type extensions: iterable(int)

            Extension 1 :

                add all clauses that are true based on the assignment by the model of Fprime

            Extension 2 :

                for all variables not in variables assigned by model of Fprime
                give random values => manually check wether any clause is satisfied by this and
                add it to Fprime.

            Extension 3:

                greedy

            Extension 4:

                Maxsat
        """
        # if self.logging:
        #     tstart = time.time()
        extension = self.extension

        extensions = {
            'complement': self.defaultExtension,
            'unitprop': self.unitprop,
            'maxprop': self.maxprop,
            'greedy_param': self.greedy_param,
            'greedy_no_param': self.greedy_no_param,
            'greedy_sat': self.greedy_sat,
            'maxsat': self.maxsat_fprime,
            'greedy_vertical': self.greedy_vertical,
            # 'satlike': SATLike
        }

        new_F_prime, new_model = extensions[extension](F_prime, model)

        if self.logging:
<<<<<<< HEAD
            tend = time.time()
            self.timing.growMss.append(tend - tstart)
=======
            # tend = time.time()
            # self.timing.growMss.append(tend - tstart)
>>>>>>> omus-explain-lb
            self.steps.grow += 1
            # print("Grow:", round(tend-tstart))

        return new_F_prime, new_model

    def defaultExtension(self, F_prime, model, clauses):
        return F_prime

    def greedy_no_param(self,  F_prime, model):
        # XXX Tias thinks it has to be over all clause (filter back alter)
        # XXX Tias: SHIT! 'grow' assumes all clauses are soft...
        # XXX so it returns a solution with a violated hard constraint
        # so F - that_thing = empty.
        # how to overcome? 
        # -> we should first grow the hard clauses (or call a SAT solver to be sure)
        # -> only then 'grow' the soft clauses as we do!
        grow_clauses = self.clauses + self.hard_clauses
        cl_true = set(F_prime)
        cl_unk = set( range(len(grow_clauses)) ) - cl_true

        lit_true = set(model)
        lit_false = set(-l for l in model)
        lit_unk = set(frozenset.union(*grow_clauses)) - lit_true - lit_false

        # init counter
        cnt = Counter({literal:0 for literal in lit_unk})
        for i in cl_unk:
            cnt.update(grow_clauses[i])

        # as long as some clauses are unassigned
        while len(cl_unk) > 0:
            # check single polarity literals
            tofix = set()
            for lit in set(abs(lit) for lit in lit_unk):
                if not lit in cnt or cnt[lit] == 0:
                    tofix.add(-lit)
                elif not -lit in cnt or cnt[-lit] == 0:
                    tofix.add(lit)

            #print(cl_unk, tofix, lit_true, lit_false)
            if len(tofix) > 0:
                #print("Tofix", tofix)
                # fix all single polarity literals
                lit_true |= tofix
                lit_unk -= tofix
                tofix_neg = set(-l for l in tofix)
                lit_false |= tofix_neg
                lit_unk -= tofix_neg
            elif len(lit_unk) > 0:
                # print(cnt, lit_unk, cl_unk)
                # choose best
                # bestlit = max(lit_unk, key=lambda i: cnt[i])
                # other definition of 'best'
                bestlit = max(lit_unk, key=lambda i: cnt[i] - cnt[-i])
                #print("Best", bestlit, cnt[bestlit], cnt[-bestlit])
                lit_true.add(bestlit)
                lit_unk.remove(bestlit)
                lit_false.add(-bestlit)
                lit_unk.remove(-bestlit)
                del cnt[bestlit]
                del cnt[-bestlit]

            # update clauses (cl_unk will be modified in place)
            for idx in list(cl_unk):
                clause = grow_clauses[idx]
                unassgn = clause - lit_false
                if len(unassgn) == 0:
                    # false, no need to check again
                    cl_unk.remove(idx)
                # print(idx, clause, cl_unk, clause.intersection(lit_false))
                elif len(clause.intersection(lit_true)) > 0:
                    # true, store and remove from counter
                    cl_unk.remove(idx)
                    cl_true.add(idx)
                    cnt = cnt - Counter(clause)
                elif len(unassgn) == 1:
                    # unit...
                    # print(lit_true, unassgn)
                    bestlit = next(iter(unassgn))
                    lit_true.add(bestlit)
                    lit_unk.remove(bestlit)
                    lit_false.add(-bestlit)
                    lit_unk.remove(-bestlit)
                    del cnt[bestlit]
                    del cnt[-bestlit]
                    cl_unk.remove(idx)
                    cl_true.add(idx)

        return cl_true, lit_true

    def greedy_param(self, F_prime, model):
        # parameters
        count_clauses = self.parameters['count_clauses']
        sorting = self.parameters['sorting']
        best_unit_literal = self.parameters['best_unit_literal']
        best_literal_counter = self.parameters['best_counter_literal']

        # preprocessing
        lit_true = set(model)
        lit_false = set(-l for l in model)
        cl_true = set(F_prime)
        lit_unk = set(frozenset.union(*self.clauses)) - lit_true - lit_false
        # Pre-processing is necessary
        if sorting != ClauseSorting.IGNORE:
            cl_unk = list(set(range(self.nSoftClauses)) - cl_true)
        else:
            cl_unk = set(range(self.nSoftClauses)) - cl_true

        # literal- clause counter
        cnt = {lit:0 for lit in lit_unk}

        for i in list(cl_unk):
            clause = self.clauses[i]
            unassign_lits = clause - lit_false - lit_true
            # clause is false, remove it
            if len(unassign_lits) == 0:
                cl_unk.remove(i)
            # validated clause
            elif len(lit_true.intersection(clause)) > 0:
                cl_true.add(i)
                cl_unk.remove(i)
            else:
                for lit in unassign_lits:
                    if count_clauses == ClauseCounting.VALIDATED:
                        # check if count number of clauses
                        cnt[lit] += 1
                    elif count_clauses == ClauseCounting.WEIGHTS:
                        # clause weight
                        cnt[lit] += self.weights[i]
                    elif count_clauses == ClauseCounting.WEIGHTED_UNASSIGNED:
                        # clause weight/# litterals assigned
                        cnt[lit] += self.weights[i]/len(unassign_lits)

        while(len(cl_unk) > 0):
            # check if clauses need reordering (only useful for unit literal)
            if isinstance(sorting, ClauseSorting):
                # clause sorting based on weights
                if sorting == ClauseSorting.WEIGHTS:
                    cl_unk.sort(reverse=True, key= lambda i: self.weights[i])
                # clause sorting based on # unassigned literals
                elif sorting == ClauseSorting.UNASSIGNED:
                    cl_unk.sort(reverse=True, key= lambda i: len(self.clauses[i] - lit_true - lit_false))
                # clause sorting based on # unassigned literals
                elif sorting == ClauseSorting.WEIGHTED_UNASSIGNED:
                    cl_unk.sort(reverse=True, key= lambda i: self.weights[i] / len(self.clauses[i] - lit_true - lit_false) if len(self.clauses[i] - lit_true - lit_false) > 0 else 0 )
                elif sorting == ClauseSorting.LITERAL_ORDERING:
                    cl_unk.sort(reverse=False, key= lambda cl_id: min(abs(lit) for lit in self.clauses[cl_id]))

            # check single polarity literals
            tofix = set()
            for lit in set(abs(lit) for lit in lit_unk):
                if not lit in cnt or cnt[lit] == 0:
                    tofix.add(-lit)
                elif not -lit in cnt or cnt[-lit] == 0:
                    tofix.add(lit)

            if len(tofix) > 0:
                # fix all single polarity literals
                lit_true |= tofix
                lit_unk -= tofix
                tofix_neg = set(-l for l in tofix)
                lit_false |= tofix_neg
                lit_unk -= tofix_neg

            # Validated all pure literals
            pure_lits = {lit for lit in lit_unk if -lit not in lit_unk}

            for lit in pure_lits:
                lit_true.add(lit)
                lit_false.add(-lit)
                lit_unk.remove(lit)
                del cnt[lit]

            if len(lit_unk) > 0:
                # 4. Literal choice
                # 4.1 Literal with highest [clause count] / [sum clause weights] / [ (sum of clause weights)/#unassigned]
                if best_literal_counter == BestLiteral.COUNT_PURE_ONLY:
                    best_lit = max(lit_unk, key=lambda i: cnt[i])
                    # print(lit_unk)
                    # print(cnt)
                    # lit_max_val = max(lit_unk, key=lambda i: cnt[i])
                    # best_lit = random.choice([lit for lit in lit_unk if cnt[lit] == cnt[lit_max_val]])
                else:
                    # 4.2 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                    best_lit = max(lit_unk, key=lambda i: cnt[i] - cnt[-i])
                    # lit_max_val = max(lit_unk, key=lambda i: cnt[i] - cnt[-i])
                    # best_lit = random.choice([lit for lit in lit_unk if (cnt[lit] - cnt[-lit]) == (cnt[lit_max_val] - cnt[-lit_max_val])])

                del cnt[best_lit]
                del cnt[-best_lit]

                lit_unk.remove(best_lit)
                lit_unk.remove(-best_lit)

                lit_true.add(best_lit)
                lit_false.add(-best_lit)

            cnt = {lit:0 for lit in lit_unk}

            unit_literals = set()

            for i in set(cl_unk):
                clause = self.clauses[i]
                unassign_lits = clause - lit_false

                # clause is false, remove it
                if len(unassign_lits) == 0:
                    cl_unk.remove(i)
                # validated clause
                elif len(lit_true.intersection(clause)) > 0:
                    cl_unk.remove(i)
                    cl_true.add(i)
                # validate unit literals
                elif len(unassign_lits) == 1 and best_unit_literal != UnitLiteral.IGNORE:
                    lit = next(iter(unassign_lits))
                    if best_unit_literal == UnitLiteral.IMMEDIATE:
                        cl_true.add(i)
                        # cl_unk
                        cl_unk.remove(i)
                        # literal
                        lit_true.add(lit)
                        lit_false.add(-lit)
                        lit_unk.remove(lit)
                        del cnt[lit]
                        lit_unk.remove(-lit)
                        del cnt[-lit]
                    else:
                        unit_literals.add(lit)
                        # for lit in unassign_lits:
                        # check if count number of clauses
                        if count_clauses == ClauseCounting.VALIDATED:
                            cnt[lit] += 1
                        # clause weight
                        elif count_clauses == ClauseCounting.WEIGHTS:
                            cnt[lit] += self.weights[i]
                        # clause weight/# litterals assigned
                        elif count_clauses == ClauseCounting.WEIGHTED_UNASSIGNED:
                            cnt[lit] += self.weights[i]/len(unassign_lits)
                else:
                    for lit in unassign_lits:
                        # check if count number of clauses
                        if count_clauses == ClauseCounting.VALIDATED:
                            cnt[lit] += 1
                        # clause weight
                        elif count_clauses == ClauseCounting.WEIGHTS:
                            cnt[lit] += self.weights[i]
                        # clause weight/# litterals assigned
                        elif count_clauses == ClauseCounting.WEIGHTED_UNASSIGNED:
                            cnt[lit] += self.weights[i]/len(unassign_lits)

            while len(unit_literals) > 0:
                # 4. Literal choice
                # 4.2 Literal with highest [clause count] / [sum clause weights] / [ (sum of clause weights)/#unassigned]
                if best_unit_literal == UnitLiteral.SINGLE_POLARITY:
                    best_lit = max(unit_literals, key=lambda i: cnt[i])
                    # lit_max_val = max(unit_literals, key=lambda i: cnt[i])
                    # best_lit = random.choice([lit for lit in unit_literals if cnt[lit] == cnt[lit_max_val]])
                    # best_lit = min(unit_literals, key=lambda i: cnt[-i])
                elif best_unit_literal == UnitLiteral.POLARITY:
                # 4.3 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                    # lit_max_val = max(unit_literals, key=lambda i: cnt[i] - cnt[-i])
                    # best_lit = random.choice([lit for lit in unit_literals if (cnt[lit] - cnt[-lit]) == (cnt[lit_max_val] - cnt[-lit_max_val])])
                    best_lit = max(unit_literals, key=lambda i: cnt[i] - cnt[-i])
                else:
                    best_lit = next(iter(unit_literals))
                # literal
                lit_true.add(best_lit)
                lit_false.add(-best_lit)
                lit_unk.remove(best_lit)
                lit_unk.remove(-best_lit)
                unit_literals.remove(best_lit)
                if -best_lit in unit_literals:
                    unit_literals.remove(-best_lit)
                del cnt[best_lit]
                del cnt[-best_lit]

        # print(lit_true)
        # print(cl_true)
        # print( set(i for i, clause in enumerate(clauses) if len(clause.intersection(lit_true)) > 0))
        # assert all(False if -lit in lit_true else True for lit in lit_true)
        cl_true = set(i for i, clause in enumerate(self.clauses) if len(clause.intersection(lit_true)) > 0)
        return cl_true, lit_true

    def greedy_sat(self, F_prime, model):
        F = set(range(self.nSoftClauses))
        C = list(F - F_prime)
        new_F_prime = set(F_prime)
        new_model = set(model)
        random.shuffle(C)
        with Solver() as s:
            for i in F_prime:
                s.add_clause(self.clauses[i])
            solved = s.solve()
            while(solved):
                c = C[0]
                del C[0]
                s.add_clause(self.clauses[c])
                solved = s.solve()
                if solved:
                    new_F_prime.add(c)
                    new_model = s.get_model()
        return new_F_prime, new_model

    def greedy_vertical(self, F_prime, model):
        # soft and hard, only soft indexes really matter but all need
        # to be unit-propagated
        grow_clauses = self.clauses #+ self.hard_clauses

        ts = time.time()
        cl_true = set(F_prime)
        cl_unk = set( range(len(grow_clauses)) ) - cl_true
        #print("cl_:", time.time()-ts, len(cl_unk))
        #print("cl t",cl_true)

        lit_true = set(model)
        lit_false = set(-l for l in model)
        lit_unk = set(frozenset.union(*grow_clauses)) - lit_true - lit_false
        #print("lit_:", time.time()-ts, len(lit_unk))
        #print("lt t",lit_true)

        ts2 = time.time()
        # build vertical sets
        new_true = set()
        V = dict((e,set()) for e in lit_unk)  # for each unknown literal
        for i in sorted(cl_unk, reverse=True): # reverse: hard ones first
            # special case: already true
            if len(grow_clauses[i].intersection(lit_true)) > 0:
                cl_true.add(i)
                continue

            # special case: unit literal unknown
            unks = grow_clauses[i].intersection(lit_unk)
            if len(unks) == 1:
                # unit
                lit = next(iter(unks))
                #print("pre: unit",i, unks)
                if not -lit in new_true:
                    new_true.add(lit)
                    cl_true.add(i)
            else:
                for lit in unks:
                    V[lit].add(i)
        #print("unk",lit_unk)
        #print(V)
        # check for single polarity, add to new_true
        singpolar = [-k for (k,v) in V.items() if len(v) == 0]
        #print("singpolar", singpolar)
        for k in singpolar:
            if not -k in new_true:
                new_true.add(k)
        #print("new_true", new_true)
        #print("Built vertical:", time.time()-ts2)

        while(len(V) > 0):
            # if new_true is empty, add best one
            if len(new_true) == 0:
                # get most frequent literal
                (lit, cover) = max(V.items(), key=lambda tpl: len(tpl[1]))
                new_true.add(lit)
                #print("best new_true", new_true, len(cover))

            # prep
            # cl_newtrue = take union of new_true's in V (remove from V)
            cl_newtrue = frozenset(e for k in new_true for e in V[k])
            #print("cl_newtrue", cl_newtrue)
            cl_true |= cl_newtrue
            #print("cl_true", cl_true)
            # cl_newfalse = take union of -new_true's in V (remove from V)
            cl_newfalse = frozenset(e for k in new_true for e in V[-k])
            #print("cl_newfalse", cl_newfalse)
            for k in new_true:
                del V[k]
                if -k in V:
                    del V[-k]

            # update known literals, reset new_true
            lit_true |= new_true
            lit_unk -= new_true
            new_false = frozenset(-k for k in new_true)
            lit_false |= new_false
            lit_unk -= new_false
            new_true = set()
            #print(V, lit_true, lit_unk)

            for cl in sorted(cl_newfalse - cl_newtrue, reverse=True):
                # check for unit, add to new_true
                unks = grow_clauses[cl].intersection(lit_unk)
                if len(unks) == 1:
                    # unit
                    lit = next(iter(unks))
                    #print("unit:",lit)
                    if not -lit in new_true:
                        new_true.add(lit)
            # update vertical views (remove true clauses)
            for e in list(V):
                V[e] -= cl_newtrue
                if len(V[e]) == 0 and not e in new_true:
                    # single polarity
                    #print("single polar:",-e)
                    new_true.add(-e)
            #print(V, lit_true, lit_unk)
        #print("greedy_tias, t: ", time.time() - ts)
        #print("remaining unks:", cl_unk)
        return cl_true, lit_true

    def maxprop(self, F_prime, model):
        # parameters
        # best_unit_literal = self.parameters['best_unit_literal']
        best_literal_counter = self.parameters['best_counter_literal']

        # init counter
        all_literals = frozenset.union(*self.clauses)
        t_F_prime, t_model = self.unitprop(F_prime, model)
        lit_true = set(t_model)
        lit_false = set(-l for l in t_model)

        # alternative, over all literals
        remaining_literals = all_literals - lit_true - lit_false
        conflict_free_literals = remaining_literals - set(-l for l in remaining_literals)

        cnt = Counter({literal:0 for literal in remaining_literals})
        for i,clause in enumerate(self.clauses):
            if i not in t_F_prime:
                lit_intersect_cl = remaining_literals.intersection(clause)
                cnt.update(lit_intersect_cl)

        while(len(conflict_free_literals) > 0):

            if best_literal_counter == BestLiteral.COUNT_PURE_ONLY:
                best_lit = max(conflict_free_literals, key=lambda i: cnt[i])
            else:
                # 4.2 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                best_lit = max(conflict_free_literals, key=lambda i: cnt[i] - cnt[-i])

            lit_true.add(best_lit)
            lit_false.add(-best_lit)

            t_F_prime, t_model = self.unitprop(t_F_prime, lit_true)

            lit_true = set(t_model)
            lit_false = set(-l for l in t_model)

            remaining_literals = all_literals - lit_true - lit_false
            conflict_free_literals = remaining_literals - set(-l for l in remaining_literals if -l in remaining_literals)

            cnt = Counter({literal:0 for literal in conflict_free_literals})
            for i, clause in enumerate(self.clauses):
                if i not in t_F_prime:
                    lit_intersect_cl = conflict_free_literals.intersection(clause)
                    cnt.update(lit_intersect_cl)

        conflictual_literals = set(remaining_literals)

        cnt = Counter({literal:0 for literal in conflictual_literals})
        for i,clause in enumerate(self.clauses):
            if i not in t_F_prime:
                lit_intersect_cl = conflictual_literals.intersection(clause)
                cnt.update(lit_intersect_cl)

        assert all([True if -l in conflictual_literals else False for l in conflictual_literals])

        # propagate all remaining literals
        while len(conflictual_literals) > 0:
            if best_literal_counter == BestLiteral.COUNT_PURE_ONLY:
                best_lit = max(conflictual_literals, key=lambda i: cnt[i])
            else:
                # 4.2 Literal with highest polarity clause count / sum of clause weights / sum of clause weights/#unassigned
                best_lit = max(conflictual_literals, key=lambda i: cnt[i] - cnt[-i])

            conflictual_literals.remove(best_lit)
            # because the unit prop created a conflict-free one, we must check
            if -best_lit in conflictual_literals:
                conflictual_literals.remove(-best_lit)

            lit_true.add(best_lit)
            lit_false.add(-best_lit)

            # unit propagate new literal
            t_F_prime, t_model = self.unitprop(t_F_prime, lit_true)

            lit_true = set(t_model)
            lit_false = set(-l for l in t_model)

            # code was probably not finished because the latter was missing
            remaining_literals = all_literals - lit_true - lit_false
            conflictual_literals = set(remaining_literals)

            cnt = Counter({literal:0 for literal in conflictual_literals})
            for i,clause in enumerate(self.clauses):
                if i not in t_F_prime:
                    lit_intersect_cl = conflictual_literals.intersection(clause)
                    cnt.update(lit_intersect_cl)

        assert all([True if -l not in lit_true else False for l in lit_true])

        return t_F_prime, lit_true

<<<<<<< HEAD
=======

    def maxsat_fprime_n(self, F_prime, n):
        t_F_prime = set(F_prime)

        wcnf = WCNF()
        wcnf.extend(self.hard_clauses)
        for i, clause in enumerate(self.clauses):
            if i in F_prime:
                wcnf.append(list(clause))
            else:
                wcnf.append(list(clause), weight=self.weights[i])

        list_msses = []
        with RC2(wcnf) as rc2:
            for id, model in enumerate(rc2.enumerate()):
                if id == n:
                    break

                t_F_prime = set(F_prime)
                t_model = set(model)
                for i, clause in enumerate(self.clauses):
                    if i not in t_F_prime and len(clause.intersection(t_model)) > 0:
                        t_F_prime.add(i)

                list_msses.append((frozenset(t_F_prime), frozenset(t_model)))

        return list_msses

>>>>>>> omus-explain-lb
    def maxsat_fprime(self, F_prime, model):
        t_F_prime = set(F_prime)

        wcnf = WCNF()
        wcnf.extend(self.hard_clauses)
        for i, clause in enumerate(self.clauses):
            if i in F_prime:
                wcnf.append(list(clause))
            else:
                wcnf.append(list(clause), weight=self.weights[i])

        with RC2(wcnf) as rc2:
            t_model = rc2.compute()

        for i, clause in enumerate(self.clauses):
            if i not in t_F_prime and len(clause.intersection(t_model)) > 0:
                t_F_prime.add(i)

        return t_F_prime, t_model

    def unitprop(self, F_prime, model):
        """`Extension1' unit propagate the model to find all clauses hit by the current
        assignment of F_prime.

        Arguments:
            clauses {iterable(iterable(int))} -- collection of clauses (sets of literals)
            F_prime {iterable(int)} -- Hitting set, optimal set of clauses hitting H
            model {iterable(int)} -- model of clauses in F_prime

        Returns:
            iterable(int), iterable(int) -- Grown hitting set, new model of hitting set
        """
        # parameters
        best_unit_literal = self.parameters['best_unit_literal'] if 'best_unit_literal' in parameters else UnitLiteral.IMMEDIATE

        new_F_prime = set(F_prime)
        # precompute both
        lit_true = set(model)
        lit_false = set(-l for l in model)

        clause_added = True
        while(clause_added):
            clause_added = False
            t_F_prime = set(new_F_prime)
            for i, clause in enumerate(self.clauses):
                if i in new_F_prime:
                    continue # already in F_prime

                # Similar alternative:
                if len(clause.intersection(lit_true)) > 0:
                    # a true literal, clause is true
                    t_F_prime.add(i)
                    clause_added = True

                else:
                    unassigned = clause - lit_false
                    if len(unassigned) == 1 and best_unit_literal == UnitLiteral.IMMEDIATE:
                        t_F_prime.add(i)
                        # add literal to the model
                        lit = next(iter(unassigned))
                        lit_true.add(lit)
                        lit_false.add(-lit)
                        clause_added = True
            if len(t_F_prime) > len(new_F_prime):
                new_F_prime = t_F_prime
                # check for unit propagation

        assert all([True if -l not in lit_true else False for l in lit_true]), f"Conflicting literals {lit_true}"
        return new_F_prime, lit_true

<<<<<<< HEAD
    def omusIncr(self, add_clauses, add_weights=None, limit=None, best_cost=None):
        # Benchmark info
        t_start = time.time()
        if self.logging:
            t_start = time.time()
=======
    def omusIncr(self, I_cnf, explained_literal, add_weights=None, best_cost=None, hs_limit=None, postponed_omus=True, timeout=None):
        # Benchmark info
        t_start_omus = time.time()
        if self.logging:
>>>>>>> omus-explain-lb
            n_greedy = self.steps.greedy
            n_sat = self.steps.sat
            n_grow = self.steps.grow
            n_optimal = self.steps.optimal
            n_incremental = self.steps.incremental
        if self.reuse_mss:
            n_msses = len(self.MSSes)
        # Build clauses and additional weights
        self.clauses = self.soft_clauses + I_cnf + [frozenset({-explained_literal})]
        self.nSoftClauses = len(self.clauses)

        if add_weights is not None:
            self.weights = self.soft_weights + add_weights
        elif self.f is not None:
            self.weights = self.soft_weights + [f(clause) for clause in I_cnf + [frozenset({-explained_literal})]]

        # ---- getting more steps when reusing the models
        self.nWeights = len(self.weights)

        assert self.nSoftClauses == self.nWeights, "Weights must be the same"

        F = frozenset(range(self.nSoftClauses))
<<<<<<< HEAD
        mapped_model, solved =  self.checkSatNoSolver()
        assert solved == False, f"CNF is satisfiable check sat no solver"
        #print("\tcnf is sat", time.time()-t_start)
=======
        # print(F)
        
>>>>>>> omus-explain-lb

        self.hs_sizes = []
        H, C = [], []
        h_counter = Counter()

        gurobi_model = self.gurobiModel()
        satsolver, sat, hs = None, None, None
        my_cost = None

<<<<<<< HEAD

        # # XXX THIS PART IS A BOTTLENECK: slow for some reason... perhaps first 4 lines the list comprehension
        # if self.reuse_mss:

        #     # F_idxs = {self.softClauseIdxs[clause]: pos for pos, clause in enumerate(self.clauses)}
        #     # F_ranges = set(self.softClauseIdxs[clause] for clause in self.clauses)
        #     # soft_clauses always going to be there !
        #     for mss_ranges, MSS_model in set(self.MSSes):

        #         # mss = set(F_idxs[mss_idx] for mss_idx in P.iterate(mss_ranges.intersection(), step=1) if mss_idx in F_idxs)

        #         # if any(True if mss.issubset(MSS) else False for MSS in added_MSSes):
        #         #     continue

        #         # grow model over hard clauses first, must be satisfied
        #         if True or self.extension == 'maxsat':
        #             MSS, model = self.grow(mss, MSS_model)
        #         else:
        #             MSS, model = self.grow(mss, MSS_model, self.hard_clauses)
        #             # grow model over as many as possible soft clauses next 
        #             MSS, model = self.grow(mss, model, self.clauses)

        #         C = F - MSS

        #         if C not in H:
        #             h_counter.update(list(C))
        #             H.append(C)
        #             added_MSSes.append(MSS)
        #             self.addSetGurobiModel(gurobi_model, C)

        #             # adding the MSS as intervals
        #             mssIdxs = set(self.softClauseIdxs[self.clauses[id]] for id in MSS&F)

        #             r = ranges(mssIdxs)
        #             mss_inside = False
        #             for m, _ in self.MSSes:
        #                 if r in m:
        #                     mss_inside = True
        #                     break

        #             if not mss_inside:
        #             # for m in self.MSSes:
        #                 self.MSSes.add((r, frozenset(model)))
        # print("\treuse added", round(time.time()-t_start, 3), "s")
        # print("\t#MSSes=", len(self.MSSes))
        # mode = MODE_GREEDY

        mode = MODE_OPT
        while(True):
            #print(f"\t\topt steps = {self.steps.optimal - n_optimal}\t greedy steps = {self.steps.greedy - n_greedy}\t incremental steps = {self.steps.incremental - n_incremental}")
            while(True):
                #print(f"\t\topt steps = {self.steps.optimal - n_optimal}\t greedy steps = {self.steps.greedy - n_greedy}\t incremental steps = {self.steps.incremental - n_incremental}")
                if limit is not None and \
                   self.steps.greedy - n_greedy + self.steps.optimal - n_optimal + self.steps.incremental - n_incremental >= limit:
                    return None, None
=======
        # WARNING: self.MSSes is a tuple (mss, model)
        # XXX: the models are HUGE! can save memory if only on grid vars?
        if self.reuse_mss:
            added_MSSes = []
            # map global 'softClauseIdx' to local 'pos'
            F_idxs = {self.softClauseIdxs[clause]: pos for pos, clause in enumerate(self.clauses)}

            for mss_idxs, MSS_model in self.MSSes:

                # part of fullMSS
                if mss_idxs.issubset(self.fullMss):
                    # print("MSS is subset")
                    continue

                # if literal not in the model then we can skip it
                if explained_literal not in MSS_model and -explained_literal not in MSS_model:
                    continue

                # get local pos from global idx
                mss = set(F_idxs[mss_idx] for mss_idx in mss_idxs&F_idxs.keys())
                # print(mss, )

                if any(mss.issubset(MSS) for MSS in added_MSSes):
                    continue

                # grow model over hard clauses first, must be satisfied
                # Timing: grow is rather slow
                # XXX Model if literal inside then add it to the MSS and C = F-MSS
                # XXX remove grow
                # MSS, model = self.grow(mss, MSS_model)
                C = F - mss

                if C not in H:
                    h_counter.update(list(C))
                    H.append(C)
                    added_MSSes.append(mss&F)
                    self.addSetGurobiModel(gurobi_model, C)
        t_growing = 0
        t_incremental = 0
        t_greedy = 0
        t_sat=0
        t_opt=0
        mode = MODE_OPT
        #print("\n")
        while(True):
            # print(hs)
            if (time.time() -t_start_omus) > timeout:
                gurobi_model.dispose()
                self.hs_sizes.append(len(H))
                if self.reuse_mss:
                    self.MSS_sizes.append(len(self.MSSes) - n_msses)
                # Benchmark info
                if self.logging:
                    exec_time = time.time() - t_start_omus

                    self.total_timings.append(exec_time)
                    self.optimal_steps.append(self.steps.optimal - n_optimal)
                    self.greedy_steps.append(self.steps.greedy - n_greedy)
                    self.incremental_steps.append(self.steps.incremental - n_incremental)
                    self.sat_steps.append(self.steps.sat - n_sat)
                    self.grow_steps.append(self.steps.grow - n_grow)
                    self.optimal_timing.append(t_opt)
                    self.greedy_timing.append(t_greedy)
                    self.incremental_timing.append(t_incremental)
                    self.sat_timing.append(t_sat)
                    self.grow_timing.append(t_growing)
                return None, my_cost
            # print(f"\t\topt steps = {self.steps.optimal - n_optimal}\t greedy steps = {self.steps.greedy - n_greedy}\t incremental steps = {self.steps.incremental - n_incremental}")
            while(True and postponed_omus):
                if (time.time() -t_start_omus) > timeout:
                    gurobi_model.dispose()
                    self.hs_sizes.append(len(H))
                    if self.reuse_mss:
                        self.MSS_sizes.append(len(self.MSSes) - n_msses)
                    # Benchmark info
                    if self.logging:
                        exec_time = time.time() - t_start_omus
                        self.total_timings.append(exec_time)
                        self.optimal_steps.append(self.steps.optimal - n_optimal)
                        self.greedy_steps.append(self.steps.greedy - n_greedy)
                        self.incremental_steps.append(self.steps.incremental - n_incremental)
                        self.sat_steps.append(self.steps.sat - n_sat)
                        self.grow_steps.append(self.steps.grow - n_grow)
                        self.optimal_timing.append(t_opt)
                        self.greedy_timing.append(t_greedy)
                        self.incremental_timing.append(t_incremental)
                        self.sat_timing.append(t_sat)
                        self.grow_timing.append(t_growing)
                    return None, my_cost
                # print("Starting with optimal!")
                # print(f"\t\topt steps = {self.steps.optimal - n_optimal}\t greedy steps = {self.steps.greedy - n_greedy}\t incremental steps = {self.steps.incremental - n_incremental}")
>>>>>>> omus-explain-lb
                if mode == MODE_INCR:
                    t_start_incr = time.time()
                    # add sets-to-hit incrementally until unsat then continue with optimal method
                    # given sets to hit 'CC', a hitting set thereof 'hs' and a new set-to-hit added 'C'
                    # then hs + any element of 'C' is a valid hitting set of CC + C
                    # choose element from C with smallest weight
                    c = min(C, key=lambda i: self.weights[i])
                    # find all elements with smallest weight
                    m = [ci for ci in C if self.weights[ci] == self.weights[c]]
                    # choose clause with smallest weight appearing most in H
                    c_best = max(m, key=lambda ci: h_counter[ci])
                    hs.add(c_best)
                    # self.hs_sizes.append(len(hs))
                    if self.logging:
                        # tend = time.time()
                        # self.timing.incremental.append(tend - tstart)
                        self.steps.incremental += 1
                    t_end_incr = time.time()-t_start_incr
                    t_incremental += t_end_incr
                elif mode == MODE_GREEDY:
                    # ----- Greedy compute hitting set
                    t_startgreedy = time.time()
                    hs = self.greedyHittingSet(H)
<<<<<<< HEAD
                #print("\tgreedy or incr computed", time.time()-t_start)
=======
                    t_satend = time.time() - t_startgreedy
                    t_greedy += t_satend
                    # self.hs_sizes.append(len(hs))
>>>>>>> omus-explain-lb
                elif mode == MODE_OPT:
                    break
                # ----- check satisfiability of hitting set
                if mode == MODE_INCR:
                    t_satstart = time.time()
                    (model, sat, satsolver) = self.checkSatIncr(satsolver=satsolver, hs=hs, c=c_best)
                    t_satend = time.time() - t_satstart
                    t_sat += t_satend
                elif mode == MODE_GREEDY:
                    t_satstart = time.time()
                    (model, sat, satsolver) = self.checkSat(hs)
<<<<<<< HEAD
                #print("\ths sat checked", time.time()-t_start)


                E_i = [ci for ci in hs if self.clauses[ci] in add_clauses]

                # constraint used ('and not ci in E_i': dont repeat unit clauses)
                S_i = [ci for ci in hs if self.clauses[ci] in self.soft_clauses and self.clauses[ci] not in add_clauses]
                # opti = optimalPropagate(hard_clauses + E_i + S_i, I)
                my_cost = self.cost((E_i, S_i))

                # if best_cost is not None and best_cost < my_cost:
                #     return  None, None
                if not sat or (best_cost is not None and best_cost < my_cost):                    # incremental hs is unsat, switch to optimal method
=======
                    t_satend = time.time() - t_satstart
                    t_sat += t_satend

                E_i = [ci for ci in hs if self.clauses[ci] in I_cnf]

                # constraint used ('and not ci in E_i': dont repeat unit clauses)
                S_i = [ci for ci in hs if self.clauses[ci] in self.soft_clauses]
                # S_i = [ci for ci in hs if self.clauses[ci] in self.soft_clauses and self.clauses[ci] not in I_cnf]

                my_cost = self.cost((E_i, S_i))
                # print(my_cost, "vs ", best_cost)
                # if(len())

                if not sat or (best_cost is not None and best_cost <= my_cost):
                    # incremental hs is unsat, switch to optimal method
>>>>>>> omus-explain-lb
                    hs = None
                    if mode == MODE_INCR:
                        mode = MODE_GREEDY
                        satsolver.delete()
                        continue
                    elif mode == MODE_GREEDY:
                        mode = MODE_OPT
                        break
                    # break # skip grow
                t_growstart = time.time()
                # if (best_cost is not None and best_cost <= my_cost):
                # ------ Grow
                if True or self.extension == 'maxsat':
                    # grow model over hard clauses first, must be satisfied
                    MSS, MSS_model = self.grow(hs, model)
                else:
                    # grow model over hard clauses first, must be satisfied
                    MSS, MSS_model = self.grow(hs, model, self.hard_clauses)
                    # print("hard grow:",len(MSS),model,"->",MSS_model)
                    # grow model over as many as possible soft clauses next 
                    MSS, MSS_model = self.grow(hs, MSS_model, self.clauses)
                    # print("soft grow:",MSS,MSS_model)

                C = F - MSS
                assert len(C) > 0, f"Greedy: hs={hs}, model={model}"
                #print("hs grown", time.time()-t_start)

                # Store the MSSes
                if self.reuse_mss:
<<<<<<< HEAD
                    mssIdxs = set(self.softClauseIdxs[self.clauses[id]] for id in MSS&F)
                    r = ranges(mssIdxs)
                    mss_inside = False
                    for m, _ in self.MSSes:
                        if r in m:
                            mss_inside = True
                            break
                    if not mss_inside:
                        self.MSSes.add((r, frozenset(MSS_model)))
                    # print(mssIdxs)
                    # print(ranges(mssIdxs))
                    # self.MSSes.add((mssIdxs, frozenset(MSS_model)))

=======
                    mssIdxs = frozenset(self.softClauseIdxs[self.clauses[id]] for id in MSS&F)
                    # mssIdxs = frozenset(self.softClauseIdxs[self.clauses[id]] for id in MSS)
                    # self.MSSes = self.MSSes.filter()
                    storeMss= not mssIdxs.issubset(self.fullMss) and \
                              not any(True if mssIdxs.issubset(m[0]) else False for m in self.MSSes)
                    if(storeMss):
                        self.MSSes.add((mssIdxs, frozenset(MSS_model)))
                t_growend = time.time() - t_growstart
                t_growing += t_growend
>>>>>>> omus-explain-lb
                h_counter.update(list(C))
                self.addSetGurobiModel(gurobi_model, C)
                H.append(C)

                # Sat => Back to incremental mode 
                mode = MODE_INCR

            #print("before optimal", time.time()-t_start)
            # ----- Compute Optimal Hitting Set
            t_optstart = time.time()
            hs = self.gurobiOptimalHittingSet(gurobi_model)
<<<<<<< HEAD
            #print("after optimal", time.time()-t_start)
=======
            t_optend = time.time() - t_optstart
            t_opt += t_optend
            # self.hs_sizes.append(len(hs))

            # check cost, return premptively if worse than best
            E_i = [ci for ci in hs if self.clauses[ci] in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in hs if self.clauses[ci] in self.soft_clauses]

            # opti = optimalPropagate(hard_clauses + E_i + S_i, I)
            my_cost = self.cost((E_i, S_i))
            # print(my_cost, "vs", best_cost)
            if best_cost is not None and my_cost >= best_cost:
                gurobi_model.dispose()
                self.hs_sizes.append(len(H))
                if self.reuse_mss:
                    self.MSS_sizes.append(len(self.MSSes) - n_msses)
                # Benchmark info
                if self.logging:
                    exec_time = time.time() - t_start_omus

                    self.total_timings.append(exec_time)
                    self.optimal_steps.append(self.steps.optimal - n_optimal)
                    self.greedy_steps.append(self.steps.greedy - n_greedy)
                    self.incremental_steps.append(self.steps.incremental - n_incremental)
                    self.sat_steps.append(self.steps.sat - n_sat)
                    self.grow_steps.append(self.steps.grow - n_grow)
                    self.optimal_timing.append(t_opt)
                    self.greedy_timing.append(t_greedy)
                    self.incremental_timing.append(t_incremental)
                    self.sat_timing.append(t_sat)
                    self.grow_timing.append(t_growing)
                return None, my_cost
>>>>>>> omus-explain-lb

            # ------ Sat check
            t_satstart = time.time()
            (model, sat, satsolver) = self.checkSat(hs)
            t_satend = time.time() - t_satstart
            t_sat += t_satend

            #print("optimal, sat?", time.time()-t_start)

            if not sat:
                #
                self.hs_sizes.append(len(H))
                satsolver.delete()
                gurobi_model.dispose()
<<<<<<< HEAD
                # print("OMUS:")
                if self.reuse_mss:
                    MSS = F-hs
                    model, solved = self.checkSatNoSolver(MSS)
                    assert solved == True
                    mssIdxs = set(self.softClauseIdxs[self.clauses[id]] for id in MSS&F)
                    # print(mssIdxs)
                    r = ranges(mssIdxs)

                    self.MSSes.add((r, frozenset(MSS_model)))

=======
                if self.reuse_mss:
                    self.MSS_sizes.append(len(self.MSSes) - n_msses)
>>>>>>> omus-explain-lb
                # Benchmark info
                if self.logging:
                    exec_time = time.time() - t_start_omus

                    self.total_timings.append(exec_time)
<<<<<<< HEAD
                    if self.reuse_mss:
                        self.MSS_sizes.append(len(self.MSSes) - n_msses)
=======
>>>>>>> omus-explain-lb
                    self.optimal_steps.append(self.steps.optimal - n_optimal)
                    self.greedy_steps.append(self.steps.greedy - n_greedy)
                    self.incremental_steps.append(self.steps.incremental - n_incremental)
                    self.sat_steps.append(self.steps.sat - n_sat)
                    self.grow_steps.append(self.steps.grow - n_grow)
<<<<<<< HEAD
=======
                    self.optimal_timing.append(t_opt)
                    self.greedy_timing.append(t_greedy)
                    self.incremental_timing.append(t_incremental)
                    self.sat_timing.append(t_sat)
                    self.grow_timing.append(t_growing)
>>>>>>> omus-explain-lb
                #print("\n")
                return hs, [self.clauses[idx] for idx in hs]
            t_growstart = time.time()
            # ------ Grow
            if self.extension == 'maxsat':
                # grow model over hard clauses first, must be satisfied
<<<<<<< HEAD
                MSS, MSS_model = self.grow(hs, model, self.hard_clauses)
=======
                # MSS, MSS_model = self.grow(hs, model, self.hard_clauses)
                MSS, MSS_model = self.grow(hs, model)
>>>>>>> omus-explain-lb
            else:
                # grow model over hard clauses first, must be satisfied
                MSS, MSS_model = self.grow(hs, model, self.hard_clauses)
                # print("hard grow:",len(MSS),model,"->",MSS_model)
                # grow model over as many as possible soft clauses next
                MSS, MSS_model = self.grow(hs, MSS_model, self.clauses)

            if self.reuse_mss:
<<<<<<< HEAD
                # mssIdxs = [self.softClauseIdxs[self.clauses[id]] for id in MSS&F]
                # self.MSSes.add((mssIdxs, frozenset(MSS_model)))
                mssIdxs = set(self.softClauseIdxs[self.clauses[id]] for id in MSS&F)
                # print(mssIdxs)
                r = ranges(mssIdxs)

                self.MSSes.add((r, frozenset(MSS_model)))
                # print(ranges(mssIdxs))

            E_i = [ci for ci in hs if self.clauses[ci] in add_clauses]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in hs if self.clauses[ci] in self.soft_clauses and self.clauses[ci] not in add_clauses]
            # opti = optimalPropagate(hard_clauses + E_i + S_i, I)
            my_cost = self.cost((E_i, S_i))

            if best_cost is not None and best_cost < my_cost:
                return None, None

=======
                mssIdxs = frozenset(self.softClauseIdxs[self.clauses[id]] for id in MSS&F)
                # mssIdxs = frozenset(self.softClauseIdxs[self.clauses[id]] for id in MSS)
                storeMss= not mssIdxs.issubset(self.fullMss) and \
                            not any(True if mssIdxs < m[0] else False for m in self.MSSes)
                if(storeMss):
                    self.MSSes.add((mssIdxs, frozenset(MSS_model)))
            t_growend = time.time() - t_growstart
            t_growing += t_growend
>>>>>>> omus-explain-lb
            C = F - MSS
            self.addSetGurobiModel(gurobi_model, C)
            assert len(C) > 0, f"Opt: C empty\nhs={hs}\nmodel={model}"

            h_counter.update(list(C))
            H.append(C)
            mode = MODE_INCR

    def omus(self, add_clauses, add_weights=None):
        # ---------- build clauses and additional weights
        self.clauses = self.base_clauses + add_clauses
        self.nSoftClauses = len(self.clauses)

        if add_weights is not None:
            self.weights = self.base_weights + add_weights
        elif self.f is not None:
            self.weights = self.base_weights + [f(clause) for clause in add_clauses]
        else:
            self.weights = self.base_weights + [len(clause) for clause in add_clauses]

        assert len(self.clauses) == len(self.weights)

        # benchmark variables
        F = frozenset(range(self.nSoftClauses))
        gurobi_model = self.gurobiModel()
        H = []
        C = [] # last added 'set-to-hit'
        hs = None # last computed hitting set
        # t_start_omus = time.time()
        while(True):

            hs = self.gurobiOptimalHittingSet(gurobi_model, C)
            # print(hs)
            model, sat = self.checkSatNoSolver(hs)

            # if not sat or steps > max_steps_main:
            if not sat:
                gurobi_model.dispose()
                # return hs
                return hs, [set(self.clauses[idx]) for idx in hs]

            MSS, _ = self.grow(hs, model)
            C = F - MSS
            # print(MSS, C)

            self.addSetGurobiModel(gurobi_model, C)
            H.append(C)

    def export_results(self, outputDir, outputFile):
        # import pathlib
        from pathlib import Path
        p = Path(outputDir)
        if not p.exists():
            p.mkdir()

        results = dict()

        # global 
        results['execution_times'] = self.total_timings
        results['MSS_sizes'] = self.MSS_sizes
        results['MSSes'] = [ (list(MSS), list(model)) for MSS, model in self.MSSes]
        results['nSoftClauses'] = self.nSoftClauses
        results['nWeights'] = self.nWeights

        # n steps for every OMUS call
        results['optimal_steps'] = self.optimal_steps
        results['greedy_steps'] = self.greedy_steps
        results['incremental_steps'] = self.incremental_steps

        # Individual timings of the calls
        results['timing.optimal'] = self.timing.optimal
        results['timing.greedy'] = self.timing.greedy
        results['timing.sat'] = self.timing.sat
        results['timing.incremental'] = self.timing.incremental
        results['timing.growMss'] = self.timing.growMss

        with open(outputDir + outputFile, 'w') as file:
            file.write(json.dumps(results)) # use `json.loads` to do the reverse

<<<<<<< HEAD
    def basecost(self, constraints, clues):
        # nClues = len(constraints.intersection(clues))
        nClues = sum([1 if self.soft_weights[i] == 20 else 0 for i in constraints])
=======

    def basecost(self, constraints):
        # nClues = len(constraints.intersection(clues))
        if self.clues is not None:
            nClues = sum([1 if id in self.clues else 0 for id in constraints])
        else:
            nClues = 0
>>>>>>> omus-explain-lb
        nOthers = len(constraints) - nClues
        # print("constraints = ", constraints)
        if nClues == 0 and nOthers == 1:
            return 0
        elif nClues == 0 and nOthers > 1:
            return 20
        else:
            return nClues * 20


    def cost(self, explanation):
<<<<<<< HEAD
        # TODO match puzzle bvs
        facts, constraints = explanation
        # return self.basecost(constraints, set()) + len(facts) + len(constraints)
        return self.basecost(constraints, set()) + len(facts) + len(constraints)


# SOURCE: https://stackoverflow.com/questions/2361945/detecting-consecutive-integers-in-a-list


def ranges(nums):
    nums = sorted(set(nums))
    gaps = [[s, e] for s, e in zip(nums, nums[1:]) if s+1 < e]
    edges = iter(nums[:1] + sum(gaps, []) + nums[-1:])
    P1 = P.empty()
    for s, e in zip(edges, edges):
        P1 |= P.closed(s, e)
    return P1
=======
        facts, constraints = explanation
        return self.basecost(constraints) + len(facts) + len(constraints)
>>>>>>> omus-explain-lb


if __name__ == "__main__":
    cnf = CNF()
    cnf.append([6, 2])    # c1: ¬s
    cnf.append([-6, 2])    # c1: ¬s
    cnf.append([-2, 1])    # c1: ¬s
    cnf.append([-1])    # c1: ¬s
    cnf.append([-6,8])    # c1: ¬s
    cnf.append([6, 8])    # c1: ¬s
    cnf.append([2, 4])    # c1: ¬s
    cnf.append([-4, 5])    # c1: ¬s
    cnf.append([7, 5])    # c1: ¬s
    cnf.append([-7, 5])    # c1: ¬s
    cnf.append([-5, 3])    # c1: ¬s
    cnf.append([-3])    # c1: ¬s
    parameters = {
        'extension': 'greedy_no_param',
        'output': "bacchus_log.json",
    }
    o = OMUS(from_CNF=cnf, parameters=parameters)
    # print(o.omus())
    print(o.omusIncr())
    print(o.MSSes)
