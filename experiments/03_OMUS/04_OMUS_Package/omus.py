# system utilities
from collections import Counter
from enum import Enum, IntEnum
import time
import random

# Gurobi utilities
import gurobipy as gp
from gurobipy import GRB
# Pysat Utilities
from pysat.examples.rc2 import RC2
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

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
    def __init__(self, incremental=0, greedy=0, optimal=0):
        self.incremental = incremental
        self.greedy = greedy
        self.optimal = optimal

    def __sub__(self, other):
        s = Steps()
        s.incremental = self.incremental - other.incremental
        s.greedy = self.greedy - other.greedy
        s.optimal = self.optimal - other.optimal
        return s

    def __add__(self, other):
        s = Steps()
        s.incremental = self.incremental + other.incremental
        s.greedy = self.greedy + other.greedy
        s.optimal = self.optimal + other.optimal
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
    def __init__(self, hard_clauses=None, soft_clauses=None, I=None, bv=None, soft_weights=None, parameters={}, f=lambda x: len(x), logging=True, reuse_mss=True):
        # checking input
        assert (f is not None) or (weights is not None), "No mapping function or weights supplied."
        assert (hard_clauses is not None), "No clauses or CNF supplied."
        assert I is not None, "No interpretation provided"
        assert bv is not None, "Please add indication variables"

        # parameters of the solver
        self.extension = parameters['extension'] if 'extension' in parameters else 'greedy_no_param'
        self.output = parameters['output'] if 'output' in parameters else 'log.json'
        self.parameters = parameters

        # Logging / benchmark info
        self.logging = logging
        if logging:
            self.steps = Steps()
            self.timing = Timings()
            self.total_timings = []
            self.optimal_steps = []
            self.greedy_steps = []
            self.incremental_steps = []

        # clauses
        self.hard_clauses = [frozenset(clause) for clause in hard_clauses]
        self.soft_clauses = [frozenset(clause) for clause in soft_clauses]
        self.clauses = self.soft_clauses # soft + omus 'added' ones
        self.nSoftClauses = len(self.soft_clauses)

        # indicator variables
        self.bv = bv
        self.nBv = len(bv)

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
        if self.logging:
            tstart = time.time()
        
        #if f_prime is not None and len(f_prime) == 0:
        #    return [], True

        if f_prime is None:
            validated_clauses = self.clauses + self.hard_clauses
        else:
            validated_clauses = [self.clauses[i] for i in f_prime]
        lits = set(abs(lit) for lit in frozenset.union(*validated_clauses))

        with Solver() as s:
            s.append_formula(validated_clauses, no_return=False)
            solved = s.solve()
            model = s.get_model()
        # print(solved, model)

        if self.logging:
            tend = time.time()
            self.timing.sat.append(tend - tstart)
        if solved:
            mapped_model = set(lit for lit in model if abs(lit) in lits)
            return mapped_model, solved
        else:
            return None, solved

    def checkSat(self, f_prime):
        if self.logging:
            tstart = time.time()

        satsolver = Solver()

        #if len(f_prime) == 0:
        #    return [], True, satsolver

        validated_clauses = [self.clauses[i] for i in f_prime] + self.hard_clauses
        lits = set(abs(lit) for lit in frozenset.union(*validated_clauses))

        satsolver.append_formula(validated_clauses, no_return=False)
        solved = satsolver.solve()
        model = satsolver.get_model()

        if self.logging:
            tend = time.time()
            self.timing.sat.append(tend - tstart)

        if solved:
            mapped_model = set(lit for lit in model if abs(lit) in lits)
            return mapped_model, solved, satsolver
        else:
            return None, solved, satsolver

    def checkSatIncr(self, satsolver, hs, c):
        if self.logging:
            tstart = time.time()

        validated_clauses = [self.clauses[i] for i in hs] + self.hard_clauses
        lits = set(abs(lit) for lit in frozenset.union(*validated_clauses))
        clause = self.clauses[c]

        satsolver.add_clause(clause, no_return=False)
        solved = satsolver.solve()
        model = satsolver.get_model()

        if self.logging:
            tend = time.time()
            self.timing.sat.append(tend - tstart)

        if solved:
            mapped_model = set(lit for lit in model if abs(lit) in lits)
            return mapped_model, solved, satsolver
        else:
            satsolver.delete()
            return None, solved, satsolver

    def greedyHittingSet(self, H):
        if self.logging:
            tstart = time.time()
        # trivial case: empty
        # print(H)
        if len(H) == 0:
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
            tend = time.time()
            self.timing.greedy.append(tend-tstart)
            self.steps.greedy += 1

        return C

    def gurobiModel(self):
        if self.logging:
            tstart = time.time()
        # create gurobi model
        g_model = gp.Model('MipOptimalHittingSet')

        # model parameters
        # g_model.Params.LogFile = 'logs/'+datetime.now().strftime("%Y_%m_%d_%H_%M_%S")+'.log'
        g_model.Params.OutputFlag = 0
        g_model.Params.LogToConsole = 0
        g_model.Params.Threads = 8

        # create the variables
        x = g_model.addMVar(shape=self.nSoftClauses, vtype=GRB.BINARY, name="x")

        # set objective : min sum xi*wi
        g_model.setObjective(sum(x[i] * self.weights[i] for i in range(self.nSoftClauses)), GRB.MINIMIZE)

        # update the model
        g_model.update()

        if self.logging:
            tend = time.time()
            self.timing.greedy.append(tend - tstart)

        return g_model

    def addSetGurobiModel(self, gurobi_model, C):
        # variables
        x = gurobi_model.getVars()

        # add new constraint sum x[j] * hij >= 1
        # gurobi_model.addConstr(gp.quicksum(x[i] * h[i] for i in range(len(clauses))) >= 1)
        gurobi_model.addConstr(gp.quicksum(x[i] for i in C) >= 1)

    def gurobiOptimalHittingSet(self, gurobi_model):
        if self.logging:
            tstart = time.time()

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
            tend = time.time()
            self.timing.optimal.append(tend - tstart)
            self.steps.optimal += 1

        return hs

    # def gurobiOptimalHittingSetAll(self, gurobi_model, C):
        if self.logging:
            tstart = time.time()

        # trivial case
        if len(C) == 0:
            return []

        # print(C)
        for ci in C:
            # print(ci)
            # add new constraint sum x[j] * hij >= 1
            self.addSetGurobiModel(self.clauses, gurobi_model, ci)

        # solve optimization problem
        gurobi_model.optimize()

        # output hitting set
        x = gurobi_model.getVars()
        hs = set(i for i in range(self.nSoftClauses) if x[i].x == 1)

        if self.logging:
            tend = time.time()
            self.timing.greedy.append(tend - tstart)

        return hs

    def gurobiOptimalHittingSetCold(self, H):
        if self.logging:
            tstart = time.time()

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

        if self.logging:
            tend = time.time()
            self.timing.greedy.append(tend - tstart)

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
        if self.logging:
            tstart = time.time()
        extension = self.extension

        extensions = {
            'complement': self.defaultExtension,
            'unitprop': self.unitprop,
            'maxprop': self.maxprop,
            'greedy_param': self.greedy_param,
            'greedy_no_param': self.greedy_no_param,
            'greedy_sat': self.greedy_sat,
            'maxsat': self.maxsat_fprime,
            # 'satlike': SATLike
        }
        # print("clauses=", clauses)
        # print("weights=",weights)
        # print("F_prime=", F_prime)
        # print("model=", model)
        # print("parameters=", parameters)
        new_F_prime, new_model = extensions[extension](F_prime, model, clauses)

        if self.logging:
            tend = time.time()
            self.timing.growMss.append(tend - tstart)

        return new_F_prime, new_model

    def defaultExtension(self, F_prime, model, clauses):
        return F_prime

    def greedy_no_param(self,  F_prime, model, grow_clauses):
        # XXX Tias thinks it has to be over all clause (filter back alter)
        # XXX Tias: SHIT! 'grow' assumes all clauses are soft...
        # XXX so it returns a solution with a violated hard constraint
        # so F - that_thing = empty.
        # how to overcome? 
        # -> we should first grow the hard clauses (or call a SAT solver to be sure)
        # -> only then 'grow' the soft clauses as we do!
        if grow_clauses is None:
            print("Warning, GROW should get explicit hard/soft clauses...")
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

    def greedy_vertical(self,  F_prime, model):
        ts = time.time()
        cl_true = set(F_prime)
        cl_unk = set( range(self.nSoftClauses) ) - cl_true
        #print("cl_:", time.time()-ts, len(cl_unk))
        #print("cl t",cl_true)

        lit_true = set(model)
        lit_false = set(-l for l in model)
        lit_unk = set(frozenset.union(*self.clauses)) - lit_true - lit_false
        #print("lit_:", time.time()-ts, len(lit_unk))
        #print("lt t",lit_true)

        ts2 = time.time()
        # build vertical sets
        new_true = set()
        V = dict((e,set()) for e in lit_unk)  # for each unknown literal
        for i in cl_unk:
            # special case: already true
            if len(self.clauses[i].intersection(lit_true)) > 0:
                cl_true.add(i)
                continue

            # special case: unit literal unknown
            unks = self.clauses[i].intersection(lit_unk)
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

            for cl in cl_newfalse - cl_newtrue:
                # check for unit, add to new_true
                unks = self.clauses[cl].intersection(lit_unk)
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

    def maxsat_fprime(self, F_prime, model):
        t_F_prime = set(F_prime)

        wcnf = WCNF()
        for i, clause in enumerate(self.clauses):
            if i in F_prime:
                wcnf.append(list(clause))
            else:
                wcnf.append(list(clause), weight=weights[i])

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

    def omusIncr(self, add_clauses, add_weights=None):
        # Benchmark info
        t_start = time.time()
        n_msses = len(self.MSSes)
        n_greedy = self.steps.greedy
        n_optimal = self.steps.optimal
        n_incremental = self.steps.incremental

        # Build clauses and additional weights
        self.clauses = self.soft_clauses + add_clauses
        self.nSoftClauses = len(self.clauses)

        if add_weights is not None:
            self.weights = self.soft_weights + add_weights
        elif self.f is not None:
            self.weights = self.soft_weights + [f(clause) for clause in add_clauses]

        # ---- getting more steps when reusing the models
        self.nWeights = len(self.weights)

        assert self.nSoftClauses == self.nWeights, "Weights must be the same"

        F = frozenset(range(self.nSoftClauses))
        mapped_model, solved =  self.checkSatNoSolver()
        assert solved == False, "CNF is satisfiable"

        H, C = [], []
        h_counter = Counter()

        if self.reuse_mss:
            added_MSSes = []

        gurobi_model = self.gurobiModel()
        satsolver, sat, hs = None, None, None


        if self.reuse_mss:
            F_idxs = {self.softClauseIdxs[clause]: pos for pos, clause in enumerate(self.clauses)}
            for mss_idxs, MSS_model in set(self.MSSes):
                mss = set(F_idxs[mss_idx] for mss_idx in mss_idxs if mss_idx in F_idxs)

                if any(True if mss.issubset(MSS) else False for MSS in added_MSSes):
                    continue

                # grow model over hard clauses first, must be satisfied
                MSS, model = self.grow(mss, MSS_model, self.hard_clauses)
                # grow model over as many as possible soft clauses next 
                MSS, model = self.grow(mss, model, self.clauses)
                C = F - MSS

                if C not in H:
                    h_counter.update(list(C))
                    H.append(C)
                    added_MSSes.append(MSS)
                    self.addSetGurobiModel(gurobi_model, C)
                    #TODO: Check wether this is a good idea or not !
                    mssIdxs = frozenset(self.softClauseIdxs[self.clauses[id]] for id in MSS)
                    self.MSSes.add((mssIdxs, frozenset(model)))

        mode = MODE_GREEDY
        print("\n")
        while(True):
            print(f"\t\topt steps = {self.steps.optimal - n_optimal}\t greedy steps = {self.steps.greedy - n_greedy}\t incremental steps = {self.steps.incremental - n_incremental}", end='\r')
            while(True):
                print(f"\t\topt steps = {self.steps.optimal - n_optimal}\t greedy steps = {self.steps.greedy - n_greedy}\t incremental steps = {self.steps.incremental - n_incremental}", end='\r')
                if mode == MODE_INCR:
                    if self.logging:
                        tstart = time.time()
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
                    if self.logging:
                        tend = time.time()
                        self.timing.incremental.append(tend - tstart)
                        self.steps.incremental += 1
                elif mode == MODE_GREEDY:
                    # ----- Greedy compute hitting set
                    hs = self.greedyHittingSet(H)

                # ----- check satisfiability of hitting set
                if mode == MODE_INCR:
                    (model, sat, satsolver) = self.checkSatIncr(satsolver=satsolver, hs=hs, c=c_best)
                elif mode == MODE_GREEDY:
                    (model, sat, satsolver) = self.checkSat(hs)

                if not sat:
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

                # ------ Grow
                # grow model over hard clauses first, must be satisfied
                MSS, MSS_model = self.grow(hs, model, self.hard_clauses)
                print("hard grow:",len(MSS),model,"->",MSS_model)
                # grow model over as many as possible soft clauses next 
                MSS, MSS_model = self.grow(hs, MSS_model, self.clauses)
                print("soft grow:",MSS,MSS_model)
                print("MSS",MSS)
                C = F - MSS
                print("C",C)
                assert len(C) > 0, f"Greedy: hs={hs}, model={model}"

                # Store the MSSes
                if self.reuse_mss:
                    mssIdxs = frozenset(self.softClauseIdxs[self.clauses[id]] for id in MSS)
                    self.MSSes.add((mssIdxs, frozenset(MSS_model)))

                h_counter.update(list(C))
                self.addSetGurobiModel(gurobi_model, C)
                H.append(C)

                # Sat => Back to incremental mode 
                mode = MODE_INCR

            # ----- Compute Optimal Hitting Set
            hs = self.gurobiOptimalHittingSet(gurobi_model)

            # ------ Sat check
            (model, sat, satsolver) = self.checkSat(hs)

            if not sat:
                #
                gurobi_model.dispose()

                # Benchmark info
                if self.logging:
                    exec_time = time.time() - t_start
                    self.total_timings.append(exec_time)
                    self.MSS_sizes.append(len(self.MSSes) - n_msses)
                    self.optimal_steps.append(self.steps.optimal - n_optimal)
                    self.greedy_steps.append(self.steps.greedy - n_greedy)
                    self.incremental_steps.append(self.steps.incremental - n_incremental)
                print("\n")
                return hs, [set(self.clauses[idx]) for idx in hs]

            # ------ Grow
            # grow model over hard clauses first, must be satisfied
            MSS, MSS_model = self.grow(hs, model, self.hard_clauses)
            # grow model over as many as possible soft clauses next 
            MSS, MSS_model = self.grow(hs, MSS_model, self.clauses)
            C = F - MSS
            self.addSetGurobiModel(gurobi_model, C)
            assert len(C) > 0, f"Opt: C empty\nhs={hs}\nmodel={model}"

            h_counter.update(list(C))
            H.append(C)
            mode = MODE_INCR

            if self.reuse_mss:
                mssIdxs = frozenset(self.softClauseIdxs[self.clauses[id]] for id in MSS)
                self.MSSes.add((mssIdxs, frozenset(MSS_model)))

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
            print(hs)
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
