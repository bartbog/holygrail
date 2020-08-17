# system utilities
from collections import Counter

# Pysat Utilities
from pysat.solvers import Solver
from pysat.formula import CNF, WCNF
from pysat.examples.rc2 import RC2

# Gurobi utilities
import gurobipy as gp
from gurobipy import GRB

# OMUS Utilities
from OMUS_utils import ClauseCounting, ClauseSorting, BestLiteral, UnitLiteral

# GLOBAL VARIABELS
MODE_OPT, MODE_INCR, MODE_GREEDY = (1, 2, 3)


def bacchus():
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


class OMUS(object):
    def __init__(self, from_clauses=None, from_CNF=None, solver="Gurobi-Warm", parameters={}, weights=None, f=lambda x: len(x), output='log.json'):
        # parameters of the solver
        self.extension = parameters['extension'] if 'extension' in parameters else 'greedy_no_param'
        self.output = parameters['output'] if 'output' in parameters else output
        self.cutoff_main = parameters['cutoff_main'] if 'cutoff_main' in parameters else 15*60
        self.parameters = parameters

        if from_clauses is not None:
            self.cnf = CNF(from_clauses=from_clauses)
        elif from_CNF is not None:
            self.cnf = from_CNF
        else:
            raise "No cnf provided"

        self.clauses = [frozenset(c for c in clause) for clause in self.cnf.clauses]
        self.nClauses = len(self.clauses)

        _, solved = self.checkSatNoSolver({i for i in range(self.nClauses)})
        # print(solved)
        assert solved is False, "Cnf is satisfiable"

        # self.solver = solver
        self.H = []
        self.MSSes = []
        # self.C = []

        if weights is None:
            self.weights = [f(clause) for clause in self.clauses]
        else:
            assert len(weights) == len(self.clauses), f"# clauses ({self.nClauses}) != # weights ({len(weights)})"
            self.weights = weights

        self.mode = MODE_GREEDY

    def checkSatNoSolver(self, f_prime):
        if len(f_prime) == 0:
            return [], True

        # print(f_prime)
        validated_clauses = [self.clauses[i] for i in f_prime]
        lits = set(abs(lit) for lit in frozenset.union(*validated_clauses))

        with Solver() as s:
            s.append_formula(validated_clauses, no_return=False)
            solved = s.solve()
            model = s.get_model()
        # print(solved, model)
        if solved:
            mapped_model = set(lit for lit in model if abs(lit) in lits)
            return mapped_model, solved
        else:
            return None, solved

    def checkSat(self, f_prime):
        satsolver = Solver()

        if len(f_prime) == 0:
            return [], True, satsolver

        validated_clauses = [self.clauses[i] for i in f_prime]
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
        validated_clauses = [self.clauses[i] for i in hs]
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

    def greedyHittingSet(self):
        # trivial case: empty
        # print(H)
        if len(self.H) == 0:
            return set()

        C = set() # the hitting set

        # build vertical sets
        V = dict() # for each element in H: which sets it is in
        for i, h in enumerate(self.H):
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
            for e in list(V): # V will be changed in this loop
                V[e] -= cover
                # no sets remaining with this element?
                if len(V[e]) == 0:
                    del V[e]

        return C

    def gurobiModel(self):
        # create gurobi model
        g_model = gp.Model('MipOptimalHittingSet')

        # model parameters
        # g_model.Params.LogFile = 'logs/'+datetime.now().strftime("%Y_%m_%d_%H_%M_%S")+'.log'
        g_model.Params.OutputFlag = 0
        g_model.Params.LogToConsole = 0
        g_model.Params.Threads = 8

        # create the variables
        x = g_model.addMVar(shape=self.nClauses, vtype=GRB.BINARY, name="x")

        # set objective : min sum xi*wi
        g_model.setObjective(sum(x[i] * self.weights[i] for i in range(self.nClauses)), GRB.MINIMIZE)

        # update the model
        g_model.update()

        return g_model

    def addSetGurobiModel(self, gurobi_model, C):
        # variables
        x = gurobi_model.getVars()

        # add new constraint sum x[j] * hij >= 1
        # gurobi_model.addConstr(gp.quicksum(x[i] * h[i] for i in range(len(clauses))) >= 1)
        gurobi_model.addConstr(gp.quicksum(x[i] for i in C) >= 1)

    def gurobiOptimalHittingSet(self, gurobi_model, C):
        # trivial case
        if len(C) == 0:
            return set()

        # add new constraint sum x[j] * hij >= 1
        self.addSetGurobiModel(gurobi_model, C)

        # solve optimization problem
        gurobi_model.optimize()

        # output hitting set
        x = gurobi_model.getVars()
        hs = set(i for i in range(self.nClauses) if x[i].x == 1)

        return hs

    def gurobiOptimalHittingSetAll(self, gurobi_model, C):
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
        hs = set(i for i in range(self.nClauses) if x[i].x == 1)

        return hs

    def gurobiOptimalHittingSetCold(self):
        gurobi_model = self.gurobiModel()
        # trivial case
        if len(self.H) == 0:
            return []

        # add new constraint sum x[j] * hij >= 1
        for C in self.H:
            self.addSetGurobiModel(gurobi_model, C)

        # solve optimization problem
        gurobi_model.optimize()

        # output hitting set
        x = gurobi_model.getVars()
        hs = set(i for i in range(self.nClauses) if x[i].x == 1)
        gurobi_model.dispose()

        return hs

    def grow(self, F_prime, model):
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
        extension = self.extension

        extensions = {
            'complement': self.defaultExtension,
            'unitprop': self.unitprop,
            'maxprop': self.maxprop,
            'greedy_param': self.greedy_param,
            'greedy_no_param': self.greedy_no_param,
            'maxsat': self.maxsat_fprime,
            # 'satlike': SATLike
        }
        # print("clauses=", clauses)
        # print("weights=",weights)
        # print("F_prime=", F_prime)
        # print("model=", model)
        # print("parameters=", parameters)
        new_F_prime, new_model = extensions[extension](F_prime, model)

        return new_F_prime, new_model

    def defaultExtension(self, F_prime, model):
        return F_prime

    def greedy_no_param(self,  F_prime, model):
        cl_true = set(F_prime)
        cl_unk = set( range(self.nClauses) ) - cl_true

        lit_true = set(model)
        lit_false = set(-l for l in model)
        lit_unk = set(frozenset.union(*self.clauses)) - lit_true - lit_false

        # init counter
        cnt = Counter({literal:0 for literal in lit_unk})
        for i in cl_unk:
            cnt.update(self.clauses[i])

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
                clause = self.clauses[idx]
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
            cl_unk = list(set(range(self.nClauses)) - cl_true)
        else:
            cl_unk = set(range(self.nClauses)) - cl_true

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

    def omusIncr(self, MSSes=None):
        self.H = []

        gurobi_model = self.gurobiModel()
        C = [] # last added 'set-to-hit'
        hs = None # last computed hitting set
        h_counter = Counter()
        satsolver = None
        sat = True
        F = set(range(self.nClauses))

        if MSSes is not None:
            for mss, model in MSSes:
                hs = F.intersection(mss)
                C = self.grow(hs, model)
                self.H.append(C)

        mode = MODE_GREEDY
        while(True):
            while(True):
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
                elif mode == MODE_GREEDY:
                    # ----- Greedy compute hitting set
                    hs = self.greedyHittingSet()

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
                mss, mss_model = self.grow(hs, model)
                C = F - mss

                self.addSetGurobiModel(gurobi_model, C)
                h_counter.update(list(C))
                self.H.append(C)
                self.MSSes.append((mss, mss_model))

                # Sat => Back to incremental mode 
                mode = MODE_INCR

            # ----- Compute Optimal Hitting Set
            hs = self.gurobiOptimalHittingSet(gurobi_model, C)

            # ------ Sat check
            (model, sat, satsolver) = self.checkSat(hs)

            if not sat:
                gurobi_model.dispose()
                return [list(self.clauses[idx]) for idx in hs]

            # ------ Grow
            mss, mss_model = self.grow(hs, model)
            C = F - mss
            h_counter.update(list(C))
            self.H.append(C)
            self.MSSes.append((mss, mss_model))
            mode = MODE_INCR

    def omus(self):
        # benchmark variables
        gurobi_model = self.gurobiModel()
        self.H = []
        C = [] # last added 'set-to-hit'
        hs = None # last computed hitting set
        # t_start_omus = time.time()
        while(True):

            hs = self.gurobiOptimalHittingSet(gurobi_model, C)

            model, sat = self.checkSatNoSolver(hs)

            # if not sat or steps > max_steps_main:
            if not sat:
                gurobi_model.dispose()
                # return hs
                return [list(self.clauses[idx]) for idx in hs]

            C = self.grow(hs, model)

            self.addSetGurobiModel(gurobi_model, C)
            self.H.append(C)


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
# class OMUSSolver(object):
#     def __init__(self, name):
#         self.name = name


# class GurobiSolver(OMUSSolver):
#     def __init__(self, warm_start, weights):
#         self.weights = weights
#         if warm_start:
#             super().__init__("Gurobi-Warm")
#         else:
#             super().__init__("Gurobi-Cold")


# class OrTools(OMUSSolver):
#     def __init__(self, weights):
#         super().__init__("OrTools")
#         from ortools.linear_solver import pywraplp
#         from OMUS_utils import *
#         self.weights = weights

#     def optimalHittingSet(self, H):
#         # trivial case
#         if len(H) == 0:
#             return []
#         # indices of clauses used
#         indices_H = sorted(set.union(*H))
#         n_constraints = len(H)
#         n_vars = len(indices_H)

#         bounds = [1 for i in range(n_constraints)]
#         obj_coeffs = {index: self.weights[index] for index in indices_H}

#         # constraint coefficients hij = 1 if variable x_j is in set h_i
#         c_coeffs = [[None for _ in range(n_vars)] for _ in range(n_constraints)]

#         for j, hj in enumerate(H):
#             for i in range(n_vars):
#                 c_coeffs[j][i] = 1 if indices_H[i] in hj else 0

#         # data['constraint_coefficients'] = c_coeffs

#         # matching clause indices with position in list of clause indices
#         # ex: {3 : 0, 7: 1, ....} clause 3 position 0, clause 7 position 1, ...
#         # data['matching_table'] = {idx: i for i, idx in enumerate(indices_H)}
#         # [START solver]
#         # Create the mip solver with the CBC backend.
#         # solver = pywraplp.Solver('OptimalHittingSet', pywraplp.Solver.BOP_INTEGER_PROGRAMMING)
#         solver = pywraplp.Solver('OptimalHittingSet', pywraplp.Solver.CBC_MIXED_INTEGER_PROGRAMMING)
#         # [END solver]

#         # [START variables]
#         #infinity = solver.infinity()
#         x = {}
#         for j in indices_H:
#             # x[j] = solver.IntVar(0,1,'x[%i]' % j)
#             x[j] = solver.BoolVar('x[%i]' % j)
#         # [END variables]

#         # [START constraints]
#         for i in range(n_constraints):
#             # for all i in {1.. |H|}: sum x[j] * hij >= 1
#             constraint_expr = [c_coeffs[i][j] * x[idx] for j, idx in enumerate(indices_H)]
#             solver.Add(sum(constraint_expr) >= bounds[i])
#         # [END constraints]

#         # [START objective]
#         # Maximize sum w[i] * x[i]
#         objective = solver.Objective()
#         for idx in indices_H:
#             objective.SetCoefficient(x[idx], obj_coeffs[idx])
#         objective.SetMinimization()
#         # [END objective]

#         # max 10 minute timeout for solution
#         k = solver.SetNumThreads(8)
#         solver.set_time_limit(60 * 3* 1000)
#         # solver.set_time_limit(10 * 60 * 1000)

#         # Solve the problem and print the solution.
#         status = solver.Solve()
#         if status == pywraplp.Solver.OPTIMAL:
#             hs = [j for j in indices_H if x[j].solution_value() == 1]
#             return hs
#         else:
#             raise f"Solution not optimal! H={H}, obj_coefs={obj_coeffs}, c={c_coeffs}"
#             return []