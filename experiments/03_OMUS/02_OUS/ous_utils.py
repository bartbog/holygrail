import math
import pprint
from collections import Counter
from gurobipy import GRB

pp = pprint.PrettyPrinter(indent=4)

class OusParams(object):

    def __init__(self):
        self.incremental = False
        self.pre_seed = False
        self.sort_lits = False
        self.constrained = False
        self.bounded = False
        self.post_opt = False
        self.post_opt_incremental = False
        self.post_opt_greedy = False
        self.benchmark = False
        self.outputFile = ''
        self.timeout = None

    def __repr__(self):
        return {
            'pre_seed': self.pre_seed,
            'constrained': self.constrained,
            "incremental": self.incremental,
            'bounded': self.bounded,
            'sort_lits': self.sort_lits,
            'post_opt': self.post_opt,
            'post_opt_incremental': self.post_opt_incremental,
            'post_opt_greedy': self.post_opt_greedy,
            'benchmark': self.benchmark,
            'extension': self.extension,
            'output': self.outputFile,
            'timeout': self.timeout,
        }


class Clauses(object):
    def __init__(self, constrainedOUS=True):
        self.constrainedOUS = constrainedOUS
        self.__hard_clauses = []
        self.__soft_clauses = []
        self.__soft_weights = []
        self.__all_soft_clauses = []
        self.__all_soft_idxs = set()
        self.__all_lits = set()
        self.__lits = set()
        self.__Icnf = []
        self.__notIcnf = []
        self.derived_idxs = set()
        self.__obj_weights = []
        self.h_counter = Counter()

    def add_hardclauses(self, added_clauses):
        self.__hard_clauses += [frozenset(clause) for clause in added_clauses]
        for clause in added_clauses:
            self.__all_lits |= set(clause)
            self.__lits |= set(abs(lit) for lit in clause)

    def add_soft_clauses(self, added_clauses, added_weights=None, f=None):
        self.__soft_clauses += [frozenset(clause) for clause in added_clauses]
        for clause in added_clauses:
            self.__all_lits |= set(clause)
            self.__lits |= set(abs(lit) for lit in clause)

        if added_weights is not None:
            self.__soft_weights += added_weights
        elif f is not None:
            self.__soft_weights += [f(cl) for cl in added_clauses]
        else:
            raise "Weights/mapping f not provided"

        self.__all_soft_clauses = self.__soft_clauses + self.__Icnf + self.__notIcnf
        self.__all_soft_idxs = set(i for i in range(len(self.__all_soft_clauses)))

    def add_indicatorVars(self, weights):
        self.h_counter = Counter()
        indHard = []
        indVars = set(i for i in range(self.nLits + 1, self.nLits + self.nHard + 1))

        # update hard clauses with indicator variables
        for clause, i in zip(self.__hard_clauses, indVars):
            new_clause = set(clause) | {i}
            indHard.append(frozenset(new_clause))
            self.h_counter.update(list(new_clause))
            self.h_counter.update([-i])

        self.__hard_clauses = indHard

        # add indicator variables to soft clauses
        soft_inds = [frozenset({-i}) for i in indVars]

        if weights is None:
            self.add_soft_clauses(added_clauses=soft_inds, added_weights=[1 for _ in indVars])
        else:
            self.add_soft_clauses(added_clauses=soft_inds, added_weights=weights)

        self.__all_soft_clauses = self.__soft_clauses + self.__Icnf + self.__notIcnf
        self.__all_soft_idxs = set(i for i in range(len(self.__all_soft_clauses)))

        return indVars

    def add_I(self, added_I):
        for i in added_I:
            self.__Icnf.append(frozenset({i}))
            self.__notIcnf.append(frozenset({-i}))

        if self.constrainedOUS:
            # INFINITY because the knowledge is not derived yet
            self.__obj_weights += [GRB.INFINITY for _ in added_I]
            # 0 because we want to choose 1 of the neg lits for explanations
            self.__obj_weights += [0 for _ in added_I]

        self.__all_soft_clauses = self.__soft_clauses + self.__Icnf + self.__notIcnf
        self.__all_soft_idxs = set(i for i in range(len(self.__all_soft_clauses)))

    @property
    def indicator_vars(self):
        return self.__ind_vars

    @property
    def nLits(self):
        return len(self.__lits)

    @property
    def all_lits(self):
        """All -/+ literals appearing in the clauses."""
        return set(self.__all_lits)

    @property
    def lits(self):
        """All lits"""
        return set(self.__lits)

    @property
    def nHard(self):
        return len(self.__hard_clauses)

    @property
    def nSoft(self):
        return len(self.__soft_clauses)

    @property
    def nSoftI(self):
        return len(self.__soft_weights) + len(self.__obj_weights)

    @property
    def nDerived(self):
        return len(self.derived_idxs)

    @property
    def nHardSoft(self):
        return len(self.__soft_clauses) + len(self.__hard_clauses)

    @property
    def soft_clauses(self): return list(self.__soft_clauses)

    @property
    def derived_I_idxs(self):
        return set(self.nSoft + i for i in range(self.derived_idxs))

    @property
    def all_soft_clauses(self):
        # if self.__all_soft_clauses
        return list(self.__all_soft_clauses)

    @property
    def all_soft_weights(self):
        return self.__soft_weights + [1 if i == 0 else i for i in self.__obj_weights]
    
    @property
    def soft_idxs(self):
        return set(i for i in range(self.nSoft))
    
    @property
    def I_idxs(self):
        return set(i for i in range(self.nSoft, self.nSoftI))

    @property
    def all_soft_clauses_idxs(self):
        # soft + I_cnf_all + (- I_cnf_all)
        return set(self.__all_soft_idxs)

    @property
    def soft_I_lit_clause_idxs(self):
        # soft + I_cnf + (-lit)
        n = self.nSoft + self.nDerived + 1
        return set(i for i in range(n))

    @property
    def obj_weights(self):
        return self.__soft_weights + self.__obj_weights

    def add_derived_Icnf(self, addedI):
        for i in addedI:
            fi = frozenset({i})
            fnoti = frozenset({-i})

            posi = self.__Icnf.index(fi)
            posnoti = self.__notIcnf.index(fnoti)

            self.derived_idxs.add(posi)
            if self.constrainedOUS:
                self.__obj_weights[posi] = 1
                self.__obj_weights[len(self.__Icnf) + posnoti] = GRB.INFINITY

    def lit_idx(self, lit):
        return self.__Icnf.index(lit)

    @property
    def nCNFLits(self):
        return len(self.__Icnf)

    @property
    def hard_clauses(self): return list(self.__hard_clauses)

    @property
    def soft_weights(self): return self.__soft_weights

    @property
    def weights(self):
        return [math.inf for _ in self.__hard_clauses] + self.__soft_weights

    def __str__(self):
        return f"""
        Clauses:
        \t  hard={[list(cl) for cl in self.__hard_clauses]},
        \t  soft={[list(cl) for cl in self.__soft_clauses]},
        \tw_soft={self.__soft_weights},
        \t  lits={self.__lits},
        \t  Icnf={[list(cl) for cl in self.__Icnf]},
        \t -Icnf={[list(cl) for cl in self.__notIcnf]},
        \t w_obj={self.__obj_weights}
        \t cnter={self.h_counter}
        \t
        """


class BenchmarkInfo(object):
    def __init__(self):
        self.steps = Steps()
        self.timings = Timings()


class Steps(object):
    def __init__(self, incremental=0, greedy=0, optimal=0, sat=0, grow=0):
        self.incremental = incremental
        self.greedy = greedy
        self.optimal = optimal
        self.sat = sat
        self.grow = grow

    def __addSteps__(self, other):
        assert type(other) is Steps, "Other must be of same type"
        self.incremental += other.incremental
        self.greedy += other.greedy
        self.optimal += other.optimal
        self.sat += other.sat
        self.grow += other.grow

    def __subSteps__(self, other):
        assert type(other) is Steps, "Other must be of same type"
        self.incremental -= other.incremental
        self.greedy -= other.greedy
        self.optimal -= other.optimal
        self.sat -= other.sat
        self.grow -= other.grow

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

    def __repr__(self): return f"Steps:\n------\nIncremental=\t{self.incremental}\nGreedy=\t\t{self.greedy}\nOptimal=\t{self.optimal}"


class Timings(object):
    def __init__(self):
        self.greedy = []
        self.optimal = []
        self.incremental = []
        self.sat = []
        self.growMss = []