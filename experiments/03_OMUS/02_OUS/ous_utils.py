import math


class OusParams(object):
    def __init__(self):
        self.incremental = False
        # self.incremental_sat = False
        self.pre_seed = False
        self.sort_lits = False
        self.constrained = False
        self.bounded = False
        self.post_opt = False
        self.post_opt_incremental = False
        self.post_opt_greedy = False
        self.benchmark = False
        self.extension = ''
        self.outputFile = ''
        self.timeout = None


class Clauses(object):
    def __init__(self):
        self.__hard_clauses = []
        self.__soft_clauses = []
        self.__soft_weights = []
        self.__all_soft_idxs = set()
        self.nHardClauses = 0
        self.nSoftClauses = 0
        self.nAllClauses = 0

    def add_hardclauses(self, added_clauses):
        self.__hard_clauses += added_clauses
        self.nSoftClauses = len(self.__hard_clauses)

    def add_soft_clauses(self, added_clauses, added_weights=None, f=None):
        self.__soft_clauses += added_clauses
        self.nSoftClauses = len(self.__soft_clauses)
        self.__all_soft_idxs

        if added_weights is not None:
            self.__soft_weights += added_weights
        elif f is not None:
            self.__soft_weights += [f(cl) for cl in added_clauses]
        else:
            raise "Weights/mapping f not provided"

    @property
    def all_soft_idxs(self): return self.hard_clauses + self.soft_clauses

    @property
    def clauses(self): return self.hard_clauses + self.soft_clauses

    @property
    def soft_weights(self): return self.__soft_weights

    @property
    def weights(self): return [math.inf for _ in self.__hard_clauses] + self.__soft_weights


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