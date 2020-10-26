import math
import pprint
from collections import Counter
from gurobipy import GRB
import cProfile
import pstats
from functools import wraps

from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
from pysat.examples.rc2 import RC2

# Gurobi utilities
import gurobipy as gp
from gurobipy import GRB

pp = pprint.PrettyPrinter(indent=4)


def profileFunc(output_file=None, sort_by='cumulative', lines_to_print=None, strip_dirs=False):
    """A time profiler decorator.
    Inspired by and modified the profile decorator of Giampaolo Rodola:
    http://code.activestate.com/recipes/577817-profile-decorator/
    src:
    https://towardsdatascience.com/how-to-profile-your-code-in-python-e70c834fad89
    Args:
        output_file: str or None. Default is None
            Path of the output file. If only name of the file is given, it's
            saved in the current directory.
            If it's None, the name of the decorated function is used.
        sort_by: str or SortKey enum or tuple/list of str/SortKey enum
            Sorting criteria for the Stats object.
            For a list of valid string and SortKey refer to:
            https://docs.python.org/3/library/profile.html#pstats.Stats.sort_stats
        lines_to_print: int or None
            Number of lines to print. Default (None) is for all the lines.
            This is useful in reducing the size of the printout, especially
            that sorting by 'cumulative', the time consuming operations
            are printed toward the top of the file.
        strip_dirs: bool
            Whether to remove the leading path info from file names.
            This is also useful in reducing the size of the printout
    Returns:
        Profile of the decorated function
    """

    def inner(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            _output_file = output_file or func.__name__ + '.prof'
            pr = cProfile.Profile()
            pr.enable()
            retval = func(*args, **kwargs)
            pr.disable()
            pr.dump_stats(_output_file)

            with open(_output_file, 'w') as f:
                ps = pstats.Stats(pr, stream=f)
                if strip_dirs:
                    ps.strip_dirs()
                if isinstance(sort_by, (tuple, list)):
                    ps.sort_stats(*sort_by)
                else:
                    ps.sort_stats(sort_by)
                ps.print_stats(lines_to_print)
            return retval

        return wrapper

    return inner


class OptSolver(object):
    def __init__(self, clauses, constrained=True):

        self.clauses = clauses
        self.constrained = constrained

        if constrained:
            self.opt_model = self.cOUSModel()
        else:
            self.opt_model = self.OUSModel()

    def cOUSModel(self):
        assert self.clauses.nSoft + 2 * self.clauses.nCNFLits == self.nClauses, "check nclauses"
        assert len(self.clauses.obj_weights) == self.nClauses, "#weights != #clauses"

        self.opt_model = gp.Model('constrOptHS')

        # model parameters
        self.opt_model.Params.OutputFlag = 0
        self.opt_model.Params.LogToConsole = 0
        self.opt_model.Params.Threads = 8
        # update the model
        x = self.opt_model.addMVar(
            shape=self.nClauses,
            vtype=GRB.BINARY,
            obj=self.clauses.obj_weights,
            name="x")

        # exactly one of the -literals
        vals = range(self.clauses.nSoft + self.clauses.nCNFLits, self.nClauses)
        self.opt_model.addConstr(x[vals].sum() == 1)

        # at least one of the soft clauses
        vals2 = range(self.clauses.nSoft  + self.clauses.nCNFLits)
        self.opt_model.addConstr(x[vals2].sum() >= 1)

        self.opt_model.update()

    def OUSModel(self):
        self.opt_model = gp.Model('OptHS')

        # model parameters
        self.opt_model.Params.OutputFlag = 0
        self.opt_model.Params.LogToConsole = 0
        self.opt_model.Params.Threads = 8

        #TODO add variables
        raise "NotImplemented"

    def addCorrectionSet(self, C):
        x = self.opt_model.getVars()

        # add new constraint sum x[j] * hij >= 1
        self.opt_model.addConstr(gp.quicksum(x[i] for i in C) >= 1)

    def optHS(self):
        self.opt_model.optimize()
        x = self.opt_model.getVars()
        hs = set(i for i in range(self.nClauses) if x[i].x == 1)

        return hs

    def set_objective(self):
        x = self.opt_model.getVars()
        self.opt_model.setObjective(gp.quicksum(x[i] * self.obj_weights[i] for i in self.clause_idxs), GRB.MINIMIZE)

    def __del__(self):
        self.opt_model.dispose()
        # self.opt_model.


class Grower(object):
    def __init__(self, clauses):
        self.clauses = clauses

    def grow_default(self, f_prime, model):
        return f_prime, model

    def grow_maxsat(self, hs_in, model):
        hs = set(hs_in) # take copy!!

        wcnf = WCNF()
        wcnf.extend(self.clauses.hard_clauses)
        soft_clauses = self.clauses.all_soft_clauses
        soft_weights = self.clauses.all_soft_weights

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


class SatChecker(object):
    def __init__(self, clauses):
        self.clauses = clauses
        self.satsolver = Solver(bootstrap_with=self.clauses.hard_clauses)

    def checkSat(self, assumptions: list = []):
        # print(assumptions)
        if self.satsolver is not None:
            polarities = []
            if self.params.constrained:
                all_soft = self.clauses.all_soft_clauses
                for i in assumptions:
                    cl = all_soft[i]
                    # if len(cl) == 1:
                    # print(next(iter(cl)))
                    polarities.append(next(iter(cl)))
            else:
                raise NotImplementedError("Checksat not constrained not implemented")

            solved = self.satsolver.solve(assumptions=polarities)
            model = self.satsolver.get_model()
            return solved, model

    def __del__(self):
        self.satsolver.delete()


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
            assert len(added_clauses) == len(added_weights), f"Weights ({len(added_weights)}) and clauses ({len(added_clauses)}) must be  of same length"
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
        max_lit = max(self.__lits)
        indVars = set(i for i in range(max_lit + 1, max_lit + self.nHard + 1))

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
        # return self.__soft_weights + [1 for i in self.__obj_weights]
    
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

    @property
    def all_clauses(self): 
        return [list(c) for c in self.__hard_clauses + self.__soft_clauses]

    def __str__(self):
        return f"""
        Clauses:
        \t  hard={[list(cl) for cl in self.__hard_clauses]},
        \t  soft={[list(cl) for cl in self.__soft_clauses]},
        \t  Icnf={[list(cl) for cl in self.__Icnf]},
        \t -Icnf={[list(cl) for cl in self.__notIcnf]},
        \tw_soft={self.__soft_weights},
        \t w_obj={self.__obj_weights}
        \t  lits={self.__lits},
        \t cnter={self.h_counter}
        \t
        """

    def __del__(self):
        del self.__hard_clauses
        del self.__soft_clauses
        del self.__soft_weights
        del self.__all_soft_clauses
        del self.__all_soft_idxs
        del self.__all_lits
        del self.__lits
        del self.__Icnf
        del self.__notIcnf
        del self.derived_idxs
        del self.__obj_weights
        del self.h_counter


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