import pprint
from collections import Counter
import cProfile
import pstats
from functools import wraps
from datetime import datetime

# datetime object containing current date and time

from pysat.formula import WCNF
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
            now = datetime.now().strftime("%Y%m%d_%H%M%S")
            _output_file = output_file or "profiles/" + func.__name__ + "_" + now + '.prof'
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
            self.cOUSModel()
        else:
            self.OUSModel()

    def cOUSModel(self):
        self.opt_model = gp.Model('constrOptHS')

        # model parameters
        self.opt_model.Params.OutputFlag = 0
        self.opt_model.Params.LogToConsole = 0
        self.opt_model.Params.Threads = 1

        # update the model
        x = self.opt_model.addMVar(
            shape=self.clauses.nSoftI,
            vtype=GRB.BINARY,
            obj=self.clauses.obj_weights,
            name="x")

        # exactly one of the -literals
        # TODO: CHANGE THIS!
        vals = self.clauses.not_I_idxs
        self.opt_model.addConstr(x[vals].sum() == 1)

        # at least one of the soft clauses
        # TODO CHANGE THIS !
        vals2 = range(self.clauses.nIndi + self.clauses.nCNFLits)
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
        hs = set(i for i in self.clauses.all_soft_ids if x[i].x == 1)

        return hs

    def set_objective(self):
        x = self.opt_model.getVars()

        for i, xi in enumerate(x):
            xi.setAttr(GRB.Attr.Obj, self.clauses.obj_weights[i])

    def __del__(self):
        self.opt_model.dispose()


class Grower(object):
    def __init__(self, clauses, extension='maxsat'):
        self.clauses = clauses
        self.extension = extension

    def default(self, f_prime, model):
        return f_prime, model

    def maxsat(self, hs_in, model):
        hs = set(hs_in)  # take copy!!
        soft_clauses = self.clauses.all_soft
        soft_weights = self.clauses.all_soft_weights

        wcnf = WCNF()
        wcnf.extend(self.clauses.hard + [soft_clauses[i] for i in hs])

        wcnf.extend(
            [soft_clauses[i] for i in self.clauses.all_soft_ids if i not in hs],
            [soft_weights[i] for i in self.clauses.all_soft_ids if i not in hs]
        )

        with RC2(wcnf) as rc2:
            t_model = rc2.compute()
            if t_model is None:
                return hs, model

            for i, clause in enumerate(soft_clauses):
                if i not in hs and len(set(clause).intersection(t_model)) > 0:
                    hs.add(i)

            return hs, t_model

    def grow(self, f_prime: set, model=set()):
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
        """

        extensions = {
            'default': self.default,
            'maxsat': self.maxsat,
        }

        grown_set, grown_model = extensions[self.extension](f_prime, model)

        return grown_set, grown_model


class OusParams(object):

    def __init__(self):
        self.incremental = False
        self.warm_start = True
        # self.sort_lits = False
        self.constrained = False
        self.bounded = False
        self.post_opt = False
        self.post_opt_incremental = False
        self.post_opt_greedy = False
        self.benchmark = False
        self.ispuzzle = True
        self.outputFile = ''
        self.timeout = None
        self.extension = 'maxsat'

    def __repr__(self):
        return {
            'warm_start': self.warm_start,
            'constrained': self.constrained,
            "incremental": self.incremental,
            'bounded': self.bounded,
            # 'sort_lits': self.sort_lits,
            'extension': self.extension,
            'post_opt': self.post_opt,
            'post_opt_incremental': self.post_opt_incremental,
            'post_opt_greedy': self.post_opt_greedy,
            'benchmark': self.benchmark,
            'puzzle': self.ispuzzle,
            'output': self.outputFile,
            'timeout': self.timeout,
        }


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