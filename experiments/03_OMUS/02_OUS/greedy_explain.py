import cProfile
from collections import Counter
import pstats
import time
import json
from pathlib import Path
# import random
from functools import wraps
import copy
from itertools import chain, combinations
import signal

from multiprocessing import Process, Pool

# gurobi imports
import gurobipy as gp
from gurobipy import GRB

# pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
from pysat.examples.rc2 import RC2

# datetime object containing current date and time
from datetime import datetime

# Testing samples
from frietkot import originProblem, originProblemReify, pastaPuzzle
from frietkot import simpleProblemReify, simplestProblemReify
from frietkot import simpleProblem
from frietkot import frietKotProblem, frietKotProblemReify


SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES
MODE_OPT, MODE_GREEDY, MODE_INCR = 1, 2, 3

modes = {
    MODE_OPT: "MODE_OPT",
    MODE_GREEDY: "MODE_GREEDY",
    MODE_INCR: "MODE_INCR"
}


def profile(output_file=None, sort_by='cumulative', lines_to_print=None, strip_dirs=False):
    """
    A time profiler decorator.
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




def timeoutHandler(signum, frame):
    raise OUSTimeoutError()


def runParallel(fns, args):
    procs = []
    for fn in fns:
        for arg in args:
            arg_copy = copy.deepcopy(arg)
            p = Process(target=fn, args=(arg_copy,))
            p.start()
            procs.append(p)

    for p in procs:
        p.join()


class BestStepParams(object):
    """
    docstring
    """
    def __init__(self):
        # intialisation: pre-seeding
        self.pre_seeding = False

        # hitting set computation
        self.postpone_opt = False
        self.postpone_opt_incr = False
        self.postpone_opt_greedy = False

        # polarity of sat solver
        self.polarity = False
        self.polarity_initial = False

        # MAXSAT growing
        self.maxsat_polarities = False

        # sat - grow
        self.grow = False
        self.grow_sat = False
        self.grow_subset_maximal = False
        self.subset_maximal_I0 = False
        self.grow_maxsat = False

        # MAXSAT growing
        self.grow_maxsat_full_pos = False
        self.grow_maxsat_full_inv = False
        self.grow_maxsat_full_unif = False
        self.grow_maxsat_initial_pos = False
        self.grow_maxsat_initial_inv = False
        self.grow_maxsat_initial_unif = False
        self.grow_maxsat_actual_pos = False
        self.grow_maxsat_actual_unif = False
        self.grow_maxsat_actual_inv = False

        # timeout
        self.timeout = 2 * HOURS

        # output file
        self.output_folder = "results/" + datetime.now().strftime("%Y%m%d/")
        self.output_file = datetime.now().strftime("%Y%m%d%H%M%S%f.json")

        # instance
        self.instance = ""

    def checkParams(self):
        if self.postpone_opt:
            assert (self.postpone_opt_incr or self.postpone_opt_greedy), "At least one of the two postponing heuristics"

        if self.grow:
            assert self.grow_sat ^ \
                   self.grow_subset_maximal ^ \
                   self.grow_maxsat, \
                   "Exactly 1 grow mechanism"

        if self.grow_maxsat:
            assert self.grow_maxsat_full_pos ^ \
                    self.grow_maxsat_full_inv ^ \
                    self.grow_maxsat_full_unif ^ \
                    self.grow_maxsat_initial_pos ^ \
                    self.grow_maxsat_initial_inv ^ \
                    self.grow_maxsat_initial_unif ^ \
                    self.grow_maxsat_actual_pos ^ \
                    self.grow_maxsat_actual_unif ^ \
                    self.grow_maxsat_actual_inv, \
                   "Only 1 type of maxsat grow."

    def to_dict(self):
        return {
            # preseeding
            "preseeding": self.pre_seeding,
            # sat polarities
            "sat-polarity": self.polarity,
            "sat-polarity-initial": self.polarity_initial,
            # postpone optimisation
            "postpone_opt": self.postpone_opt,
            "postpone_opt_incr": self.postpone_opt_incr,
            "postpone_opt_greedy": self.postpone_opt_greedy,
            # grow type
            "grow": self.grow,
            "grow_sat": self.grow_sat,
            "grow_subset_maximal": self.grow_subset_maximal,
            "grow_maxsat": self.grow_maxsat,
            # maxsat polarities
            "maxsat_polarities": self.maxsat_polarities,
            # maxsat costs
            "grow_maxsat_full_pos": self.grow_maxsat_full_pos,
            "grow_maxsat_full_inv": self.grow_maxsat_full_inv,
            "grow_maxsat_full_unif": self.grow_maxsat_full_unif,
            "grow_maxsat_initial_pos": self.grow_maxsat_initial_pos,
            "grow_maxsat_initial_inv": self.grow_maxsat_initial_inv,
            "grow_maxsat_initial_unif": self.grow_maxsat_initial_unif,
            "grow_maxsat_actual_pos": self.grow_maxsat_actual_pos,
            "grow_maxsat_actual_unif": self.grow_maxsat_actual_unif,
            "grow_maxsat_actual_inv": self.grow_maxsat_actual_inv,
            # run parameters
            "timeout": self.timeout,
            "instance": self.instance,
            "output": self.output_folder+self.output_file
        }

    def __str__(self):
        s = ""
        if self.pre_seeding_subset_minimal:
            s += "pre-seeding-subset-minimal\n"

        if self.pre_seeding_grow:
            s += "pre-seeding-grow-simple\n"

        if self.postpone_opt:
            s += "postpone_opt \n"
        if self.postpone_opt_incr:
            s += "postpone_opt_incr \n"
        if self.postpone_opt_greedy:
            s += "postpone_opt_greedy \n"

        # polarity of sat solver
        if self.polarity:
            s += "polarity \n"
        elif self.polarity_initial:
            s += "polarity-initial interpretation \n"

        # sat - grow
        if self.grow_sat:
            s += "\t grow-sat-model \n"
        if self.grow_subset_maximal:
            s += "\t grow-subset-maximal \n"
        if self.grow_maxsat:
            # TODO add the str version!
            s += "\t grow-MaxSat"
            if self.grow_maxsat_initial_pos:
                s += "-initial_interpretation"
            elif self.grow_maxsat_actual_pos:
                s += "-actual_int_pos"
            elif self.grow_maxsat_actual_inv:
                s += "-actual_int_inv"
            elif self.grow_maxsat_actual_unif:
                s += "-actual_int_unif"
            s += "\n"

        return s


class OusParams(BestStepParams):
    def __init__(self):
        super().__init__()
        self.reuse_SSes = False
        self.sort_literals = False

    def __str__(self):
        s = ""
        if self.postpone_opt:
            s += "postpone_opt \n"
        if self.postpone_opt_incr:
            s += "postpone_opt_incr \n"
        if self.postpone_opt_greedy:
            s += "postpone_opt_greedy \n"

        # polarity of sat solver
        if self.polarity:
            s += "polarity \n"

        # sat - grow
        if self.grow_sat:
            s += "\t grow-sat-model \n"
        if self.grow_subset_maximal:
            s += "\t grow-subset-maximal \n"
        if self.grow_maxsat:
            # TODO add the str version!
            s += "\t grow-MaxSat"
            if self.grow_maxsat_initial_pos:
                s += "-initial_interpretation"
            elif self.grow_maxsat_actual_pos:
                s += "-actual_int_pos"
            elif self.grow_maxsat_actual_inv:
                s += "-actual_int_inv"
            elif self.grow_maxsat_actual_unif:
                s += "-actual_int_unif"
            s += "\n"

        return s

    def to_dict(self):
        super_dict = super().to_dict()
        super_dict.update({
            "reuse_SSes": self.reuse_SSes,
            "reuse_costs": self.reuse_costs
        })
        return super_dict


class OUSTimeoutError(Exception):
    """Exception raised for errors in satisfiability check.

    Attributes:
        I -- partial interpretation given as assumptions
    """
    def __init__(self):
        self.message = f"Ous explain Timeout !"
        super().__init__(self.message)

    def __str__(self):
        return f'{self.message}'


class UnsatError(Exception):
    """Exception raised for errors in satisfiability check.

    Attributes:
        I -- partial interpretation given as assumptions
    """
    def __init__(self, I: set):
        self.I = I
        self.message = f"Partial interpretation is unsat:"
        super().__init__(self.message)

    def __str__(self):
        return f'{self.message}\n\t{self.I}'


class CostFunctionError(Exception):
    """Exception cost function, literal is not in User variables

    Attributes:
        U -- user variables
        lit -- literal
    """
    def __init__(self, U:set, lit: int):
        self.U = U
        self.lit = lit
        self.message = f"Cost function contains literal not in  user vars:"
        super().__init__(self.message)

    def __str__(self):
        return f'{self.message} {self.lit} not in {self.U}'


class BestStepComputer(object):
    def __init__(self, cnf: CNF, sat: Solver, params: OusParams, I0, Iend):
        self.params = params
        self.sat_solver = sat
        self.cnf = cnf
        self.opt_model = None
        self.I0 = I0
        self.I = set()
        self.Iend = Iend

        self.t_expl = {
            't_post': [],
            't_sat': [],
            't_mip': [],
            't_grow': [],
            't_ous': 0,
            '#H':0,
            '#H_greedy': 0,
            '#H_incr': 0,
        }

    def grow(self, f, F, A, HS, HS_model):
        # no actual grow needed if 'HS_model' contains all user vars
        t_grow = time.time()

        if not self.params.grow:
            SS = set(HS)
        elif self.params.grow_sat:
            SS = set(HS_model)
        elif self.params.grow_subset_maximal or self.params.subset_maximal_I0:
            SS = set(self.grow_subset_maximal(A=A, HS=HS, Ap=HS_model))
        elif self.params.grow_maxsat:
            SS = set(self.grow_maxsat(f=f, F=F, A=A, HS=HS))
        else:
            raise NotImplementedError("Grow")
        self.t_expl['t_grow'].append(time.time() - t_grow)
        return SS

    def grow_maxsat(self, f, F, A, HS):
        # print("Growing!", A, HS)
        wcnf = WCNF()

        # add hard clauses of CNF
        wcnf.extend(self.cnf.clauses + [[l] for l in HS])

        # cost is associated for assigning a truth value to literal not in
        # contrary to A.
        remaining = None

        # associate small neg cost to expensive literals
        # intuitively grow the most expensive SS to have cheapest
        # complement
        # unit cost similar to sat call
        # maxsat with initial interpretation
        if self.params.grow_maxsat_initial_pos:
            remaining = self.I0 - HS
            weights = [f(l) for l in remaining]
            wcnf.extend([[l] for l in remaining], weights)
        elif self.params.grow_maxsat_initial_unif:
            remaining = self.I0 - HS
            weights = [1 for l in remaining]
            wcnf.extend([[l] for l in remaining], weights)
        elif self.params.grow_maxsat_initial_inv:
            remaining = self.I0 - HS
            max_weight = max(f(l) for l in remaining)
            weights = [max_weight+1 - f(l) for l in remaining]
            wcnf.extend([[l] for l in remaining], weights)
        # maxsat with actual interpretation
        elif self.params.grow_maxsat_actual_pos:
            remaining = self.I - HS
            weights = [f(l) for l in remaining]
            wcnf.extend([[l] for l in remaining], weights)
        elif self.params.grow_maxsat_actual_unif:
            remaining = self.I - HS
            weights = [1 for l in remaining]
            wcnf.extend([[l] for l in remaining], weights)
        elif self.params.grow_maxsat_actual_inv:
            remaining = self.I - HS
            max_weight = max(f(l) for l in remaining)
            weights = [max_weight+1 - f(l) for l in remaining]
            wcnf.extend([[l] for l in remaining], weights)
        elif self.params.grow_maxsat_full_pos:
            remaining = A - HS
            weights = [f(l) for l in remaining]
            wcnf.extend([[l] for l in remaining], weights)
        elif self.params.grow_maxsat_full_unif:
            remaining = A - HS
            weights = [1 for l in remaining]
            wcnf.extend([[l] for l in remaining], weights)
        elif self.params.grow_maxsat_full_inv:
            remaining = A - HS
            max_weight = max(f(l) for l in remaining)
            weights = [max_weight+1 - f(l) for l in remaining]
            wcnf.extend([[l] for l in remaining], weights)

        with RC2(wcnf) as rc2:
            if self.params.maxsat_polarities:
                rc2.oracle.set_phases(literals=list(self.Iend))
            t_model = rc2.compute()

            return set(t_model)

    def grow_subset_maximal(self, A, HS, Ap):
        _, App = self.checkSat(HS | (self.I0 & Ap), phases=self.I0)
        if self.params.subset_maximal_I0:
            while (Ap != App):
                Ap = set(App)
                _, App = self.checkSat(HS | (self.I0 & Ap), phases=self.I0)

        # repeat until subset maximal wrt A
        while (Ap != App):
            Ap = set(App)
            _, App = self.checkSat(HS | (A & Ap), phases=A)
        return App

    def checkSat(self, Ap: set, phases=set()):
        """Check satisfiability of given assignment of subset of the variables
        of Vocabulary V.
            - If the subset is unsatisfiable, Ap is returned.
            - If the subset is satisfiable, the model computed by the sat
                solver is returned.

        Args:
            Ap (set): Susbet of literals

        Returns:
            (bool, set): sat value, model assignment
        """
        tstart = time.time()
        if self.params.polarity:
            self.sat_solver.set_phases(literals=list(phases - Ap))

        solved = self.sat_solver.solve(assumptions=list(Ap))

        if not solved:
            self.t_expl['t_sat'].append(time.time() - tstart)
            return solved, Ap

        model = set(self.sat_solver.get_model())
        self.t_expl['t_sat'].append(time.time() - tstart)
        return solved, model

    def greedyHittingSet(self, H, f):
        # trivial case: empty
        if len(H) == 0:
            return set()

        # the hitting set
        C = set()

        # build vertical sets
        V = dict()  # for each element in H: which sets it is in

        for i, h in enumerate(H):
            # special case: only one element in the set, must be in hitting set
            # h = hi& A
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
            if -c in V:
                del V[-c]

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
                (c, cover) = max(c_covers, key=lambda tpl: f(tpl[0]))

            del V[c]

            if -c in V:
                del V[-c]

            C.add(c)

            # update vertical views, remove covered sets
            for e in list(V):
                # V will be changed in this loop
                V[e] -= cover
                # no sets remaining with this element?
                if len(V[e]) == 0:
                    del V[e]

        return C

    def next_mode(self, sat, mode):
        # OPT stays OPT
        if not self.params.postpone_opt:
            # print(modes[mode], "->", modes[MODE_OPT])
            return MODE_OPT

        if not sat:
            # INCR -> GREEDY -> OPT
            if mode == MODE_INCR and self.params.postpone_opt_greedy:
                # print(modes[mode], "->", modes[MODE_GREEDY])
                return MODE_GREEDY
            # skip greedy to OPT
        else:
            # SAT: OPT => INCR => GREEDY
            if self.params.postpone_opt_incr:
                # print(modes[mode], "->", modes[MODE_INCR])
                return MODE_INCR
            # SAT: OPT => GREEDY
            elif self.params.postpone_opt_greedy:
                # print(modes[mode], "->", modes[MODE_GREEDY])
                return MODE_GREEDY
        # print(modes[mode], "->", modes[MODE_OPT])
        return MODE_OPT


class BestStepOUSComputer(BestStepComputer):
    """
        Class for computing Optimal Unsatisfiable Subsets given
        a sat solver bootstrapped with a CNF and user variables. Beststep
        computer is implemented based on [1].

        [1]

        Args:
            sat (pysat.Solver): Sat solver bootstrapped with CNF on a
                                vocabulary V.
            U (set): Set of user variables subset of V.
            Iend (set): The cautious consequence, the set of literals that hold in
                        all models.
            I (set): A partial interpretation such that I \subseteq Iend.
            preseeding (bool, optional): [description]. Defaults to True.
        """
    def __init__(self, cnf, sat: Solver, f, Iend: set,  I: set, params: OusParams):
        super().__init__(cnf, sat, params, I0=set(I), Iend=set(Iend))

        # keeping track of the satisfiable subsets
        self.SSes = set()
        self.bestCosts = dict()

        # initialize costs
        Xbest = I | {-l for l in  Iend - I}
        f_xbest = sum(f(l) for l in Xbest)

        # pre-compute the best cost
        for l in Iend - I:
            # initialising the best cost
            self.bestCosts[l] = f_xbest

        # end-interperation
        self.fullSS = set(Iend)

    def bestStep(self, f, Iend, I: set):
        bestExpl, bestLit = None, None
        timings = dict()
        self.I = set(I)
        self.t_expl = {
            't_post': [],
            't_sat': [],
            't_mip': [],
            't_grow': [],
            't_ous': [],
            '#H': 0,
            '#H_greedy': 0,
            '#H_incr': 0,
        }

        tstart_expl = time.time()

        # best cost
        remaining = list(Iend - I)
        for i in I:
            if i in self.bestCosts:
                del self.bestCosts[i]

        if self.params.sort_literals:
            remaining.sort(key=lambda l: self.bestCosts[l])

        bestCost = min(self.bestCosts.values())

        for id, l in enumerate(remaining):
            print(f"OUS lit {id+1}/{len(remaining)+1}", flush=True, end='\r')
            # initialising the best cost
            F = I | {-l, l}

            # expl is None when cutoff (timeout or cost exceeds current best Cost)
            A = I | set({-l})

            expl, costExpl, t_exp = self.bestStepOUS(f, F=F, A=A)

            # can only keep the costs of the optHittingSet computer
            if costExpl < self.bestCosts[l] and expl is not None:
                self.bestCosts[l] = costExpl

            # store explanation
            if costExpl <= bestCost and expl is not None:
                bestExpl = expl
                bestLit = l
                bestCost = costExpl

        self.t_expl["texpl"] = time.time() - tstart_expl
        # literal already found, remove its cost
        del self.bestCosts[bestLit]
        return bestExpl, self.t_expl

    def process_SSes(self, H):
        self.SSes |= H

        # post-processing the MSSes
        keep = set()
        for m1 in self.SSes:
            keep_m1 = True
            for m2 in self.SSes:
                if m1 != m2 and m1 < m2:
                    keep_m1 = False
            if keep_m1:
                keep.add(m1)
        self.SSes = keep

    def computeHittingSet(self, f, HCounter, H, C, HS, mode):
        if mode == MODE_INCR:
            t_incr = time.time()
            hs = set(HS)
            # p-cosntraint validation only 1 of p
            # take the minimum cost literal
            c = min(C, key=lambda l: f(l))
            # find all elements with smallest weight
            m = [ci for ci in C if f(c) == f(c)]
            # choose clause with smallest weight appearing most in H
            c_best = max(m, key=lambda ci: HCounter[ci])
            hs.add(c_best)
            self.t_expl['t_post'].append(time.time() - t_incr)
            self.t_expl['#H_incr'] += 1
            return hs
        elif mode == MODE_GREEDY:
            t_greedy = time.time()
            hs = self.greedyHittingSet(H, f)
            self.t_expl['t_post'].append(time.time() - t_greedy)
            self.t_expl['#H_greedy'] += 1
            return hs
        elif mode == MODE_OPT:
            t_opt = time.time()
            hs = self.optHSComputer.OptHittingSet()
            self.t_expl['t_mip'].append(time.time() - t_opt)
            self.t_expl['#H'] += 1
            return hs

    def bestStepOUS(self, f, F, A):
        tstart = time.time()

        # initial running varaibles
        HCounter = Counter()
        H, HS, C, SSes = set(), set(), set(), set()

        # initial best cost
        bestCost = min(self.bestCosts.values())
        costHS = sum(f(l) for l in A)

        # Start with OPTIMISATION mode
        mode = MODE_OPT

        # OPTIMISATION MODEL
        self.optHSComputer = OptHS(f, F, A)

        # lit to explain!
        lit_expl = next(iter(F - A))

        if self.params.reuse_SSes:
            for SS in self.SSes:
                if SS.issubset(self.fullSS):
                    continue

                if lit_expl not in SS or -lit_expl not in SS:
                    continue

                ss = SS & F

                if any(ss.issubset(MSS) for MSS in SSes):
                    continue

                C = F - ss

                if C not in H:
                    H.add(C)
                    HCounter.update(C)
                    SSes.append(ss)
                    self.optHSComputer.addCorrectionSet(C)

        while(True):
            HS = self.computeHittingSet(f, HCounter, H, C, HS, mode)

            sat, HSModel = self.checkSat(HS, phases=self.I0)

            costHS = sum(f(l) for l in HS)

            if mode == MODE_OPT and costHS > bestCost:
                self.t_expl['t_ous'].append(time.time() - tstart)
                return None, costHS, self.t_expl

            # OUS FOUND?
            if not sat and mode == MODE_OPT:
                self.t_expl['t_ous'].append(time.time() - tstart)
                # cleaning up!
                self.optHSComputer.dispose()

                if self.params.reuse_SSes:
                    self.process_SSes(SSes)

                return HS, costHS, self.t_expl

            mode = self.next_mode(sat, mode)

            if not sat:
                # skip grow!
                continue

            SS = self.grow(f=f, F=F, A=A, HS=HS, HS_model=HSModel)
            C = F - SS
            HCounter.update(C)
            H.add(frozenset(C))
            self.optHSComputer.addCorrectionSet(C)
            if self.params.reuse_SSes:
                SSes.add(frozenset(SS))


class OptHS(object):
    def __init__(self, f, F, A):
        # Iend + -Iexpl
        # print(F)
        # print("I=", [l for l in F if -l not in F])
        # print("Iend/Iexpl=", [l for l in F if -l in F])
        self.allLits = list(F)
        self.nAllLits = len(self.allLits)

        # optimisation model
        self.opt_model = gp.Model('OptHittingSet')

        # model parameters
        self.opt_model.Params.OutputFlag = 0
        self.opt_model.Params.LogToConsole = 0
        self.opt_model.Params.Threads = 1

        # VARIABLE -- OBJECTIVE
        x = self.opt_model.addMVar(
            shape=self.nAllLits,
            vtype=GRB.BINARY,
            obj=[f(l) if l in A else GRB.INFINITY for l in self.allLits],
            name="x")

        self.opt_model.update()

    def addCorrectionSet(self, C: set):
        """Add new constraint of the form to the optimization model,
        mapped back to decision variable lit => x[i].

            sum x[j] * hij >= 1

        Args:
            C (set): set of assumption literals.
        """
        x = self.opt_model.getVars()

        Ci = [self.allLits.index(lit) for lit in C]

        # add new constraint sum x[j] * hij >= 1
        self.opt_model.addConstr(gp.quicksum(x[i] for i in Ci) >= 1)

    def OptHittingSet(self):
        """Compute conditional Optimal hitting set.

        Returns:
            set: Conditional optimal hitting mapped to assumption literals.
        """
        self.opt_model.optimize()

        x = self.opt_model.getVars()
        hs = set(lit for i, lit in enumerate(self.allLits) if x[i].x == 1)

        return hs

    def dispose(self):
        self.opt_model.dispose()


def optimalPropagate(sat, I=set(), U=None):
    """
    optPropage produces the intersection of all models of cnf more precise
    projected on focus.

    Improvements:
    - Extension 1:
        + Reuse solver only for optpropagate
    - Extension 2:
        + Reuse solver for all sat calls
    - Extension 3:
        + Set phases

    Args:
    cnf (list): CNF C over V:
            hard puzzle problems with assumptions variables to activate or
            de-active clues.
    I (list): partial interpretation

    U (list):
        +/- literals of all user variables
    """
    solved = sat.solve(assumptions=list(I))

    if not solved:
        raise UnsatError(I)

    model = set(sat.get_model())
    if U:
        model = set(l for l in model if abs(l) in U)

    bi = sat.nof_vars() + 1

    while(True):
        sat.add_clause([-bi] + [-lit for lit in model])
        solved = sat.solve(assumptions=list(I) + [bi])

        if not solved:
            sat.add_clause([-bi])
            return model

        new_model = set(sat.get_model())
        model = model.intersection(new_model)


def print_timings(t_exp, timedout=False):
    if timedout:
        return

    print("texpl=", round(sum(t_exp['t_ous']), 3), "s\n")
    print("\t#HS Opt:", t_exp['#H'], "\t Incr:", t_exp['#H_incr'], "\tGreedy:", t_exp['#H_greedy'], "\n")

    if len(t_exp['t_mip']) > 1:
        print("\tMIP=\t", round(sum(t_exp['t_mip']), 3), f"s [{round(100*sum(t_exp['t_mip'])/sum(t_exp['t_ous']))}%]\t", "t/call=", round(sum(t_exp['t_mip'])/len(t_exp['t_mip']), 3))
    if len(t_exp['t_post']) > 1:
        print("\tPOST=\t", round(sum(t_exp['t_post']), 3), f"s [{round(100*sum(t_exp['t_post'])/sum(t_exp['t_ous']))}%]\t", "t/call=", round(sum(t_exp['t_post'])/len(t_exp['t_post']), 3))
    if len(t_exp['t_sat']) > 1:
        print("\tSAT=\t", round(sum(t_exp['t_sat']), 3), f"s [{round(100*sum(t_exp['t_sat'])/sum(t_exp['t_ous']))}%]\t", "t/call=", round(sum(t_exp['t_sat'])/len(t_exp['t_sat']), 3))
    if len(t_exp['t_grow']) > 1:
        print("\tGROW=\t", round(sum(t_exp['t_grow']), 3), f"s [{round(100*sum(t_exp['t_grow'])/sum(t_exp['t_ous']))}%]\t", "t/call=", round(sum(t_exp['t_grow'])/len(t_exp['t_grow']), 3))


def saveResults(results, t_exp):
    results["results"]["HS"].append(t_exp["#H"])
    results["results"]["HS_greedy"].append(t_exp["#H_greedy"])
    results["results"]["HS_incr"].append(t_exp["#H_incr"])
    results["results"]["HS-opt-time"].append(sum(t_exp["t_mip"]))
    results["results"]["HS-postpone-time"].append(sum(t_exp["t_post"]))
    results["results"]["OUS-time"].append(t_exp["t_ous"])
    results["results"]["SAT-time"].append(sum(t_exp["t_sat"]))
    results["results"]["grow-time"].append(sum(t_exp["t_grow"]))


def print_expl(matching_table, Ibest):
    if matching_table is None:
        return

    for i in Ibest:
        if(i in matching_table['Transitivity constraint']):
            print("trans", i)
        elif(i in matching_table['Bijectivity']):
            print("bij", i)
        elif(i in matching_table['clues']):
            print("clues n°", matching_table['clues'][i])
        else:
            print("Fact:", i)

@profile(output_file=f'profiles/explain_greedy_{datetime.now().strftime("%Y%m%d%H%M%S")}.prof', lines_to_print=20, strip_dirs=True)
def explainGreedy(C: CNF, U: set, f, I0: set, params: OusParams, verbose=False, matching_table=None):
    """
    ExplainCSP uses hard clauses supplied in CNF format to explain user
    variables with associated weights users_vars_cost based on the
    initial interpretation.

    => hyp: cost is linear

    Args:

        cnf (list): CNF C over a vocabulary V.

        U (set): User vocabulary U subset of V.

        f (list): f is a mapping of user vars to real cost.

        I0 (list): Initial interpretation subset of U.
    """
    params.checkParams()

    if verbose:
        print("Expl:")
        print("\tcnf:", len(C.clauses), C.nv)
        print("\tU:", len(U))
        print("\tf:", f)
        print("\tI0:", len(I0))

    # init experimental results
    # init experimental results
    results = {
        "config": params.to_dict(),
        "results": {
            "HS": [],
            "HS_greedy": [],
            "HS_incr": [],
            "HS-opt-time": [],
            "HS-postpone-time": [],
            "SAT-time": [],
            "grow-time": [],
            "#expl": 0,
            "expl_seq": [],
            "OUS-time": [],
            "timeout": False
        }
    }

    t_expl_start = time.time()
    # check literals of I are all user vocabulary
    assert all(True if abs(lit) in U else False for lit in I0), f"Part of supplied literals not in U (user variables): {lits for lit in I if lit not in U}"

    # Initialise the sat solver with the cnf
    sat = Solver(bootstrap_with=C.clauses)
    assert sat.solve(assumptions=I0), f"CNF is unsatisfiable with given assumptions {I}."

    # Explanation sequence
    E = []

    # Most precise intersection of all models of C project on U
    Iend = optimalPropagate(U=U, I=I0, sat=sat)

    # print(Iend)
    c = BestStepOUSComputer(f=f, cnf=C, sat=sat, Iend=Iend, I=I0, params=params)

    I = set(I0) # copy
    while(len(Iend - I) > 0):
        # remaining_time = params.timeout - (time.time() - t_expl_start)
        # Compute optimal explanation explanation assignment to subset of U.
        expl, t_exp = c.bestStep(f, Iend, I)
        # print(expl)
        # print(t_exp)
        saveResults(results, t_exp)

        if expl is None:
            results["results"]['timeout'] = True
            break

        # facts used

        Ibest = I & expl

        # New information derived "focused" on
        Nbest = optimalPropagate(U=U, I=Ibest, sat=sat) - I
        assert len(Nbest - Iend) == 0

        E.append({
            "constraints": list(Ibest),
            "derived": list(Nbest)
        })

        if verbose:
            print_timings(t_exp)
            print_expl(matching_table, Ibest)
            print(f"\nOptimal explanation \t\t {Ibest} => {Nbest}\n")

        I |= Nbest

        results["results"]["#expl"] += 1

    if verbose:
        print(E)

    results["results"]["expl_seq"] = E
    write_results(results, params.output_folder, params.instance + "_" + params.output_file)
    return E


def to_json_expl(explanation, matching_table, f):
    constraints = list(explanation["constraints"])
    derived = list(explanation["derived"])

    json_explanation = {
        "cost": sum(f(l) for l in constraints),
        "clue": None,
        "assumptions": [],
        "derivations": []
    }

    for fact in derived:
        json_fact = matching_table['bvRel'][abs(fact)]
        json_fact["value"] = True if fact > 0 else False
        json_explanation["derivations"].append(json_fact)

    clue = []
    nTrans = 0
    nBij = 0
    nClue = 0

    for c in constraints:
        if(c in matching_table['Transitivity constraint']):
            nTrans += 1
        elif(c in matching_table['Bijectivity']):
            nBij += 1
        elif(c in matching_table['clues']):
            nClue += 1
            clue.append(matching_table['clues'][c])
        else:
            json_fact = matching_table['bvRel'][abs(c)]
            json_fact["value"] = True if c > 0 else False
            json_explanation["assumptions"].append(json_fact)


    if nClue == 0:
        if nTrans == 0 and nBij == 1:
            json_explanation["clue"] = "Bijectivity"
        elif nTrans == 1 and nBij == 0:
            json_explanation["clue"] = "Transitivity constraint"
        else:
            json_explanation["clue"] = "Combination of logigram constraints"
    elif nClue == 1:
        if nTrans + nBij >= 1:
            json_explanation["clue"] = "Clue and implicit Constraint"
        else:
            json_explanation["clue"] = clue[0]
    else:
        json_explanation["clue"] = "Multiple clues"

    return json_explanation


def write_explanations(explanations, matching_table, f, outputdir, outputfile):
    if not Path(outputdir).parent.exists():
        Path(outputdir).parent.mkdir()
    if not Path(outputdir).exists():
        Path(outputdir).mkdir()
    file_path = Path(outputdir) / outputfile
    json_explanations = []

    for e in explanations:
        json_explanation = to_json_expl(e, matching_table, f)
        json_explanations.append(json_explanation)

    with file_path.open('w') as f:
        json.dump(json_explanations, f)


def write_results(results, outputdir, outputfile):
    print(outputdir)
    print(Path(outputdir).parent)
    print(outputfile)
    if not Path(outputdir).parent.exists():
        Path(outputdir).parent.mkdir()
    if not Path(outputdir).exists():
        Path(outputdir).mkdir()
    file_path = Path(outputdir) / outputfile
    with file_path.open('w') as f:
        json.dump(results, f)


def add_assumptions(cnf):
    flat = set(abs(i) for lst in cnf for i in lst)
    max_lit = max(flat)

    cnf_ass = []
    assumptions = []
    for id, cl in enumerate(cnf):
        ass = max_lit + id + 1
        cl.append(-ass)
        assumptions.append(ass)
        cnf_ass.append(cl)

    return cnf_ass, assumptions


def cost_puzzle(U, I, cost_clue):
    """
    U = user variables
    I = initial intepretation

    bij/trans/clues = subset of user variables w/ specific cost.
    """
    litsU = set(abs(l) for l in U) | set(-abs(l) for l in U)

    I0 = set(I)

    def cost_lit(lit):
        if lit not in litsU:
            raise CostFunctionError(U, lit)
        elif lit in cost_clue:
            return cost_clue[lit]
        else:
            # lit in
            return 1

    return cost_lit


def cost(U, I):
    litsU = set(abs(l) for l in U) | set(-abs(l) for l in U)
    I0 = set(I)

    def cost_lit(lit):
        if lit not in litsU:
            raise CostFunctionError(U, lit)
        elif lit in I0 or -lit in I0:
            return 20
        else:
            return 1

    return cost_lit


def get_user_vars(cnf):
    """Flattens cnf into list of different variables.

    Args:
        cnf (CNF): CNF object

    Returns:
        set: lits of variables present in cnf.
    """
    U = set(abs(l) for lst in cnf.clauses for l in lst)
    return U


def read_json(pathstr):
    f_path = Path(pathstr)
    with f_path.open('r') as fp:
        json_dict = json.load(fp)
    return json_dict


def frietkotGreedy(params):
    f_cnf, f_user_vars = frietKotProblem()
    f_cnf_ass, assumptions = add_assumptions(f_cnf)

    # transform list cnf into CNF object
    frietkot_cnf = CNF(from_clauses=f_cnf_ass)
    U = f_user_vars | set(abs(l) for l in assumptions)
    I = set(assumptions)
    f = cost(U, I)
    explainGreedy(C=frietkot_cnf, U=U, f=f, I0=I, params=params, verbose=True)


def simpleGreedy(params):
    s_cnf = simpleProblem()
    s_cnf_ass, assumptions = add_assumptions(s_cnf)
    # transform list cnf into CNF object
    simple_cnf = CNF(from_clauses=s_cnf_ass)
    U = get_user_vars(simple_cnf)
    I = set(assumptions)
    f = cost(U, I)
    explainGreedy(C=simple_cnf, U=U, f=f, I0=I, params=params, verbose=True)


def puzzleGreedy(params):
    params.instance = "origin-problem"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = originProblem()

    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explainGreedy(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)

if __name__ == "__main__":
    # Translating the explanation sequence generated to website visualisation
    # Execution parameters
    params = OusParams()

    params.pre_seeding = True
    params.polarity = True
    params.reuse_SSes = True
    params.reuse_costs = True

    params.grow = True
    # params.grow_subset_maximal = True
    params.grow_maxsat = True
    params.grow_maxsat_actual_unif = True

    # INSTANCES
    # simpleGreedy(params)
    # frietkotGreedy(params)
    puzzleGreedy(params)
