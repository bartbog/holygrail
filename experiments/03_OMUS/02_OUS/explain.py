import cProfile
from collections import Counter
import pstats
import time
import json
from pathlib import Path
# import random
from functools import wraps
import copy
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
from frietkot import originProblem, originProblemReify, p12, p13, p16, p18, p19, p20, p25, p93, pastaPuzzle
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


def timeoutHandler(signum, frame):
    raise OUSTimeoutError()


class COusParams(object):
    """
    docstring
    """
    def __init__(self):
        # reinitialising the HS solver at every OUS call
        self.disableConstrained = False

        # intialisation: pre-seeding
        self.pre_seeding = False

        # hitting set computation
        self.postpone_opt = False
        self.postpone_opt_incr = False
        self.postpone_opt_greedy = False

        # polarity of sat solver
        self.polarity = False
        self.polarity_initial = False

        # sat - grow
        self.grow = False
        self.grow_sat = False
        self.grow_subset_maximal_actual = False
        self.grow_subset_maximal = False
        self.subset_maximal_I0 = False
        self.grow_maxsat = False

        # MAXSAT growing
        self.maxsat_polarities = False

        #type of grow
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
                   self.subset_maximal_I0 ^ \
                   self.grow_subset_maximal_actual ^ \
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
            "disableConstrained": self.disableConstrained,
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
            "grow_subset_maximal_actual": self.grow_subset_maximal_actual,
            "grow_maxsat": self.grow_maxsat,
            # maxsat polarities
            "maxsat_polarities":self.maxsat_polarities,
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


class MaxSatExtensionError(Exception):
    """Exception raised for errors in satisfiability check.

    Attributes:
        I -- partial interpretation given as assumptions
    """
    def __init__(self, params):
        self.message = f"Wrong Maxsat extension.\nParams:\n\n" + str(params.to_dict())
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


class BestStepCOUSComputer(object):
    """
        Class for computing conditional Optimal Unsatisfiable Subsets given
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
    def __init__(self, sat: Solver, f, U: set, Iend: set, I: set, params: COusParams, cnf: CNF = None):
        """
            Constructor.
        """
        # Execution parameters
        self.sat_solver = sat
        self.params = params
        self.cnf = cnf

        # Optimisation model
        self.opt_model = CondOptHS(U=U, Iend=Iend, I=I)

        # initial values
        self.I0 = set(I)
        self.I = set(I)
        self.U = set(U) | set(-l for l in U)
        self.Iend = set(Iend)

        # Current formula
        A = self.I0 | {-l for l in Iend-I}

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

        F = set(l for l in U) | set(-l for l in U)
        F -= set(-l for l in I)

        if self.params.pre_seeding:
            print("Warm start!")

            Ap = Iend # satisfiable subset

            # ensures at least one of the -lits in HS
            C = F - Ap
            self.opt_model.addCorrectionSet(C)

            seedable = set(-i for i in Iend - I)
            tottime = 0

            while len(seedable) > 0:
                l = next(iter(seedable))

                # print(f"Seeding {l} [{len(seedable)} remaining]")

                HS = set({l})
                _, Ap = self.checkSat(Ap=HS, phases=Iend)
                tsartseed = time.time()
                if self.params.grow:
                    SS = self.grow(f, F=F, A=A, HS=HS, HS_model=Ap)
                else:
                    SS = Ap
                tendseed = time.time() - tsartseed
                # print("Time grow {l}:", round(tendseed), "s")
                tottime += tendseed
                C = frozenset(F - SS)

                self.opt_model.addCorrectionSet(C)

                other_seeds = seedable & frozenset(SS)
                # no need to 'grow' a literal that already has an MSS
                seedable -= other_seeds
            # print("Finished pre-seeding, tottime =", round(tottime), "s")

    def bestStep(self, f, U: set, Iend: set, I: set):
        """
        bestStep computes a subset A' of A that satisfies p s.t.
        C u A' is UNSAT and A' is f-optimal.

        Args:

            f (list): A cost function mapping 2^A -> N.
            Iend (set): The cautious consequence, the set of literals that hold in
                        all models.
            I (set): A partial interpretation such that I \subseteq Iend.
            sat (pysat.Solver): A SAT solver initialized with a CNF.
        """
        self.I = set(I)
        Iexpl = Iend - I
        F = set(l for l in U) | set(-l for l in U)
        F -= {-l for l in I}
        # print("F=", F)
        p = {-l for l in Iexpl}

        A = I | {-l for l in Iexpl}
        return self.bestStepCOUS(f, F, A, p=p)

    def grow(self, f, F, A, HS, HS_model):
        # no actual grow needed if 'HS_model' contains all user vars
        t_grow = time.time()

        if not self.params.grow:
            SS = set(HS)
        elif self.params.grow_sat:
            SS = set(HS_model)
        elif self.params.grow_subset_maximal_actual:
            SS = set(self.grow_subset_maximal_actual(HS=HS, Ap=HS_model))
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
        else:
            raise MaxSatExtensionError()

        with RC2(wcnf) as s:
            # mistery error
            if self.params.maxsat_polarities and hasattr(s, 'oracle'):
                s.oracle.set_phases(literals=list(self.Iend))
            t_model = s.compute()
            if t_model is None:
                return HS

            return set(t_model)

    def grow_subset_maximal_actual(self,  HS, Ap):
        _, App = self.checkSat(HS | (self.I & Ap), phases=self.I)
        # repeat until subset maximal wrt A
        while (Ap != App):
            Ap = set(App)
            sat, App = self.checkSat(HS | (self.I & Ap), phases=self.I)
        # print("\tgot sat", sat, len(App))
        return App

    def grow_subset_maximal(self, A, HS, Ap):
        _, App = self.checkSat(HS | (self.I0 & Ap), phases=self.I0)
        if self.params.subset_maximal_I0:
            while (Ap != App):
                Ap = set(App)
                _, App = self.checkSat(HS | (self.I0 & Ap), phases=self.I0)

        # repeat until subset maximal wrt A
        while (Ap != App):
            Ap = set(App)
            sat, App = self.checkSat(HS | (A & Ap), phases=A)
        # print("\tgot sat", sat, len(App))
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
        t_sat = time.time()
        if self.params.polarity_initial:
            self.sat_solver.set_phases(literals=list(self.I0 - Ap))
        elif self.params.polarity:
            self.sat_solver.set_phases(literals=list(self.Iend - Ap))

        solved = self.sat_solver.solve(assumptions=list(Ap))

        if not solved:
            self.t_expl['t_sat'].append(time.time() - t_sat)
            return solved, Ap

        model = set(self.sat_solver.get_model())

        self.t_expl['t_sat'].append(time.time() - t_sat)
        return solved, model

    def greedyHittingSet(self, H, A, f, p):
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

    def ConstrainedGreedyHittingSet(self, H, A, f, p):
        hC = Counter(H)
        #TODO: need to be smarter only 1 of p !!!
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

        # make sure p constriant is validated
        if len(p & C) == 0:
            Vp = {key: V[key] for key in V.keys() & p}
            if len(Vp) > 0:
                (c, cover) = max(Vp.items(), key=lambda tpl: len(tpl[1]))
                c_covers = [tpl for tpl in Vp.items() if len(tpl[1]) == len(cover)]

                if len(c_covers) > 1:
                    (c, cover) = min(c_covers, key=lambda tpl: f(tpl[0]))

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
            else:
                # C cannot contain p and -p
                pNotC = p - {-l for l in C}
                if len(pNotC) > 0:
                    c = min(pNotC, key=lambda l: f(l))
                else:
                    c = min(p, key=lambda l: f(l))
                C.add(c)
        # only select 1!
        else:
            # remove rest of elems of p
            for e in V.keys() & p:
                # don't need to remove -e can be added
                del V[e]

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
                (c, cover) = min(c_covers, key=lambda tpl: f(tpl[0]))

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

        if len(C) == 1:
            c = max(A-p - C, key= lambda l: hC[l])
            C.add(c)
        return C

    def computeHittingSet(self, F, A, f, p, H, C, HS, mode):
        if mode == MODE_INCR:
            t_incr = time.time()
            hs = set(HS)
            # p-cosntraint validation only 1 of p
            # take the minimum cost literal
            if len(p & hs) > 0:
                # cannot select lit that is in p already and already in hs
                selectable = C - (hs | {-l for l in hs} | p)
            else:
                selectable = p - {-l for l in hs}

            if len(selectable) > 0:
                c = min(selectable, key=lambda l: f(l))
            else:
                c = min(F - HS, key=lambda l: f(l))

            hs.add(c)
            self.t_expl['t_post'].append(time.time() - t_incr)
            self.t_expl['#H_incr'] += 1
            return hs
        elif mode == MODE_GREEDY:
            # print("Greedy")
            t_greedy = time.time()
            hs = self.greedyHittingSet(H, A, f, p)
            self.t_expl['t_post'].append(time.time() - t_greedy)
            self.t_expl['#H_greedy'] += 1
            return hs
        elif mode == MODE_OPT:
            t_opt = time.time()
            # print("Opt!")
            hs = self.opt_model.CondOptHittingSet()
            self.t_expl['t_mip'].append(time.time() - t_opt)
            self.t_expl['#H'] += 1
            return hs

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

    def bestStepCOUS(self, f, F, A: set, p):
        """Given a set of assumption literals A subset of F, bestStepCOUS
        computes a subset a subset A' of A that satisfies p s.t C u A' is
        UNSAT and A' is f-optimal based on [1].

        Args:
            f (func): Cost function mapping from lit to int.
            F (set): Set of literals I + (Iend \\ I)) + (-Iend \\ -I).
            A (set): Set of assumption literals I + (-Iend \\ -I).

        Returns:
            set: a subset A' of A that satisfies p s.t C u A' is UNSAT
                 and A' is f-optimal.
        """
        self.t_expl = {
            't_post': [0],
            't_sat': [0],
            't_mip': [0],
            't_grow': [0],
            't_ous': 0,
            '#H':0,
            '#H_greedy': 0,
            '#H_incr': 0,
        }

        tstart = time.time()

        # UPDATE OBJECTIVE WEIGHTS
        self.opt_model.updateObjective(f, A)

        # VARIABLE INITIALISATION
        H, C, HS, SS = list(), set(), set(), set()
        mode = MODE_OPT

        while(True):
            # COMPUTING OPTIMAL HITTING SET
            HS = self.computeHittingSet(f=f, F=F, A=A, p=p, H=H, C=C, HS=HS, mode=mode)

            # Timings

            # CHECKING SATISFIABILITY
            sat, HS_model = self.checkSat(HS, phases=self.I0)

            # OUS FOUND?
            if not sat and mode == MODE_OPT:
                self.t_expl['t_ous'] = time.time() - tstart
                return HS

            mode = self.next_mode(sat, mode)

            if not sat:
                # skip grow!
                continue

            # XXX Idea for grow- skip the grow when incremental!
            SS = self.grow(f, F, A, HS, HS_model)
            C = F - SS

            # ADD COMPLEMENT TO HITTING SET OPTIMISATION SOLVER
            H.append(C)
            self.opt_model.addCorrectionSet(C)

    def __del__(self):
        """Ensure sat solver is deleted after garbage collection.
        """
        self.opt_model.__del__()


class CondOptHS(object):
    def __init__(self, U: set, Iend: set, I: set):
        """
        # Optimisation model:

        The constrained optimal hitting set is described by:

        - x_l={0,1} is a boolean decision variable if the literal is selected
                    or not.

        - w_l=f(l) is the cost assigned to having the literal in the hitting
                   set (INF otherwise).

        - c_lj={0,1} is 1 (0) if the literal l is (not) present in hitting set j.

        Objective:

             min sum(x_l * w_l) over all l in Iend + (-Iend \ -I)

        Subject to:

            (1) sum x_l * c_lj >= 1 for all hitting sets j.

                = Hitting set must hit all sets-to-hit.

            (2) sum x_l == 1 for l in (-Iend \ -I)

        Args:

            U (set): User variables over a vocabulary V

            Iend (set): Cautious consequence, the set of literals that hold in
                        all models.

            I (set): partial interpretation subset of Iend.

        """
        Iexpl = Iend - I
        notIexpl = set(-lit for lit in Iexpl)

        # Iend + -Iexpl
        # print("I=", [l for l in F if -l not in F])
        # print("Iend/Iexpl=", [l for l in F if -l in F])

        self.allLits = list(Iend) + list(notIexpl)
        self.nAllLits = len(self.allLits)

        # optimisation model
        self.opt_model = gp.Model('CondOptHittingSet')

        # model parameters
        self.opt_model.Params.OutputFlag = 0
        self.opt_model.Params.LogToConsole = 0
        self.opt_model.Params.Threads = 1

        # VARIABLE -- OBJECTIVE
        x = self.opt_model.addMVar(
            shape=self.nAllLits,
            vtype=GRB.BINARY,
            obj=[GRB.INFINITY] * self.nAllLits,
            name="x")

        # CONSTRAINTS
        # every explanation contains 1 neg Lit.
        posnegIexpl = range(len(Iend), self.nAllLits)

        self.opt_model.addConstr(
            x[posnegIexpl].sum() == 1
        )

        # update model
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

    def CondOptHittingSet(self):
        """Compute conditional Optimal hitting set.

        Returns:
            set: Conditional optimal hitting mapped to assumption literals.
        """
        self.opt_model.optimize()

        x = self.opt_model.getVars()
        hs = set(lit for i, lit in enumerate(self.allLits) if x[i].x == 1)

        return hs

    def updateObjective(self, f, A: set):
        """Update objective of subset A {I + (-Iend\-I )}, a set of assumption
        literals s.t C u A is unsatisfiable.

        Costs of literals in A should be set to f(lit) and others not in A,
        should be set to INF.

        Args:
            f (func): A cost function mapping literal to a int cost (> 0).
            A (set): A set of assumption literals.
        """
        x = self.opt_model.getVars()

        # update the objective weights
        for xi, lit in zip(x, self.allLits):
            if lit in A:
                xi.setAttr(GRB.Attr.Obj, f(lit))
            else:
                xi.setAttr(GRB.Attr.Obj, GRB.INFINITY)

        self.opt_model.update()

    def __del__(self):
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

    print("texpl=", round(t_exp['t_ous'], 3), "s\n")
    print("\t#HS Opt:", t_exp['#H'], "\t Incr:", t_exp['#H_incr'], "\tGreedy:", t_exp['#H_greedy'], "\n")

    if len(t_exp['t_mip']) > 1:
        print("\tMIP=\t", round(sum(t_exp['t_mip']), 3), f"s [{round(100*sum(t_exp['t_mip'])/t_exp['t_ous'])}%]\t", "t/call=", round(sum(t_exp['t_mip'])/len(t_exp['t_mip']), 3))
    if len(t_exp['t_post']) > 1:
        print("\tPOST=\t", round(sum(t_exp['t_post']), 3), f"s [{round(100*sum(t_exp['t_post'])/t_exp['t_ous'])}%]\t", "t/call=", round(sum(t_exp['t_post'])/len(t_exp['t_post']), 3))
    if len(t_exp['t_sat']) > 1:
        print("\tSAT=\t", round(sum(t_exp['t_sat']), 3), f"s [{round(100*sum(t_exp['t_sat'])/t_exp['t_ous'])}%]\t", "t/call=", round(sum(t_exp['t_sat'])/len(t_exp['t_sat']), 3))
    if len(t_exp['t_grow']) > 1:
        print("\tGROW=\t", round(sum(t_exp['t_grow']), 3), f"s [{round(100*sum(t_exp['t_grow'])/t_exp['t_ous'])}%]\t", "t/call=", round(sum(t_exp['t_grow'])/len(t_exp['t_grow']), 3))


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


# @profile(output_file=f'profiles/explain_{datetime.now().strftime("%Y%m%d%H%M%S")}.prof', lines_to_print=20, strip_dirs=True)
def explain(C: CNF, U: set, f, I0: set, params: COusParams, verbose=False, matching_table=None):
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
    assert all(True if abs(lit) in U else False for lit in I0), f"Part of supplied literals not in U (user variables): {lits for lit in I0 if lit not in U}"

    # Initialise the sat solver with the cnf
    sat = Solver(bootstrap_with=C.clauses)
    assert sat.solve(assumptions=I0), f"CNF is unsatisfiable with given assumptions {I}."

    # Explanation sequence
    E = []

    # Most precise intersection of all models of C project on U
    Iend = optimalPropagate(U=U, I=I0, sat=sat)

    # TIMEOUT Handler!
    remaining_time = round(params.timeout - (time.time() - t_expl_start))
    _ = signal.signal(signal.SIGALRM, timeoutHandler)

    # ensure max-time is not exceeded!
    signal.alarm(remaining_time)

    try:
        c = BestStepCOUSComputer(f=f, sat=sat, U=U, Iend=Iend, I=I0, params=params, cnf=C)
    # only handling timeout error!
    except OUSTimeoutError:
        print("Pre-seeding timeout !")
        write_results(results, params.output_folder, params.instance + "_" + params.output_file)
        return E

    # keeping track of the timings
    t_exp = c.t_expl
    saveResults(results, t_exp)

    signal.alarm(0)

    I = set(I0) # copy
    while(len(Iend - I) > 0):
        # ensure timeout in cOUS ocmputation
        remaining_time = round(params.timeout - (time.time() - t_expl_start))

        if remaining_time <= 0:
            results["results"]['timeout'] = True
            break

        signal.alarm(remaining_time)

        # Compute optimal explanation explanation assignment to subset of U.
        expl_found = True
        try:
            expl = c.bestStep(f, U, Iend, I)
        # only handling timeout error!
        except OUSTimeoutError:
            expl_found = False
        finally:
            # ensure we don't get a timeout outside
            signal.alarm(0)

            # keeping track of the timings
            t_exp = c.t_expl
            saveResults(results, t_exp)

        if verbose:
            print_timings(t_exp, not expl_found)

        if not expl_found:
            results["results"]['timeout'] = True
            break

        # facts used
        Ibest = I & expl

        # New information derived "focused" on
        Nbest = optimalPropagate(U=U, I=Ibest, sat=sat) - I
        assert len(Nbest - Iend) == 0

        E.append({
            "constraints": list(Ibest),
            "derived": list(Nbest),
            "cost": sum(f(l) for l in Ibest)
        })

        if verbose:
            print_expl(matching_table, Ibest)
            qual = sum([f(l) for l in Ibest])
            print(f"\nOptimal explanation \t\t {Ibest} => {Nbest} \t (cost: {qual})\n")

        I |= Nbest

        results["results"]["#expl"] += 1

        if params.disableConstrained:
            c.__del__()
            remaining_time = round(params.timeout - (time.time() - t_expl_start))
            if remaining_time <= 0:
                results["results"]['timeout'] = True
                break

            # ensure max-time is not exceeded!
            signal.alarm(remaining_time)

            try:
                c = BestStepCOUSComputer(f=f, sat=sat, U=U, Iend=Iend, I=I, params=params, cnf=C)
            # only handling timeout error!
            except OUSTimeoutError:
                break
            finally:
                signal.alarm(0)
                # keeping track of the timings
                t_exp = c.t_expl
                saveResults(results, t_exp)

    if verbose:
        print(E)

    results["results"]["expl_seq"] = E
    write_results(results, params.output_folder, params.instance + "_" + params.output_file)

    # produce some explanation file to be visualised
    if matching_table:
        write_explanations(E, matching_table, f, params.output_folder, params.instance + datetime.now().strftime("%Y%m%d%H%M%S%f") + ".output.json")

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
    # print(outputdir)
    # print(Path(outputdir).parent)
    # print(outputfile)
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


def test_frietkot(params):
    params.instance = "frietkot"

    f_cnf, f_user_vars = frietKotProblem()
    f_cnf_ass, assumptions = add_assumptions(f_cnf)

    # transform list cnf into CNF object
    frietkot_cnf = CNF(from_clauses=f_cnf_ass)
    U = f_user_vars | set(abs(l) for l in assumptions)
    I = set(assumptions)
    f = cost(U, I)
    explain(C=frietkot_cnf, U=U, f=f, I0=I, params=params)


def test_puzzle(params):
    params.instance = "origin-problem"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = originProblem()
    
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


def test_p19Puzzle(params):
    params.instance = "p19"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = p19()

    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    with Solver(bootstrap_with=o_clauses + o_assumptions) as s:
        sat = s.solve()
        print(sat)
        prev = None
        for id, m in enumerate(s.enum_models()):
            print(f"{id}: model found")
            if not prev is None:
                print("diff", sorted(set(prev) - set(m), key=lambda l: abs(l)))
            prev = m
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


def test_p93Puzzle(params):
    params.instance = "p93"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = p93()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


def test_p20Puzzle(params):
    params.instance = "p20"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = p20()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


def test_p25Puzzle(params):
    params.instance = "p25"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = p25()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


def test_p18Puzzle(params):
    params.instance = "p18"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = p18()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


def test_p16Puzzle(params):
    params.instance = "p16"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = p16()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


def test_p13Puzzle(params):
    params.instance = "p13"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = p13()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


def test_p12Puzzle(params):
    params.instance = "p12"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = p12()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


def test_PastaPuzzle(params):
    params.instance = "pasta"
    o_clauses, o_assumptions, o_weights, o_user_vars, matching_table = pastaPuzzle()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    print()
    return
    explain(C=o_cnf, U=U, f=f, I0=I, params=params, matching_table=matching_table, verbose=True)


def test_explain(params):
    params.instance = "simple"
    # test on simple case
    s_cnf = simpleProblem()
    s_cnf_ass, assumptions = add_assumptions(s_cnf)
    # transform list cnf into CNF object
    simple_cnf = CNF(from_clauses=s_cnf_ass)
    U = get_user_vars(simple_cnf)
    I = set(assumptions)
    f = cost(U, I)
    explain(C=simple_cnf, U=U, f=f, I0=I, params=params, verbose=True)


def test_simplestReify(params):
    cnf, assumptions, U = simplestProblemReify()
    simple_cnf = CNF(from_clauses=cnf)
    U = set(U) | set(assumptions)
    I = set(assumptions)
    f = cost(U, I)
    explain(C=simple_cnf, U=U, f=f, I0=I, params=params)


def test_simpleReify(params):
    cnf, assumptions, U = simpleProblemReify()
    simple_cnf = CNF(from_clauses=cnf)
    U = set(U) | set(assumptions)
    I = set(assumptions)
    f = cost(U, I)
    explain(C=simple_cnf, U=U, f=f, I0=I, params=params)


def test_frietkotReify(params):
    cnf, assumptions, U = frietKotProblemReify()
    simple_cnf = CNF(from_clauses=cnf)
    U = set(U) | set(assumptions)
    I = set(assumptions)
    f = cost(U, I)
    explain(C=simple_cnf, U=U, f=f, I0=I, params=params)


def test_puzzleReify(params):
    params.instance = "origin-problem-Reify"
    o_clauses, o_assumptions, o_weights, o_user_vars = originProblemReify()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params)

if __name__ == "__main__":
    # Translating the explanation sequence generated to website visualisation
    # d = read_json("expl_seq.json")
    # write_explanations(d["results"]["expl_seq"], matching_table, f, './', 'explanatons_puzzle.json')

    # runParallel(fns, all_params)
    optimalParams = COusParams()
    # preseeding
    optimalParams.pre_seeding = False
    # params.pre_seeding_subset_minimal = True

    # polarity of sat solver
    # params.polarity = True
    optimalParams.polarity = True

    # sat - grow
    optimalParams.grow = True
    optimalParams.grow_subset_maximal_actual = True
    # optimalParams.grow_maxsat = True
    # optimalParams.grow_maxsat_initial_pos = True
    # optimalParams.grow_maxsat_actual_pos = True

    # timeout
    # optimalParams.timeout = 1 * MINUTES

    params = COusParams()
    # preseeding
    params.pre_seeding = True
    # params.pre_seeding_subset_minimal = True

    # polarity of sat solver
    params.polarity = True
    # params.polarity_initial = True

    # sat - grow
    params.grow = True
    params.grow_maxsat = True
    # params.grow_subset_maximal= True

    # max cost neg => fast pre-seeding! (0s)
    # params.grow_maxsat_max_cost_neg = True
    # unit => SLOW pre-seeding! (325s)
    # params.grow_maxsat_unit = True
    # pos cost => FAST pre-seeding! (6s)
    # params.grow_maxsat_pos_cost = True
    # neg cost => very fast pre-seeding! (0s)
    # params.grow_maxsat_neg_cost = True
    # initial cost => FAST pre-seeding!
    # params.grow_maxsat_initial_pos = True

    ## Postponing Hitting set solver call
    # params.postpone_opt = True
    # params.postpone_opt_incr = True
    # params.postpone_opt_greedy = True

    # timeout
    params.timeout = 30*SECONDS

    ## INSTANCES
    # test_explain(params)
    # test_frietkot(params)
    # test_puzzle(params)
    # test_puzzle(optimalParams)
    # test_PastaPuzzle(optimalParams)
    # test_PastaPuzzle(optimalParams)
    # test_p12Puzzle(optimalParams)
    # test_p13Puzzle(optimalParams)
    # test_p16Puzzle(optimalParams)
    # test_p18Puzzle(optimalParams)
    test_puzzle(optimalParams)
    # test_p25(optimalParams)
    # test_p20(optimalParams)
    # test_p93(optimalParams)
    # test_simplestReify(params)
    # test_simpleReify(params)
    # test_puzzleReify(params)
