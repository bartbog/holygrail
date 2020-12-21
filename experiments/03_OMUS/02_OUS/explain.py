import cProfile
from collections import Counter
import pstats
import time
import json
from pathlib import Path
# import random
from functools import wraps
import os
import copy

from multiprocessing import Process, Pool

# gurobi imports
import gurobipy as gp
from gurobipy import GRB

# pysat imports
from pysat.formula import CNF, WCNF, WCNFPlus
from pysat.solvers import Solver
from pysat.examples.rc2 import RC2
from pysat.examples.musx import MUSX

from datetime import datetime

# datetime object containing current date and time

# Testing samples
from frietkot import originProblem, originProblemReify
from frietkot import simpleProblemReify, simplestProblemReify
from frietkot import simpleProblem
from frietkot import frietKotProblem, frietKotProblemReify

from datetime import datetime

SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES
MODE_OPT, MODE_GREEDY, MODE_INCR = 1, 2, 3

modes = {
    MODE_OPT: "MODE_OPT",
    MODE_GREEDY: "MODE_GREEDY",
    MODE_INCR: "MODE_INCR"
}


def smap(f, args):
    print(args)
    print(f)
    return f(args)


def runPool(fn, args):
    nprocs = 8
    if "PBS_NP" in os.environ:
        nprocs = int(os.environ["PBS_NP"])

    with Pool(processes=nprocs) as pool:
        pool.map(fn, args)


def runParallel(fns, args):
    procs = []
    for fn in fns:
        for arg in args:
            arg_copy = copy.deepcopy(arg)
            p = Process(target=fn, args=(arg,))
            p.start()
            procs.append(p)

    for p in procs:
        p.join()


class COusParams(object):
    """
    docstring
    """
    def __init__(self):
        # intialisation: pre-seeding
        self.pre_seeding = False
        self.pre_seeding_subset_minimal = False
        self.pre_seeding_grow = False
        self.pre_seeding_grow_maxsat = False

        # hitting set computation
        self.postpone_opt = False
        self.postpone_opt_incr = False
        self.postpone_opt_greedy = False

        # polarity of sat solver
        self.polarity = False

        # sat - grow
        self.grow = False
        self.grow_sat = False
        self.grow_subset_maximal = False
        self.grow_maxsat = False

        self.grow_maxsat_neg_cost = False
        self.grow_maxsat_pos_cost = False
        self.grow_maxsat_max_cost_neg = False
        self.grow_maxsat_unit = False

        self.grow_skip_incremental = False
        self.grow_skip_greedy = False

        # timeout
        self.timeout = 24 * HOURS

        # output file
        self.output_folder = "results/" + datetime.now().strftime("%Y%m%d/")
        self.output_file = datetime.now().strftime("%Y%m%d%H%M%S%f.json")

        # instance
        self.instance = ""

    def checkParams(self):
        if self.postpone_opt:
            assert (self.postpone_opt_incr or self.postpone_opt_greedy), "At least one of the two postponing heuristics"

        if self.grow:
            assert self.grow_sat ^ self.grow_subset_maximal ^ self.grow_maxsat, "Exactly 1 grow mechanism"

    def to_dict(self):
        return {
            "preseeding": self.pre_seeding,
            "preseeding-minimal": self.pre_seeding_subset_minimal,
            "preseeding-grow": self.pre_seeding_grow,
            "preseeding-grow-maxsat": self.pre_seeding_grow_maxsat,
            "sat-polarity": self.polarity,
            "postpone_opt": self.postpone_opt,
            "postpone_opt_incr": self.postpone_opt_incr,
            "postpone_opt_greedy": self.postpone_opt_greedy,
            "grow": self.grow,
            "grow_sat": self.grow_sat,
            "grow_subset_maximal": self.grow_subset_maximal,
            "grow_maxsat": self.grow_maxsat,
            "timeout": self.timeout,
            "instance": self.instance,
            "output": self.output_folder+self.output_file,
        }
    def __str__(self):
        s = ""
        if self.pre_seeding_subset_minimal:
            s += "pre-seeding-subset-minimal\n"

        if self.pre_seeding_grow:
            s += "pre-seeding-grow-simple\n"

        if self.pre_seeding_grow_maxsat:
            s += "pre-seeding-grow-maxsat \n"

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
            s += "\t grow-MaxSat"
            if self.grow_maxsat_neg_cost:
                s += "-neg_cost"
            elif self.grow_maxsat_pos_cost:
                s += "-pos_cost"
            elif self.grow_maxsat_max_cost_neg:
                s += "-max_cost_neg"
            elif self.grow_maxsat_unit:
                s += "-unit_cost"
            s += "\n"

        return s


class OusParams(COusParams):
    def __init__(self):
        super().__init__()
        self.reuse_SSes = False
        self.reuse_costs = False

    def __str__(self):
        s = ""
        if self.pre_seeding_subset_minimal:
            s += "pre-seeding-subset-minimal\n"

        if self.pre_seeding_grow:
            s += "pre-seeding-grow-simple\n"

        if self.pre_seeding_grow_maxsat:
            s += "pre-seeding-grow-maxsat \n"

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
            s += "\t grow-MaxSat"
            if self.grow_maxsat_neg_cost:
                s += "-neg_cost"
            elif self.grow_maxsat_pos_cost:
                s += "-pos_cost"
            elif self.grow_maxsat_max_cost_neg:
                s += "-max_cost_neg"
            elif self.grow_maxsat_unit:
                s += "-unit_cost"
            s += "\n"

        return s

    def to_dict(self):
        return {
            "preseeding": self.pre_seeding,
            "preseeding-minimal": self.pre_seeding_subset_minimal,
            "preseeding-grow": self.pre_seeding_grow,
            "preseeding-grow-maxsat": self.pre_seeding_grow_maxsat,
            "sat-polarity": self.polarity,
            "postpone_opt": self.postpone_opt,
            "postpone_opt_incr": self.postpone_opt_incr,
            "postpone_opt_greedy": self.postpone_opt_greedy,
            "grow": self.grow,
            "grow_sat": self.grow_sat,
            "grow_subset_maximal": self.grow_subset_maximal,
            "grow_maxsat": self.grow_maxsat,
            "timeout": self.timeout,
            "instance": self.instance,
            "output": self.output_folder+self.output_file,
        }


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
    def __init__(self, cnf: CNF, sat: Solver, params, I0):
        self.params = params
        self.sat_solver = sat
        self.cnf = cnf
        self.opt_model = None
        self.I0 = I0

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
        elif self.params.grow_subset_maximal:
            SS = set(self.grow_subset_maximal(A=A, HS=HS, Ap=HS_model))
        elif self.params.grow_maxsat:
            SS = set(self.grow_maxsat(f=f, F=F, A=A, HS=HS))
        else:
            raise NotImplementedError("Grow")
        self.t_expl['t_grow'].append(time.time() - t_grow)
        return SS

    def grow_maxsat(self, f, F, A, HS):
        wcnf = WCNF()

        # add hard clauses of CNF
        wcnf.extend(self.cnf.clauses + [[l] for l in HS])

        # TODO: is this really correct ? A - HS ? add soft clasues => F - HS
        remaining = A - HS
        wcnf.extend([[l] for l in remaining], [-f(l) for l in remaining])

        with RC2(wcnf) as rc2:
            t_model = rc2.compute()

            if t_model is None:
                return set(HS)

            return set(t_model)

    def grow_subset_maximal(self, A, HS, Ap):
        sat, App = self.checkSat(HS | (self.I0 & Ap), phases=A)

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
        if self.params.polarity:
            self.sat_solver.set_phases(literals=list(phases - Ap))

        solved = self.sat_solver.solve(assumptions=list(Ap))

        if not solved:
            return solved, Ap

        model = set(self.sat_solver.get_model())

        return solved, model


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
    def __init__(self, cnf, sat: Solver, Iend: set,  I: set, params: OusParams):
        super().__init__(cnf, sat, params, I0=set(I))
        self.SSes = set()
        self.bestCosts = dict()
        self.fullSS = set(Iend)

    def bestStep(self, f, U, Iend, I: set, timeout=None):
        # best cost
        Xbest = I | {-l for l in  Iend - I}
        f_xbest = sum(f(l) for l in Xbest)

        for l in Iend - I:
            # initialising the best cost
            if l not in self.bestCosts or self.bestCosts[l] > f_xbest:
                self.bestCosts[l] = f_xbest

            F = I | {-l, l}
            X = self.bestStepOUS(f, F, I | set({-l}))
            f_expl = sum(f(l) for l in X)

            if f_expl < f_xbest:
                Xbest = X
                f_xbest = f_expl

        return Xbest

    def process_SSes(self, H):
        self.SSes |= H

        # post-processing the MSSes
        keep = set()
        for m1, m1_model in self.SSes:
            keep_m1 = True
            for m2, _ in self.SSes:
                if m1 != m2 and m1 < m2:
                    keep_m1 = False
            if keep_m1:
                keep.add((m1, m1_model))
        self.SSes = keep

    def bestStepOUS(self, f, F, A):
        bestCost = min(self.bestCosts.values())
        H, HS = set(), set()
        SSes = set()
        added_MSSes = set()
        opt_model = OptHS(F)
        lit_expl = next(iter(F - A))

        if self.params.reuse_mss:
            for SS in self.SSes:
                if SS.issubset(self.fullSS):
                    continue
                if -lit_expl not in SS or lit_expl not in SS:
                    continue

                ss = SS & F

                if any(ss.issubset(MSS) for MSS in added_MSSes):
                    continue

                C = F - ss

                if C not in H:
                    H.add(C)
                    added_MSSes.append(ss & F)
                    self.opt_model.addCorrectionSet(C)

        while(True):
            while(self.params.postpone_opt):

                while(self.params.postpone_opt_incr):
                    hs = set(HS)
                    # p-cosntraint validation only 1 of p
                    # take the minimum cost literal
                    c = min(C, key=lambda l: f(l))
                    hs.add(c)

                    sat, HSModel = self.checkSat(Ap=hs, phases=self.I0)

                    if not sat:
                        break

                    costHS = sum(f(l) for l in HS)
                    if self.params.reuse_costs and costHS > bestCost:
                        return None, costHS

                    SS = self.grow(f=f, F=F, A=A, HS=hs, HS_model=HSModel)
                    C = F - SS
                    H.add(frozenset(C))
                    self.opt_model.addCorrectionSet(C)
                    if self.params.reuse_SSes:
                        SSes.add(frozenset(SS))

                if not self.params.postpone_opt_greedy:
                    break

                HS = self.greedyHittingSet()

                sat, HSModel = self.checkSat(Ap=HS, phases=self.I0)

                costHS = sum(f(l) for l in HS)

                if not sat:
                    break

                if self.params.reuse_costs and costHS > bestCost:
                    return None, costHS

                SS = self.grow(f=f, F=F, A=A, HS=HS, HS_model=HSModel)
                C = F - SS
                H.add(frozenset(C))
                self.opt_model.addCorrectionSet(C)
                if self.params.reuse_SSes:
                    SSes.add(frozenset(SS))

            HS = opt_model.OptHittingSet()

            sat, HSModel = self.checkSat(HS, phases=self.I0)

            costHS = sum(f(l) for l in HS)

            if not sat:
                if self.params.reuse_SSes:
                    self.process_SSes(SSes)

                return HS, costHS

            if self.params.reuse_costs and costHS > bestCost:
                return None, costHS

            SS = self.grow(f=f, F=F, A=A, HS=HS, HS_model=HSModel)
            C = F - SS
            H.add(frozenset(C))
            self.opt_model.addCorrectionSet(C)
            if self.params.reuse_SSes:
                SSes.add(frozenset(SS))


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

        H = []

        if self.params.pre_seeding:
            print("Preseeding")
            # print(U)
            F = set(l for l in U) | set(-l for l in U)
            F -= {-l for l in I}
            # print("F=", F)
            # print("U=", U)
            # print("I", self.I0)
            # print("Iend", Iend)

            # find (m)ss'es of F, add correction sets
            Ap = Iend # satisfiable subset

            C = frozenset(F - Ap)

            self.opt_model.addCorrectionSet(C)
            H.append(C)

            covered = set(Iend) # already in an satsubset

            SSes = []
            for l in F:
                if self.params.pre_seeding_subset_minimal and l in covered:
                    continue

                print("Seeding", {l})
                HS = set({l})
                _, Ap = self.checkSat(Ap=HS, phases=Iend)

                # growing the HS
                if self.params.pre_seeding_grow_maxsat:
                    C = frozenset(F - self.grow_maxsat_preseeding(f=f, F=F, A=A, HS=HS, SSes=SSes))
                    SSes.append(C)
                elif self.params.pre_seeding_grow:
                    C = frozenset(F - self.grow(f, F=F, A=A, HS=HS, HS_model=Ap))
                else:
                    C = frozenset(F - Ap)

                if C not in H:
                    self.opt_model.addCorrectionSet(C)
                    H.append(C)

                if  self.params.pre_seeding_subset_minimal:
                    covered |= (Ap & F) # add covered lits of F

    def grow_maxsat_preseeding(self, f, F, A, HS, SSes):
        wcnf = WCNF()

        # add hard clauses of CNF
        wcnf.extend(self.cnf.clauses)
        # HS as hard clause
        wcnf.extend([[l] for l in HS])

        if SSes:
            # reuse previous Satisfiable subsets for diversity
            wcnf.extend([[-l for l in SS] for SS in SSes])

        # add soft clasues => F - HS
        remaining = A - HS

        weights = None

        if self.params.grow_maxsat_neg_cost:
            weights = [-f(l) for l in remaining]
        elif self.params.grow_maxsat_pos_cost:
            weights = [f(l) for l in remaining]
        elif self.params.grow_maxsat_max_cost_neg:
            max_weight = max(f(l) for l in remaining)
            weights = [max_weight+1 - f(l) for l in remaining]
        elif self.params.grow_maxsat_unit:
            weights = [1] * len(remaining)
        else:
            # print("MaxSat Grow - Defaulting to unit weight!")
            weights = [1] * len(remaining)

        wcnf.extend([[l] for l in remaining], weights)

        with RC2(wcnf) as rc2:
            t_model = rc2.compute()

            if t_model is None:
                return HS

            return set(t_model)

    def bestStep(self, f, U: set, Iend: set, I: set, timeout=1 * HOURS):
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
        Iexpl = Iend - I
        F = set(l for l in U) | set(-l for l in U)
        F -= {-l for l in I}
        # print("F=", F)
        p = {-l for l in Iexpl}

        A = I | {-l for l in Iexpl}
        return self.bestStepCOUS(f, F, A, timeout=timeout, p=p)

    def grow_maxsat(self, f, F, A, HS):
        wcnf = WCNF()

        # add hard clauses of CNF
        wcnf.extend(self.cnf.clauses + [[l] for l in HS])

        # TODO: is this really correct ? A - HS ? add soft clasues => F - HS
        remaining = A - HS

        weights = None

        if self.params.grow_maxsat_neg_cost:
            weights = [-f(l) for l in remaining]
        elif self.params.grow_maxsat_pos_cost:
            weights = [f(l) for l in remaining]
        elif self.params.grow_maxsat_max_cost_neg:
            max_weight = max(f(l) for l in remaining)
            weights = [max_weight+1 - f(l) for l in remaining]
        elif self.params.grow_maxsat_unit:
            weights = [1] * len(remaining)
        else:
            # print("MaxSat Grow - Defaulting to unit weight!")
            weights = [1] * len(remaining)

        wcnf.extend([[l] for l in remaining], weights)

        with RC2(wcnf) as rc2:
            t_model = rc2.compute()

            if t_model is None:
                return set(HS)

            return set(t_model)

    def grow_subset_maximal(self, A, HS, Ap):
        sat, App = self.checkSat(HS | (self.I0 & Ap), phases=A)

        # repeat until subset maximal wrt A
        while (Ap != App):
            Ap = set(App)
            sat, App = self.checkSat(HS | (A & Ap), phases=A)
        # print("\tgot sat", sat, len(App))
        return App

    def grow(self, f, F, A, HS, HS_model):
        # no actual grow needed if 'HS_model' contains all user vars
        t_grow = time.time()
        
        if not self.params.grow:
            SS = set(HS)
        elif self.params.grow_sat:
            SS = set(HS_model)
        elif self.params.grow_subset_maximal:
            SS = set(self.grow_subset_maximal(A=A, HS=HS, Ap=HS_model))
        elif self.params.grow_maxsat:
            SS = set(self.grow_maxsat(f=f, F=F, A=A, HS=HS))
        else:
            raise NotImplementedError("Grow")
        self.t_expl['t_grow'].append(time.time() - t_grow)
        return SS

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
        if self.params.polarity:
            self.sat_solver.set_phases(literals=list(phases - Ap))

        solved = self.sat_solver.solve(assumptions=list(Ap))

        if not solved:
            self.t_expl['t_sat'].append(time.time() - t_sat)
            return solved, Ap

        model = set(self.sat_solver.get_model())

        self.t_expl['t_sat'].append(time.time() - t_sat)
        return solved, model

    def greedyHittingSet(self, H, A, f, p):
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
            if len(p&hs) > 0:
                # cannot select lit that is in p already and already in hs
                selectable = C - (hs | {-l for l in hs} | p)
            else:
                selectable = p - {-l for l in hs}

            if len(selectable) > 0:
                c = min(selectable, key=lambda l: f(l))
            else:
                c = min(F - HS, key=lambda l: f(l) )
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

    def bestStepCOUS(self, f, F, A: set, timeout, p):
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
            't_post': [],
            't_sat': [],
            't_mip': [],
            't_grow': [],
            't_ous': 0,
            '#H':0,
            '#H_greedy': 0,
            '#H_incr': 0,
        }

        tstart = time.time()

        # UPDATE OBJECTIVE WEIGHTS
        self.opt_model.updateObjective(f, A)

        # VARIABLE INITIALISATION
        H, C, HS = list(), set(), set()
        mode = MODE_OPT

        while(True):
            if time.time() - tstart > timeout:
                self.t_expl['t_ous'] = timeout
                return HS, self.t_expl, False

            # COMPUTING OPTIMAL HITTING SET
            HS = self.computeHittingSet(f=f, F=F, A=A, p=p, H=H, C=C, HS=HS, mode=mode)
            # Timings
            print(f"\t{modes[mode]}: got HS",len(HS), "cost", self.opt_model.opt_model.objval if mode == MODE_OPT else sum(f(l) for l in HS))

            # CHECKING SATISFIABILITY
            sat, HS_model = self.checkSat(HS, phases=self.I0)

            # OUS FOUND?
            if not sat and mode == MODE_OPT:
                self.t_expl['t_ous'] = time.time() - tstart
                return HS, self.t_expl, True

            mode = self.next_mode(sat, mode)

            if not sat:
                # skip grow!
                continue

            # XXX Idea for grow- skip the grow when incremental!
            if (mode == MODE_INCR and self.params.grow_skip_incremental) or (mode == MODE_GREEDY and self.params.grow_skip_greedy):
                SS = HS_model
            else:
                SS = self.grow(f, F, A, HS, HS_model)

            C = F - SS

            # ADD COMPLEMENT TO HITTING SET OPTIMISATION SOLVER
            H.append(frozenset(C))
            self.opt_model.addCorrectionSet(C)

    def __del__(self):
        """Ensure sat solver is deleted after garbage collection.
        """
        self.sat_solver.delete()


class OptHS(object):
    def __init__(self, F, p):
        # Iend + -Iexpl
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
            obj=[f(l) for l in self.allLits],
            name="x")

        # at least the negated literal
        self.opt_model.addConstr(
            x[self.nAllLits-1] == 1
        )

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


class CondOptHS(object):
    def __init__(self, U, Iend, I):
        """Build optimisation model. The constrained optimal hitting set
        is described by:
        - x_l={0,1} is a boolean decision variable if the literal is selected
                    or not.
        - w_l=f(l) is the cost assigned to having the literal in the hitting
                   set (INF otherwise).
        - c_lj={0,1} is 1 (0) if the literal l is (not) present in hitting set j.

        Objective:
             min sum(x_l * w_l) over all l in Iend + (-Iend \ -I)
        Subject to:
            (1) sum x_l * c_lj >= 1 for all hitting sets j.
                => Hitting set must hit all sets-to-hit.
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
        self.allLits = list(I) + list(Iexpl) + list(notIexpl)
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


def profile(output_file=None, sort_by='cumulative', lines_to_print=None, strip_dirs=False):
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


def print_timings(t_exp):
    print("texpl=", round(t_exp['t_ous'], 3), "s\n")
    print("\t#HS Opt:", t_exp['#H'], "\t Incr:", t_exp['#H_incr'], "\tGreedy:", t_exp['#H_greedy'], "\n")
    if len(t_exp['t_mip']) > 0:
        print("\tMIP=\t", round(sum(t_exp['t_mip']), 3), f"s [{round(100*sum(t_exp['t_mip'])/t_exp['t_ous'])}%]\t", "t/call=", round(sum(t_exp['t_mip'])/len(t_exp['t_mip']), 3))
    if len(t_exp['t_post']) > 0:
        print("\tPOST=\t", round(sum(t_exp['t_post']), 3), f"s [{round(100*sum(t_exp['t_post'])/t_exp['t_ous'])}%]\t", "t/call=", round(sum(t_exp['t_post'])/len(t_exp['t_post']), 3))
    if len(t_exp['t_sat']) > 0:
        print("\tSAT=\t", round(sum(t_exp['t_sat']), 3), f"s [{round(100*sum(t_exp['t_sat'])/t_exp['t_ous'])}%]\t", "t/call=", round(sum(t_exp['t_sat'])/len(t_exp['t_sat']), 3))
    if len(t_exp['t_grow']) > 0:
        print("\tGROW=\t", round(sum(t_exp['t_grow']), 3), f"s [{round(100*sum(t_exp['t_grow'])/t_exp['t_ous'])}%]\t", "t/call=", round(sum(t_exp['t_grow'])/len(t_exp['t_grow']), 3))


def explainGreedy(C: CNF, U: set, f, I0: set, params: OusParams, verbose=True, matching_table=None):
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
    c = BestStepOUSComputer(f=f, cnf=C, sat=sat, I=I0, params=params)

    I = set(I0) # copy
    while(len(Iend - I) > 0):
        remaining_time = params.timeout - (time.time() - t_expl_start)
        # Compute optimal explanation explanation assignment to subset of U.
        expl, t_exp, expl_found = c.bestStep(f, U, Iend, I, timeout=remaining_time)

        if verbose:
            print_timings(t_exp)

        results["results"]["HS"].append(t_exp["#H"])
        results["results"]["HS_greedy"].append(t_exp["#H_greedy"])
        results["results"]["HS_incr"].append(t_exp["#H_incr"])
        results["results"]["HS-opt-time"].append(sum(t_exp["t_mip"]))
        results["results"]["HS-postpone-time"].append(sum(t_exp["t_post"]))
        results["results"]["OUS-time"].append(t_exp["t_ous"])
        results["results"]["SAT-time"].append(sum(t_exp["t_sat"]))
        results["results"]["grow-time"].append(sum(t_exp["t_grow"]))

        if not expl_found:
            results["results"]['timeout'] = True
            break

        # facts used

        Ibest = I & expl

        if matching_table and verbose:
            for i in Ibest:
                if(i in matching_table['trans']):
                    print("trans", i)
                elif(i in matching_table['bij']):
                    print("bij", i)
                elif(i in matching_table['clues']):
                    print("clues n°", matching_table['clues'][i])
                else:
                    print("Fact:", i)

        # New information derived "focused" on
        Nbest = optimalPropagate(U=U, I=Ibest, sat=sat) - I
        assert len(Nbest - Iend) == 0

        E.append({
            "constraints": list(Ibest), 
            "derived": list(Nbest)
        })

        if verbose:
            print(f"\nOptimal explanation \t\t {Ibest} => {Nbest}\n")

        I |= Nbest


        results["results"]["#expl"] += 1

    if verbose:
        print(E)

    results["results"]["expl_seq"] = E
    write_results(results, params.output_folder, params.instance + "_" + params.output_file)
    return E


# @profile(output_file=f'profiles/explain_{datetime.now().strftime("%Y%m%d%H%M%S")}.prof', lines_to_print=10, strip_dirs=True)
def explain(C: CNF, U: set, f, I0: set, COusParams, verbose=True, matching_table=None):
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
    assert all(True if abs(lit) in U else False for lit in I0), f"Part of supplied literals not in U (user variables): {lits for lit in I if lit not in U}"

    # Initialise the sat solver with the cnf
    sat = Solver(bootstrap_with=C.clauses)
    assert sat.solve(assumptions=I0), f"CNF is unsatisfiable with given assumptions {I}."

    # Explanation sequence
    E = []

    # Most precise intersection of all models of C project on U
    Iend = optimalPropagate(U=U, I=I0, sat=sat)
    # print(Iend)
    c = BestStepCOUSComputer(f=f, sat=sat, U=U, Iend=Iend, I=I0, params=params, cnf=C)

    I = set(I0) # copy
    while(len(Iend - I) > 0):
        remaining_time = params.timeout - (time.time() - t_expl_start)
        # Compute optimal explanation explanation assignment to subset of U.
        expl, t_exp, expl_found = c.bestStep(f, U, Iend, I, timeout=remaining_time)

        if verbose:
            print_timings(t_exp)

        results["results"]["HS"].append(t_exp["#H"])
        results["results"]["HS_greedy"].append(t_exp["#H_greedy"])
        results["results"]["HS_incr"].append(t_exp["#H_incr"])
        results["results"]["HS-opt-time"].append(sum(t_exp["t_mip"]))
        results["results"]["HS-postpone-time"].append(sum(t_exp["t_post"]))
        results["results"]["OUS-time"].append(t_exp["t_ous"])
        results["results"]["SAT-time"].append(sum(t_exp["t_sat"]))
        results["results"]["grow-time"].append(sum(t_exp["t_grow"]))

        if not expl_found:
            results["results"]['timeout'] = True
            break

        # facts used

        Ibest = I & expl

        if matching_table and verbose:
            for i in Ibest:
                if(i in matching_table['trans']):
                    print("trans", i)
                elif(i in matching_table['bij']):
                    print("bij", i)
                elif(i in matching_table['clues']):
                    print("clues n°", matching_table['clues'][i])
                else:
                    print("Fact:", i)

        # New information derived "focused" on
        Nbest = optimalPropagate(U=U, I=Ibest, sat=sat) - I
        assert len(Nbest - Iend) == 0

        E.append({
            "constraints": list(Ibest), 
            "derived": list(Nbest)
        })

        if verbose:
            print(f"\nOptimal explanation \t\t {Ibest} => {Nbest}\n")

        I |= Nbest


        results["results"]["#expl"] += 1

    if verbose:
        print(E)

    results["results"]["expl_seq"] = E
    write_results(results, params.output_folder, params.instance + "_" + params.output_file)
    return E


def write_results(results, outputdir, outputfile):
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
    explain(C=simple_cnf, U=U, f=f, I0=I, params=params)


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
    # runParallel(fns, all_params)
    params = COusParams()
    # preseeding
    params.pre_seeding = True
    # params.pre_seeding_subset_minimal = True
    params.pre_seeding_grow = True

    # polarity of sat solver
    params.polarity = True

    # sat - grow
    params.grow = True
    # params.grow_subset_maximal= True
    params.grow_maxsat = True
    params.grow_maxsat_max_cost_neg = True

    params.postpone_opt = True
    params.postpone_opt_incr = True
    # params.postpone_opt_greedy = True

    # timeout
    params.timeout = 1 * HOURS

    ## INSTANCES
    # test_explain(params)
    # test_frietkot(params)
    test_puzzle(params)
    # test_simplestReify(params)
    # test_simpleReify(params)
    # test_puzzleReify(params)


    # test_explainIff(params)
    # cnf, ass = simplestProblemIff()
    # with Solver(bootstrap_with=cnf + ass + [[-2]]) as s:
    #     s.solve()
    #     for m in s.enum_models():
    #         print(m)
    # test_explainIff(params)
    # test_frietkot(params)
    # mycnf, ass= simpleProblemIff()
    # print(mycnf)
    # print(ass)
    # test_explain(params)
    # test_frietkot(params)
    # test_explainImplies(params)
    # test_originProblemIff(params)
    # test_originProblemIff()


