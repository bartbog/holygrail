import cProfile
import pstats
import time
import json
from pathlib import Path
# import random
from functools import wraps

from multiprocessing import Process, Pool

# gurobi imports
import gurobipy as gp
from gurobipy import GRB

# pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
from pysat.examples.rc2 import RC2

from datetime import datetime

# datetime object containing current date and time


# Testing samples
from frietkot import simpleProblem, originProblem, originProblemIff, frietKotProblem, simpleProblemIff, simpleProblemImplies, simplestProblemIff, testTseitin

from datetime import datetime

SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES

class ComputationParams(object):
    """
    docstring
    """
    def __init__(self):
        # intialisation: pre-seeding
        self.pre_seeding = False
        self.pre_seeding_minimal = False
        self.pre_seeding_grow = False

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

        # timeout
        self.timeout = 24 * HOURS

        # output file
        self.output_folder = "results/" + datetime.now().strftime("%Y%m%d/")
        self.output_file = datetime.now().strftime("%Y%m%d%H%M%S%f.json")

        # instance
        self.instance = ""

    def to_dict(self):
        return {
            "preseeding": self.pre_seeding,
            "preseeding-minimal": self.pre_seeding_minimal,
            "preseeding-grow": self.pre_seeding_grow,
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
    #preparing for inheritance
    def grow(self, f, A, Ap):
        # no actual grow needed if 'Ap' contains all user vars
        return Ap

    def checkSat(self, Ap: set, polarity=True, phases=set()):
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
        if polarity:
            self.sat_solver.set_phases(literals=list(phases - Ap))

        solved = self.sat_solver.solve(assumptions=list(Ap))

        if not solved:
            return solved, Ap

        model = set(self.sat_solver.get_model())

        return solved, model


class BestStepOUSComputer(object):
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
    def __init__(self, sat: Solver, U: set, I: set, Iend: set, params: ComputationParams):
        self.sat = sat
        self.Iend = Iend
        self.I0 = set(I)
        pass

    def bestStep(self, f, I: set):
        # best cost
        Xbest = I | {-l for l in  self.Iend - I}
        f_xbest = sum(f(l) for l in Xbest)

        for l in self.Iend - I:
            X = self.bestStepOUS(f, F, I | set({-l}))
            f_expl = sum(f(l) for l in X)

            if f_expl < f_xbest:
                Xbest = X
                f_xbest = f_expl

        return Xbest

    def checkSat(self, Ap: set, polarity=True, phases=set()):
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
        if polarity:
            self.sat_solver.set_phases(literals=list(phases - Ap))

        solved = self.sat_solver.solve(assumptions=list(Ap))

        if not solved:
            return solved, Ap

        model = set(self.sat_solver.get_model())

        return solved, model

    def bestStepOUS(self, f, F, A):
        H = set()
        opt_model = OptHS()

        while(True):
            HS = opt_model.OptHittingSet()

            sat, Ap = self.checkSat(HS, phases=self.I0)
            sat, App = self.checkSat(HS | (self.I0 & Ap), phases=A)

            if not sat:
                return App

            C = F - self.grow(f, F, App)
            H.add(frozenset(C))
            self.opt_model.addCorrectionSet(C)


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
    def __init__(self, sat: Solver, f, U: set, Iend: set, I: set, params: ComputationParams, cnf: CNF = None):
        """
            Constructor.
        """
        self.sat_solver = sat
        self.opt_model = CondOptHS(U=U, Iend=Iend, I=I)
        self.I0 = set(I)
        self.Iend = set(Iend)
        A = self.I0 | {-l for l in Iend-I}
        self.params = params
        self.cnf = cnf

        if self.params.pre_seeding:
            # print("Pre-seeding")
            F = set(l for l in U) | set(-l for l in U)
            F -= {-l for l in I}

            # find (m)ss'es of F, add correction sets
            Ap = Iend # satisfiable subset

            if self.params.pre_seeding_grow:
                C = F - self.grow(f, F=F, A=A, HS=Ap, HS_model=Ap)
            else:
                C = F - Ap

            self.opt_model.addCorrectionSet(C)
            # print("pre-seed","",C)
            if self.params.pre_seeding_minimal:
                covered = set(Iend) # already in an satsubset

            for l in F:
                if self.params.pre_seeding_minimal and l in covered:
                    continue
                issat, Ap = self.checkSat(set({l}), phases=Iend)
                # print(issat)
                if self.params.pre_seeding_grow:
                    C = F - self.grow(f, F=F, A=A, HS=set({l}), HS_model=Ap)
                else:
                    C = F - Ap

                self.opt_model.addCorrectionSet(C)
                # print("pre-seed",l,C)
                if  self.params.pre_seeding_minimal:
                    covered |= (Ap & F) # add covered lits of F

    def bestStep(self, f, U: set, Iend: set, I: set, timeout=1 * HOURS):
        """bestStep computes a subset A' of A that satisfies p s.t.
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

    def grow_maxsat(self, f, F, A, HS, model):
        hs = set(HS) # take copy!!

        wcnf = WCNF()

        # add hard clauses of CNF
        wcnf.extend(self.cnf.clauses + [[l] for l in HS])

        # add soft clasues => F - HS
        remaining = F - HS
        # for l in remaining:
        #     wcnf.append([l], weight=f(l))
        wcnf.extend([[l] for l in remaining], [-f(l) for l in remaining])

        with RC2(wcnf) as rc2:
            t_model = rc2.compute()
            if t_model is None:
                return hs, model
            # print(hs, t_model)
            # print(F)
            # hs = hs | (set(t_model) & F)
            return set(t_model)

    def grow_subset_maximal(self, A, HS, Ap):
        sat, App = self.checkSat(HS | (self.I0 & Ap), phases=A)
        # repeat until subset maximal wrt A
        while (Ap != App):
            Ap = App
            sat, App = self.checkSat(HS | (A & Ap), phases=A)
        # print("\tgot sat", sat, len(App))
        return App

    def grow(self, f, F, A, HS, HS_model):
        # no actual grow needed if 'Ap' contains all user vars
        if not self.params.grow:
            return HS
        elif self.params.grow_sat:
            return HS_model
        elif self.params.grow_subset_maximal:
            return self.grow_subset_maximal(A, HS, HS_model)
        elif self.params.grow_maxsat:
            return self.grow_maxsat(f, F, A, HS, HS_model)

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

    def greedyHittingSet(self, H, f, p):
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
            assert len(Vp) > 0, "There should be at least one of p."

            (c, cover) = max(Vp.items(), key=lambda tpl: len(tpl[1]))
            c_covers = [tpl for tpl in Vp.items() if len(tpl[1]) == len(cover)]

            if len(c_covers) > 1:
                (c, cover) = min(c_covers, key=lambda tpl: f(tpl[0]))

            del V[c]
            C.add(c)

            # update vertical views, remove covered sets
            for e in list(V):
                # V will be changed in this loop
                V[e] -= cover
                # no sets remaining with this element?
                if len(V[e]) == 0:
                    del V[e]

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
                (c, cover) = min(c_covers, key=lambda tpl: f(tpl[0]))

            del V[c]
            C.add(c)

            # update vertical views, remove covered sets
            for e in list(V):
                # V will be changed in this loop
                V[e] -= cover
                # no sets remaining with this element?
                if len(V[e]) == 0:
                    del V[e]

        return C

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
        t_expl = {
            't_post':[],
            't_sat':[],
            't_mip':[],
            't_grow':[],
            't_ous':0,
            '#H':0,
            '#H_greedy':0,
            '#H_incr':0,
        }
        tstart = time.time()

        # UPDATE OBJECTIVE WEIGHTS
        self.opt_model.updateObjective(f, A)

        print("updateObj, A=",len(A))

        # VARIABLE INITIALISATION
        H, C, HS = set(), set(), set()

        while(True):
            if time.time() - tstart > timeout:
                t_expl['t_ous'] = timeout
                return HS, t_expl, False

            HS_greedy = set(HS)

            # POSTPONING OPTIMISATION
            time_post = time.time()
            while(self.params.postpone_opt):
                # tincr = time.time()
                while(self.params.postpone_opt_incr and len(H) > 0):
                    if len(C) == 0:
                        break
                    # Computing a hitting set
                    # p-cosntraint validation
                    if len(HS_greedy & p) == 0:
                        if len(p & C) > 0:
                            c = min(p & C, key=lambda l: f(l))
                            C.remove(c)
                        else:
                            c = min(p, key=lambda l: f(l))
                            if -c in C:
                                C.remove(-c)
                        # take the minimum cost literal
                    else:
                        c = min(C, key=lambda l: f(l))
                        C.remove(c)

                    HS_greedy.add(c)

                    tsat = time.time()
                    # checking for satisfiability
                    sat, HS_model_incr = self.checkSat(HS_greedy, phases=self.I0)
                    t_expl['t_sat'].append(time.time() - tsat)
                    # Did we find an OUS ?
                    if not sat:
                        break

                    tgrow = time.time()
                    C_incr = F - self.grow(f, F, A, HS_greedy, HS_model_incr)
                    t_expl['t_grow'].append(time.time() - tgrow)

                    # print("\tgot C", len(C))
                    H.add(frozenset(C_incr))
                    self.opt_model.addCorrectionSet(C_incr)
                    t_expl['#H_incr'] += 1

                if not self.params.postpone_opt_greedy:
                    break

                HS_greedy = self.greedyHittingSet(H, f, p)
                t_expl['#H_greedy'] += 1

                # checking for satisfiability
                tsat = time.time()
                sat, HS_model_greedy = self.checkSat(HS_greedy, phases=self.I0)
                t_expl['t_sat'].append(time.time() - tsat)

                if not sat:
                    break

                tgrow = time.time()
                C = F - self.grow(f, F, A, HS_greedy, HS_model_greedy)
                t_expl['t_grow'].append(time.time() - tgrow)

                H.add(frozenset(C))
                self.opt_model.addCorrectionSet(C)


            # TIMING POSTPONE OPTIMISATION
            time_post = time.time() - time_post
            if self.params.postpone_opt:
                t_expl["t_post"].append(time_post)

            topt = time.time()

            # COMPUTING OPTIMAL HITTING SET
            HS = self.opt_model.CondOptHittingSet()

            t_expl['#H'] += 1
            # Timings
            t_expl['t_mip'].append(time.time() - topt)
            print("\tgot HS", len(HS), "cost", self.opt_model.opt_model.objval)

            tsat = time.time()

            # CHECKING SATISFIABILITY
            sat, HS_model = self.checkSat(HS, phases=self.I0)
            t_expl['t_sat'].append(time.time() - tsat)

            # OUS FOUND?
            if not sat:
                t_expl['t_ous'] = time.time()-tstart
                return HS, t_expl, True

            tgrow = time.time()
            # GROW + COMPLEMENT
            C = F - self.grow(f, F, A, HS, HS_model)
            t_expl['t_grow'].append(time.time() - tgrow)
            print("\tgot C", len(C), round(time.time() - tgrow,3), "s")

            # ADD COMPLEMENT TO HITTING SET OPTIMISATION SOLVER
            H.add(frozenset(C))
            self.opt_model.addCorrectionSet(C)

    def __del__(self):
        """Ensure sat solver is deleted after garbage collection.
        """
        self.sat_solver.delete()


class OptHS(object):
    def __init__(self, U, I, l):
        # notIexpl = set(-lit for lit in Iexpl)

        # Iend + -Iexpl
        self.allLits = list(I) + [l] + [-l]
        self.nAllLits = len(self.allLits)

        # optimisation model
        self.opt_model = gp.Model('OptHittingSet')

        # model parameters
        self.opt_model.Params.OutputFlag = 0
        self.opt_model.Params.LogToConsole = 0
        self.opt_model.Params.Threads = 8

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

        self.opt_model.addConstr(
            x.sum() >= 2
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


@profile(output_file=f'profiles/explain_{datetime.now().strftime("%Y%m%d%H%M%S")}.prof', lines_to_print=10, strip_dirs=True)
def explain(C: CNF, U: set, f, I0: set, params):
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
    if params.postpone_opt:
        assert params.postpone_opt_greedy or params.postpone_opt_incr, "At least one greedy approach."

    print("Expl:")
    print("\tcnf:", len(C.clauses))
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
    # print("Iend", Iend)
    c = BestStepCOUSComputer(f=f, sat=sat, U=U, Iend=Iend, I=I0, params=params, cnf=C)

    I = set(I0) # copy
    while(len(Iend - I) > 0):
        remaining_time = params.timeout - (time.time() - t_expl_start)
        # Compute optimal explanation explanation assignment to subset of U.
        expl, t_exp, expl_found = c.bestStep(f, U, Iend, I, timeout=remaining_time)

        print_timings(t_exp)
        results["results"]["HS"].append(t_exp["#H"])
        results["results"]["HS_greedy"].append(t_exp["#H_greedy"])
        results["results"]["HS_incr"].append(t_exp["#H_incr"])
        results["results"]["HS-opt-time"].append(sum(t_exp["t_mip"]))
        results["results"]["HS-postpone-time"].append(sum(t_exp["t_post"]))
        results["results"]["OUS-time"].append(t_exp["t_ous"])
        results["results"]["SAT-time"].append(sum(t_exp["t_sat"]))

        if not expl_found:
            results["results"]['timeout'] = True
            break

        # facts used
        Ibest = I & expl

        # New information derived "focused" on
        Nbest = optimalPropagate(U=U, I=Ibest, sat=sat) - I

        E.append({
            "constraints": list(Ibest), 
            "derived": list(Nbest)
        })

        print(f"\nOptimal explanation \t\t {Ibest} => {Nbest}\n")

        I |= Nbest


        results["results"]["#expl"] += 1

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

def test_originProblemIff(params):
    params.instance = "origin-problem-iff"
    o_clauses, o_assumptions, o_weights, o_user_vars = originProblemIff()
    o_cnf = CNF(from_clauses=o_clauses)
    with Solver(bootstrap_with=o_cnf.clauses + o_assumptions) as s:
        solved = s.solve()
        for i, m in enumerate(s.enum_models()):
            print(i)

    # U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    # I = set(x for lst in o_assumptions for x in lst)
    # f = cost(U, I)
    # explain(C=o_cnf, U=U, f=f, I0=I, params=params)

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
    o_clauses, o_assumptions, o_weights, o_user_vars = originProblem()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    # print(o_weights)
    # return 
    f = cost_puzzle(U, I, o_weights)
    explain(C=o_cnf, U=U, f=f, I0=I, params=params)

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

def test_explainImplies(params):
    params.instance = "simpleIff"
    s_cnf, s_ass = simpleProblemIff()
    with Solver(bootstrap_with=s_cnf + [[l] for l in s_ass]) as s:
        solved = s.solve()
        i = 0
        for i, m in enumerate(s.enum_models()):
            if i > 0:
                print(i)
        assert i == 0
    simple_cnf = CNF(from_clauses=s_cnf)
    U = get_user_vars(simple_cnf)
    I = set(s_ass)
    f = cost(U, I)
    explain(C=simple_cnf, U=U, f=f, I0=I, params=params)

def test_explainIff(params):
    params.instance = "simpleIff"
    s_cnf, s_ass = simpleProblemIff()
    print(s_cnf)
    print(s_ass)
    with Solver(bootstrap_with=s_cnf + [[-l] for l in s_ass]) as s:
        solved = s.solve()
        i = 0
        for i, m in enumerate(s.enum_models()):
            print(m)
            if i > 4:
                break
                # print(i)
        assert i == 0
    simple_cnf = CNF(from_clauses=s_cnf)
    U = get_user_vars(simple_cnf)
    I = set(s_ass)
    f = cost(U, I)
    explain(C=simple_cnf, U=U, f=f, I0=I, params=params)

def all_param_test():
    all_params = []
    for preseed in [True, False]:
        for subset_maximal in [True, False]:
            for polarity in [True, False]:
                # preseeding
                p = ComputationParams()
                p.pre_seeding = preseed
                p.pre_seeding_minimal = preseed

                # polarity
                p.polarity = polarity

                # subset_maximal
                p.subset_maximal = subset_maximal

                all_params.append(p)
    return all_params

def runParallel(fns, args):
    procs = []
    for fn in fns:
        for arg in args:
            p = Process(target=fn, args=(arg,))
            p.start()
            procs.append(p)

    for p in procs:
        p.join()


if __name__ == "__main__":
    # all_params = all_param_test()
    # fns = [test_explain, test_frietkot, test_puzzle, test_originProblemIff]

    # runParallel(fns, all_params)
    params = ComputationParams()
    # preseeding
    params.pre_seeding = True
    params.pre_seeding_minimal = True
    params.pre_seeding_grow = True

    # polarity of sat solver
    params.polarity = True

    # sat - grow
    params.grow = True
    params.grow_subset_maximal= True
    # params.grow_maxsat = True

    # params.postpone_opt = True
    # params.postpone_opt_incr = True
    # params.postpone_opt_greedy = True

    # timeout
    params.timeout = 1 * HOURS

    # test_explain(params)
    # test_frietkot(params)
    # test_explainIff(params)
    # cnf, ass = simplestProblemIff()
    # with Solver(bootstrap_with=cnf + ass + [[-2]]) as s:
    #     s.solve()
    #     for m in s.enum_models():
    #         print(m)
    # test_explainIff(params)
    # test_frietkot(params)
    test_puzzle(params)
    # mycnf, ass= simpleProblemIff()
    # print(mycnf)
    # print(ass)
    # test_explain(params)
    # test_frietkot(params)
    # test_explainImplies(params)
    # test_originProblemIff(params)
    # test_originProblemIff()


