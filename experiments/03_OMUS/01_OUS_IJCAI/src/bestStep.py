
from exceptions import UnsatError
from hittingSet import CondOptHS, OptHS
from params import BestStepParams, COusParams, OusParams

# pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
from pysat.examples.musx import MUSX
from pysat.examples.rc2 import RC2


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



class BestStepComputer(object):
    def __init__(self, cnf: CNF, sat: Solver, params: BestStepParams, I0, Iend):
        self.sat_solver = sat
        self.cnf = cnf
        self.opt_model = None
        self.I0 = I0
        self.I = set(I0)
        self.Iend = Iend
        self.params = params


    def grow_subset_maximal_actual(self,  HS, Ap):
        _, App = self.checkSat(HS | (self.I & Ap), phases=self.I)
        # repeat until subset maximal wrt A
        while (Ap != App):
            Ap = set(App)
            sat, App = self.checkSat(HS | (self.I & Ap), phases=self.I)
        # print("\tgot sat", sat, len(App))
        return App

    def grow(self, f, F, A, HS, HS_model):
        # no actual grow needed if 'HS_model' contains all user vars
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
        return SS

    def grow_maxsat(self, f, F, A, HS):
        # print("Growing!", A, HS)
        wcnf = WCNF()

        # add hard clauses of CNF
        wcnf.extend(self.cnf.clauses + [[l] for l in HS])

        # cost is associated for assigning a truth value to literal not in
        # contrary to A.
        remaining = None

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

        with RC2(wcnf) as s:
            if self.params.maxsat_polarities and hasattr(s, 'oracle'):
                s.oracle.set_phases(literals=list(self.Iend))
            t_model = s.compute()

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
        if self.params.polarity:
            self.sat_solver.set_phases(literals=list(self.Iend - Ap))
        elif self.params.polarity_initial:
            self.sat_solver.set_phases(literals=list(self.I0 - Ap))

        solved = self.sat_solver.solve(assumptions=list(Ap))

        if not solved:
            return solved, Ap

        model = set(self.sat_solver.get_model())
        return solved, model


class BestStepMUSComputer(object):
    def __init__(self, f, cnf, sat, U, Iend, I):
        """
        MUS computer iteratively computes the next explanation
        using mus extraction methods (MUSX):

            https://pysathq.github.io/docs/html/api/examples/musx.html
        """
        self.f = f
        self.sat = sat
        self.cnf = cnf
        self.Iend = set(Iend)
        self.I = set(I)
        self.U = set(U)

    def MUSExtraction(self, C):
        wcnf = WCNF()
        wcnf.extend(self.cnf.clauses)
        wcnf.extend([[l] for l in C], [1]*len(C))
        with MUSX(wcnf, verbosity=0) as musx:
            mus = musx.compute()
            # gives back positions of the clauses !!
            return set(C[i-1] for i in mus)

    def candidate_explanations(self, I: set, C: set):
        candidates = []
        # kinda hacking here my way through I and C
        J = optimalPropagate(U=self.U, I=I | C, sat=self.sat) - C
        for a in J - (I|C):
            unsat = list(set({-a}) | I | C)
            X = self.MUSExtraction(unsat)
            E = I.intersection(X)
            S = C.intersection(X)
            candidates.append((E, S))
        return candidates

    def naive_min_explanation(self, I, C):
        Candidates = []
        all_constraints = set(C)
        cands = self.candidate_explanations(I, all_constraints)
        for cand in cands:
            E, S = cand
            cost_cand = sum(self.f(l) for l in E) + sum(self.f(l) for l in S)
            Candidates.append((cost_cand, cand))

        return min(Candidates, key=lambda cand: cand[0])


class BestStepCOUSComputer(BestStepComputer):
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
        super().__init__(cnf=cnf, sat=sat, params=params, I0=I, Iend=Iend,)
        # Execution parameters
        # Optimisation model
        self.opt_model = CondOptHS(U=U, Iend=Iend, I=I)

        # initial values
        self.I0 = set(I)
        self.U = set(U) | set(-l for l in U)

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
        return self.bestStepCOUS(f, F, A)

    def computeHittingSet(self):
        hs = self.opt_model.CondOptHittingSet()
        return hs


    def bestStepCOUS(self, f, F, A: set):
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
        # UPDATE OBJECTIVE WEIGHTS
        self.opt_model.updateObjective(f, A)

        while(True):
            # COMPUTING OPTIMAL HITTING SET
            HS = self.computeHittingSet()

            # CHECKING SATISFIABILITY
            sat, HS_model = self.checkSat(HS, phases=self.I0)

            # OUS FOUND?
            if not sat:
                return HS

            SS = self.grow(f, F, A, HS, HS_model)
            C = F - SS

            self.opt_model.addCorrectionSet(C)

    def __del__(self):
        """Ensure sat solver is deleted after garbage collection.
        """
        self.opt_model.__del__()


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
        self.params = params
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
        self.I = set(I)

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

            expl, costExpl = self.bestStepOUS(f, F=F, A=A)

            # can only keep the costs of the optHittingSet computer
            if costExpl < self.bestCosts[l] and expl is not None:
                self.bestCosts[l] = costExpl

            # store explanation
            if costExpl <= bestCost and expl is not None:
                bestExpl = expl
                bestLit = l
                bestCost = costExpl

        # literal already found, remove its cost
        del self.bestCosts[bestLit]
        return bestExpl

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

    def computeHittingSet(self,):
        hs = self.optHSComputer.OptHittingSet()
        return hs

    def bestStepOUS(self, f, F, A):
        # initial running varaibles
        H, HS, C, SSes = set(), set(), set(), set()

        # initial best cost
        bestCost = min(self.bestCosts.values())
        costHS = sum(f(l) for l in A)

        # Start with OPTIMISATION mode

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
                    SSes.append(ss)
                    self.optHSComputer.addCorrectionSet(C)

        while(True):
            HS = self.computeHittingSet()

            sat, HSModel = self.checkSat(HS, phases=self.I0)

            costHS = sum(f(l) for l in HS)

            if costHS > bestCost:
                return None, costHS

            # OUS FOUND?
            if not sat:
                # cleaning up!
                self.optHSComputer.dispose()

                if self.params.reuse_SSes:
                    self.process_SSes(SSes)

                return HS, costHS

            SS = self.grow(f=f, F=F, A=A, HS=HS, HS_model=HSModel)
            C = F - SS
            H.add(frozenset(C))
            self.optHSComputer.addCorrectionSet(C)
            if self.params.reuse_SSes:
                SSes.add(frozenset(SS))
