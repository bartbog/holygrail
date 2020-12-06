import cProfile
import pstats
import time
# import random
from functools import wraps

# gurobi imports
import gurobipy as gp
from gurobipy import GRB

# pysat imports
from pysat.formula import CNF
from pysat.solvers import Solver

# Testing samples
from frietkot import simpleProblem, originProblem, frietKotProblem

from datetime import datetime


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
    pass


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
    def __init__(self, sat: Solver, U: set, I: set, Iend:set, preseeding=True):
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
    def __init__(self, sat: Solver, U: set, Iend: set, I: set, preseeding=True):
        """
            Constructor.
        """
        self.sat_solver = sat
        self.opt_model = CondOptHS(U=U, Iend=Iend, I=I)
        self.I0 = set(I)
        self.Iend = set(Iend)

        preseeding_minimal = True
        if preseeding:
            # print("Pre-seeding")
            F = set(l for l in U) | set(-l for l in U)
            F -= {-l for l in I}

            # find (m)ss'es of F, add correction sets
            Ap = Iend # satisfiable subset
            C = F - Ap
            self.opt_model.addCorrectionSet(C)
            # print("pre-seed","",C)
            if preseeding_minimal:
                covered = set(Iend) # already in an satsubset

            for l in F:
                if preseeding_minimal and l in covered:
                    continue
                issat, Ap = self.checkSat({l}, phases=F)
                C = F - Ap
                self.opt_model.addCorrectionSet(C)
                # print("pre-seed",l,C)
                if preseeding_minimal:
                    covered |= (Ap & F) # add covered lits of F

    def bestStep(self, f, U: set, Iend: set, I: set):
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

        A = I | {-l for l in Iexpl}
        return self.bestStepCOUS(f, F, A)

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

    def greedyHittingSet(self, H, f, A):
        # trivial case: empty
        # print(H)
        if len(H) == 0:
            return set()

        # the hitting set
        C = set()

        # build vertical sets
        V = dict()  # for each element in H: which sets it is in

        for i, h in enumerate(H):
            # TIAS: only take soft clauses
            # h = [e for e in hi if self.obj_weights[e] < 1e50 and self.obj_weights[e] > 0]
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

    def bestStepCOUS(self, f, F, A: set, do_incremental=False):
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
            't_sat':[],
            't_mip':[],
            't_ous':0
        }
        # p = 
        tstart = time.time()
        self.opt_model.updateObjective(f, A)
        print("updateObj, A=",len(A))
        # print("A=", A)
        # print(f, A)
        H, C = set(), set()
        HS, Ap, App=set(), set(), set()

        MODE_OPT, MODE_GREEDY, MODE_INCR = 3, 2, 1
        mode = MODE_OPT
        while(True):
            HS_greedy = set(HS)

            while(do_incremental):
                # print("incr")
                # Computing a hitting set
                if mode == MODE_INCR:
                    # select a constraint to add
                    c = min(C, key=lambda l: f(l))
                    HS_greedy.add(c)
                elif mode == MODE_GREEDY:
                    # find a new greedy hitting set
                    HS_greedy = self.greedyHittingSet(H, f, A)
                elif mode == MODE_OPT:
                    break

                # checking for satisfiability
                sat, Ap_greedy = self.checkSat(HS_greedy, phases=self.I0)
                sat, App_greedy = self.checkSat(HS_greedy | (self.I0 & Ap_greedy), phases=A)

                # Did we find an OUS ?
                if not sat:
                    if mode == MODE_INCR:
                        mode = MODE_GREEDY
                        continue
                    elif mode == MODE_GREEDY:
                        mode = MODE_OPT
                        break

                C = F - self.grow(f, F, App_greedy)
                # print("\tgot C", len(C))
                H.add(frozenset(C))
                self.opt_model.addCorrectionSet(C)
                mode = MODE_INCR

            topt = time.time()
            HS = self.opt_model.CondOptHittingSet()
            t_expl['t_mip'].append(time.time() - topt)
            # print("\tgot HS", len(Ap), "cost", self.opt_model.opt_model.objval)

            tsat = time.time()
            sat, Ap = self.checkSat(HS, phases=self.I0)
            sat, App = self.checkSat(HS | (self.I0 & Ap), phases=A)

            t_expl['t_sat'].append(time.time() - tsat)
            # print("\tgot sat", sat, len(Ap))
            # print("\tHS=", HS)
            # print("\tAp=", Ap)
            # print("\tApp=", App)
            if not sat:
                t_expl['ous'] = time.time()-tstart
                return App, t_expl

            C = F - self.grow(f, F, App)
            # print("\tC=", C, "\n")
            # print("\tgot C", len(C))
            H.add(frozenset(C))
            self.opt_model.addCorrectionSet(C)
            mode = MODE_INCR

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
            obj=[f(l) for l in self.allLits],,
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
        self.opt_model.Params.Threads = 8

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
    print("texpl=", round(t_exp['ous'], 3), "s")
    print("\t#HS=", len(t_exp['t_mip']))
    print("\tSAT=", round(sum(t_exp['t_sat']), 3), f"s [{round(100*sum(t_exp['t_sat'])/t_exp['ous'])}%]\t", "t/call=", round(sum(t_exp['t_sat'])/len(t_exp['t_sat']), 3))
    print("\tMIP=", round(sum(t_exp['t_mip']), 3), f"s [{round(100*sum(t_exp['t_mip'])/t_exp['ous'])}%]\t", "t/call=", round(sum(t_exp['t_mip'])/len(t_exp['t_mip']), 3))


def write_json_timings(t_exp):
    pass


@profile(output_file=f'profiles/explain_{datetime.now().strftime("%Y%m%d%H%M%S")}.prof', lines_to_print=10, strip_dirs=True)
def explain(C: CNF, U: set, f, I0: set):
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
    print("Expl:")
    print("\tcnf:", len(C.clauses))
    print("\tU:", len(U))
    print("\tf:", f)
    print("\tI0:", len(I0))
    # best-step with multiple implementations possible (OUS/c-OUS/MUS...)
    # 1. rename to best-step-computer
    # 2. warm start to constructor
    # - (optional) sat solver is best to leave how it is, instead of giving it 
    # phases, might be better not modifying it.
    # - check intersection

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
    c = BestStepCOUSComputer(sat=sat, U=U, Iend=Iend, I=I0)

    I = set(I0) # copy
    while(len(Iend - I) > 0):
        # Compute optimal explanation explanation assignment to subset of U.
        expl, t_exp = c.bestStep(f, U, Iend, I)
        print_timings(t_exp)

        # facts used
        Ibest = I & expl

        # New information derived "focused" on
        Nbest = optimalPropagate(U=U, I=Ibest, sat=sat) - I

        E.append((Ibest, Nbest))

        print(f"\nOptimal explanation \t\t {Ibest} => {Nbest}\n")

        I |= Nbest

    print(E)
    return E


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


def test_frietkot():
    f_cnf, f_user_vars = frietKotProblem()
    f_cnf_ass, assumptions = add_assumptions(f_cnf)
    print("prob:", f_cnf)

    # transform list cnf into CNF object
    frietkot_cnf = CNF(from_clauses=f_cnf_ass)
    U = f_user_vars | set(abs(l) for l in assumptions)
    I = set(assumptions)
    f = cost(U, I)
    print(U)
    print(I)
    print(frietkot_cnf.clauses)
    explain(C=frietkot_cnf, U=U, f=f, I0=I)


def test_puzzle():
    o_clauses, o_assumptions, o_weights, o_user_vars = originProblem()
    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost(U, I)
    explain(C=o_cnf, U=U, f=f, I0=I)

def test_explain():
    # test on simple case
    s_cnf = simpleProblem()
    s_cnf_ass, assumptions = add_assumptions(s_cnf)
    print("prob:", s_cnf)

    # transform list cnf into CNF object
    simple_cnf = CNF(from_clauses=s_cnf_ass)
    U = get_user_vars(simple_cnf)
    I = set(assumptions)
    f = cost(U, I)
    explain(C=simple_cnf, U=U, f=f, I0=I)

if __name__ == "__main__":
    # test_explain()
    # test_frietkot()
    test_puzzle()
