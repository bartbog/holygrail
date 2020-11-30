import cProfile
import pstats
from functools import wraps

# gurobi imports
import gurobipy as gp
from gurobipy import GRB

# pysat imports
from pysat.formula import CNF
from pysat.solvers import Solver

# Testing samples
from frietkot import simpleProblem

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


class BestStepComputer(object):
    def __init__(self, Iend: set, sat: Solver):

        self.Iend = Iend
        self.sat_solver = sat
        self.opt_model = CondOptHS(Iend)

    def bestStep(self, f, Iend: set, I: set):
        """bestStep computes a subset A' of A that satisfies p s.t.
        C u A' is UNSAT and A' is f-optimal.

        Args:

            f (list): A cost function mapping 2^A -> N.
            Iend (set): The cautious consequence, the set of literals that hold in
                        all models.
            I (set): A partial interpretation such that I \subseteq Iend.
            sat (pysat.Solver): A SAT solver initialized with a CNF.
        """
        notIend = {-l for l in Iend}
        notI = {-l for l in I}

        # sum(x[lit]) == 1
        p = notIend - notI

        A = I.union(p)
        return self.bestStepCOUS(f, p, A)

    def grow(self, f, A, Ap):
        # no actual grow needed if 'Ap' contains all user vars
        return Ap

    def checkSat(self, A: set, Ap: set):
        # TODO: minimal doc of parameters
        # TODO: voeg optie toe om polarities te zetten
        solved = self.sat_solver.solve(assumptions=list(Ap))

        if not solved:
            return solved, Ap

        model = set(self.sat_solver.get_model())
        # XXX onderstaande is correct voor latere code, maar niet conceptueel deel van 'checkSat'
        #model &= A

        return solved, model

    def bestStepCOUS(self, f, p: list, A: set):
        # TODO: minimal doc of parameters
        optcnt, satcnt = 0, 0

        self.opt_model.updateObjective(f, p, A)
        print("updateObj, A=",A)
        H = set()

        while(True):
            Ap = self.opt_model.CondOptHittingSet()
            print("got HS", Ap)
            print("HS manual cost:", [(l,f(l)) for l in Ap])
            optcnt += 1

            sat, Ap = self.checkSat(A, Ap)
            print("got sat", sat, Ap)
            satcnt += 1

            if not sat:
                print(optcnt, satcnt)
                return Ap

            # XXX wat moet dit hier? (noot: huidige hack zet ook -I erin)
            H = A | {-l for l in A}
            C = H - self.grow(f, A, Ap)
            print("got C", C)
            H.add(frozenset(C))
            self.opt_model.addCorrectionSet(C)

    def __del__(self):
        self.sat_solver.delete()


class CondOptHS(object):
    def __init__(self, Iend: set):
        self.Iend = Iend
        self.notIend = set(-lit for lit in Iend)
        # XXX this includes too many, for all those in 'I' you don't need their complement!


        # idx to A + (-A)
        self.allLits = self.Iend | self.notIend
        self.nAllLits = len(self.allLits)

        # match A and -A to fix idx
        self.litToIndex = {lit: i for i, lit in enumerate(self.allLits)}

        # objective weights
        self.objWeights = [1] * self.nAllLits

        # optimisation model
        self.opt_model = gp.Model('CondOptHittingSet')

        # model parameters
        self.opt_model.Params.OutputFlag = 0
        self.opt_model.Params.LogToConsole = 0
        self.opt_model.Params.Threads = 8

        # add var with objective
        self.x = self.opt_model.addMVar(
            shape=self.nAllLits,
            vtype=GRB.BINARY,
            obj=self.objWeights,
            name="x")

        # CONSTRAINTS

        # update model
        self.opt_model.update()

    def addCorrectionSet(self, C: set):
        x = self.opt_model.getVars()
        Ci = [self.litToIndex[lit] for lit in C]

        # add new constraint sum x[j] * hij >= 1
        self.opt_model.addConstr(gp.quicksum(x[i] for i in Ci) >= 1)

    def CondOptHittingSet(self):
        self.opt_model.optimize()

        x = self.opt_model.getVars()
        hs = set(lit for i, lit in enumerate(self.allLits) if x[i].x == 1)

        print("hs: cost is ", self.opt_model.objval)
        return hs

    def updateObjective(self, f, p: list, A: set):
        # TODO: minimal doc of params
        x = self.opt_model.getVars()

        # add the p-meta constraint
        # exactly one of not Iend in the unsat subset
        # XXX this is not the objective? you are adding this each time!?
        # just once for all vars is enough (because your obj is reducing the amount of possible vars)
        print("upd obj, p=",p)
        self.opt_model.addConstr(
            gp.quicksum(x[self.litToIndex[lit]] for lit in p) == 1
        )

        # adapt the objective weights of the lits
        for lit, pos in self.litToIndex.items():
            if lit in A:
                self.objWeights[pos] = f(lit)
            else:
                self.objWeights[pos] = GRB.INFINITY
            print("obj", lit, self.objWeights[pos])

        # update the objective weights
        # XXX je kan DIT gewoon doen hierboven in de if doen? zonder die 'objWeights' array en
        # zonder dus alle vars te setAttr'en?
        for i, xi in enumerate(x):
            xi.setAttr(GRB.Attr.Obj, self.objWeights[i])

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


def optPropagateSolver(C, focus=None, I=[]):
    """
    optPropage produces the intersection of all models of cnf more precise
    projected on focus.

    Improvements:
    + Add new clause with assumption literal
        ex: a_i=7
    + solve with assumption literal set to false.
    + Add 1 assumption only as True to the solver (to disable clause). 
        add_clauses([a_i]).
    - Extension 1:
        + Reuse solver only for optpropagate
    - Extension 2:
        + Reuse solver for all sat calls

    Args:
    cnf (list): CNF C over V:
            hard puzzle problems with assumptions variables to activate or
            de-active clues.
    I (list):
        Assumptions 
        => TODO: .... Ei/Si(partial assignment to the decision variables of 
        the User vocabulary V')
    focus (set):
        +/- literals of all user variables
    """
    with Solver(bootstrap_with=C) as s:
        s.solve(assumptions=I)

        model = set(s.get_model())
        if focus:
            model &= focus

        bi = C.nv + 1
        while(True):
            s.add_clause([-bi] + [-lit for lit in model])
            solved = s.solve(assumptions=[bi])

            if not solved:
                return model

            new_model = set(s.get_model())
            model = model.intersection(new_model)


def optimalPropagate(U=None, I=set(), sat=None):
    # XXX Tias: set optional vars at end, so (sat, I, U)
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
        model &= U

    bi = sat.nof_vars() + 1

    while(True):
        sat.add_clause([-bi] + [-lit for lit in model])
        solved = sat.solve(assumptions=list(I) + [bi])

        if not solved:
            sat.add_clause([-bi])
            return model

        new_model = set(sat.get_model())
        model = model.intersection(new_model)


@profile(output_file=f'profiles/explain_{datetime.now().strftime("%Y%m%d%H%M%S")}.prof', lines_to_print=10, strip_dirs=True)
def explain(C: CNF, U: set, f, I: set):
    print("Expl:")
    print("\tcnf:",CNF)
    print("\tU:", U)
    print("\tf:", f)
    print("\tI:", I)
    """
    ExplainCSP uses hard clauses supplied in CNF format to explain user
    variables with associated weights users_vars_cost based on the
    initial interpretation.

    => hyp: cost is linear

    Args:

        cnf (list): CNF C over a vocabulary V.

        U (set): User vocabulary U subset of V.

        f (list): f is a mapping of user vars to real cost.

        I (list): Initial interpretation subset of U.
    """
    # best-step with multiple implementations possible (OUS/c-OUS/MUS...)
    # 1. rename to best-step-computer
    # 2. warm start to constructor
    # - (optional) sat solver is best to leave how it is, instead of giving it 
    # phases, might be better not modifying it.
    # - check intersection

    # check literals of I are all user vocabulary
    assert all(True if abs(lit) in U else False for lit in I), f"Part of supplied literals not in U (user variables): {lits for lit in I if lit not in U}"

    # Initialise the sat solver with the cnf
    sat = Solver(bootstrap_with=C.clauses)
    # print(C.clauses)
    #assert sat.solve(), f"CNF is unsatisfiable."
    assert sat.solve(assumptions=I), f"CNF is unsatisfiable with given assumptions {I}."

    # Explanation sequence
    E = []

    # Most precise intersection of all models of C project on U
    Iend = optimalPropagate(U=U, I=I, sat=sat)
    print("Iend", Iend)
    c = BestStepComputer(Iend, sat)

    while(len(Iend - I) > 0):
        # Compute optimal explanation explanation assignment to subset of U.
        expl = c.bestStep(f, Iend, I)
        print(expl)

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


def cost(I):
    # This is the outer enclosing function
    # litsU = set(l for l in U) | set(-abs(l) for l in U)
    # litsUnotI = litsU - I

    def cost_lit(lit):
        # This is the nested function
        # print(msg)
        if lit in I or -lit in I:
            return 20
        else:
            return 1

    return cost_lit


def get_user_vars(cnf):
    U = set(abs(l) for lst in cnf.clauses for l in lst)
    return U | set(-abs(l) for l in U)


def test_explain():
    # test on simple case
    s_cnf = simpleProblem()
    s_cnf_ass, assumptions = add_assumptions(s_cnf)
    print("prob:", s_cnf)

    # transform list cnf into CNF object
    simple_cnf = CNF(from_clauses=s_cnf_ass)
    U = get_user_vars(simple_cnf)
    I = set(assumptions)
    # XXX fix this crazy mess...
    f = cost(I)
    dct = {l: f(l) for l in U}
    f2 = lambda x: dct[x]
    explain(C=simple_cnf, U=U, f=f2, I=I)

if __name__ == "__main__":
    test_explain()
