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
    def __init__(self, sat: Solver, Iend: set, Iexpl: set):
        self.sat_solver = sat
        self.opt_model = CondOptHS(Iend=Iend, Iexpl=Iexpl)

    def bestStep(self, f, U: set, Iexpl: set, I: set):
        """bestStep computes a subset A' of A that satisfies p s.t.
        C u A' is UNSAT and A' is f-optimal.

        Args:

            f (list): A cost function mapping 2^A -> N.
            Iend (set): The cautious consequence, the set of literals that hold in
                        all models.
            I (set): A partial interpretation such that I \subseteq Iend.
            sat (pysat.Solver): A SAT solver initialized with a CNF.
        """
        F = set(l for l in U) | set(-l for l in U)
        F -= {-l for l in I}
        print("F=", F)

        A = I | {-l for l in Iexpl}
        return self.bestStepCOUS(f, F, A)

    def grow(self, f, A, Ap):
        # no actual grow needed if 'Ap' contains all user vars
        return Ap

    def checkSat(self, A: set, Ap: set, polarity=False):
        """Check satisfiability of given assignment of subset of the variables of Vocabulary V.
        If the subset is unsatisfiable, Ap is returned.
        If the subset is satisfiable, the model computed by the sat solver is returned.

        Args:
            Ap (set): Susbet of literals

        Returns:
            (bool, set): sat value, model assignment
        """
        if polarity:
            self.sat_solver.set_phases(literals=list(A-Ap))

        solved = self.sat_solver.solve(assumptions=list(Ap))

        if not solved:
            return solved, Ap

        model = set(self.sat_solver.get_model())

        return solved, model

    def bestStepCOUS(self, f, F, A: set):
        # TODO: minimal doc of parameters
        optcnt, satcnt = 0, 0

        self.opt_model.updateObjective(f, A)
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
            # Stuff = 
            C = F - self.grow(f, A, Ap)
            print("got C", C)
            H.add(frozenset(C))
            self.opt_model.addCorrectionSet(C)

    def __del__(self):
        self.sat_solver.delete()


class CondOptHS(object):
    def __init__(self, Iend, Iexpl):
        notIexpl = set(-lit for lit in Iexpl)

        # Iend + -Iexpl
        self.allLits = list(l for l in Iend - Iexpl) + list(Iexpl) + list(notIexpl)
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
        print(self.allLits)
        print(Iexpl)
        print(notIexpl)
        # every explanation contains 1 neg Lit.
        posnegIexpl = range(len(Iend), self.nAllLits)
        self.opt_model.addConstr(
            x[posnegIexpl].sum() == 1
        )

        # update model
        self.opt_model.update()

    def addCorrectionSet(self, C: set):
        x = self.opt_model.getVars()
        Ci = [self.allLits.index(lit) for lit in C]

        # add new constraint sum x[j] * hij >= 1
        self.opt_model.addConstr(gp.quicksum(x[i] for i in Ci) >= 1)

    def CondOptHittingSet(self):
        self.opt_model.optimize()

        x = self.opt_model.getVars()
        hs = set(lit for i, lit in enumerate(self.allLits) if x[i].x == 1)

        print("hs: cost is ", self.opt_model.objval)
        return hs

    def updateObjective(self, f, A: set):
        # TODO: minimal doc of params
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


@profile(output_file=f'profiles/explain_{datetime.now().strftime("%Y%m%d%H%M%S")}.prof', lines_to_print=10, strip_dirs=True)
def explain(C: CNF, U: set, f, I: set):
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
    print("Expl:")
    print("\tcnf:", C.clauses)
    print("\tU:", U)
    print("\tf:", f)
    print("\tI:", I)
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
    assert sat.solve(assumptions=I), f"CNF is unsatisfiable with given assumptions {I}."

    # Explanation sequence
    E = []

    # Most precise intersection of all models of C project on U
    Iend = optimalPropagate(U=U, I=I, sat=sat)
    print("Iend", Iend)
    c = BestStepComputer(sat=sat, Iend=Iend, Iexpl=Iend - I)

    while(len(Iend - I) > 0):
        # Compute optimal explanation explanation assignment to subset of U.
        expl = c.bestStep(f, U, Iend-I, I)
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
    U = set(abs(l) for lst in cnf.clauses for l in lst)
    return U


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
    # explain(C=simple_cnf, U=U, f=f, I=I)
    # XXX fix this crazy mess...
    # f = cost(I)
    # dct = {l: f(l) for l in U}
    # f2 = lambda x: dct[x]
    # explain(C=simple_cnf, U=U, f=f2, I=I)
    explain(C=simple_cnf, U=U, f=f, I=I)

if __name__ == "__main__":
    test_explain()
