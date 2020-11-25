import cProfile
import pstats
import random
import time
from functools import wraps

# gurobi imports
import gurobipy as gp
from gurobipy import GRB

# pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

# Testing samples
from frietkot import simpleProblem


class UnsatError(Exception):
    """Exception raised for errors in satisfiability check.

    Attributes:
        I -- partial interpretation given as assumptions
    """
    def __init__(self, I):
        self.I = I
        self.message = f"Partial interpretation is unsat:"
        super().__init__(self.message)

    def __str__(self):
        return f'{self.message}\n\t{self.I}'


class BestStepComputer(object):
    def __init__(self, f, Iend: set, I: set, sat: Solver):
        # self.p = p
        self.f = f
        self.Iend = Iend

        # compute initial A
        notIend = {-l for l in Iend}
        notI = {-l for l in I}
        A = I.union(notIend - notI)

        self.sat_solver = sat
        self.opt_model = CondOptHS(f, A)

    def bestStep(self, I: set):
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

        return self.bestStepCOUS(p, A)

    def bestStepCOUS(p, A):
        pass


class CondOptHS(object):
    def __init__(self, f, A):
        self.A = A
        self.notA = [-lit for lit in A]

        # match A and -A to fix idx
        self.litToIndex = {lit: i for i, lit in enumerate(self.A + self.notA)}

        # idx to A + (-A)
        self.allLits = self.A + self.notA
        self.nAllLits = len(self.allLits)

        # objective weights
        self.objWeights = [f(lit) for lit in A] + [GRB.INFINITY] * len(self.notA)
        self.opt_model = gp.Model('CondOptHittingSet')

        # add var with objective
        x = self.opt_model.addMVar(
            shape=self.nAllLits,
            vtype=GRB.BINARY,
            obj=self.objWeights,
            name="x")

        # CONSTRAINTS
        # Exactly one of the -literals
        self.opt_model.addConstr(x[p].sum() == 1)

        # update model
        self.opt_model.update()

    def addCorrectionSet(self, C):
        x = self.opt_model.getVars()
        Ci = [self.litToIndex[lit] for lit in C]

        # add new constraint sum x[j] * hij >= 1
        self.opt_model.addConstr(gp.quicksum(x[i] for i in Ci) >= 1)

    def optHS(self):
        self.opt_model.optimize()
        x = self.opt_model.getVars()
        hs = set(lit for i, lit in enumerate(self.allLits) if x[i].x == 1)

        return hs

    def updateObj(self):
        x = self.opt_model.getVars()

        for i, xi in enumerate(x):
            xi.setAttr(GRB.Attr.Obj, self.clauses.obj_weights[i])

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


def optimalPropagate(U=None, I=[], sat=None):
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
    solved = sat.solve(assumptions=I)

    if not solved:
        raise UnsatError(I)

    model = set(sat.get_model())
    if U:
        model &= U

    bi = sat.nof_vars() + 1

    while(True):
        sat.add_clause([-bi] + [-lit for lit in model])
        solved = sat.solve(assumptions=I + [bi])

        if not solved:
            sat.add_clause([bi])
            return model

        new_model = set(sat.get_model())
        model = model.intersection(new_model)


def bestStep


def explain(C: CNF, U: list, f, I):
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
    assert all(True if abs(lit) in U else False for lit in I), f"Part of supplied literals not in U (user variables)."

    # Initialise the sat solver with the cnf
    sat = Solver(bootstrap_with=C.clauses)
    assert sat.solve(), f"CNF is unsatisfiable."
    assert sat.solve(assumptions=I), f"CNF is unsatisfiable with given assumptions {I}."

    # Explanation sequence
    E = []

    # Most precise intersection of all models of C project on U
    Iend = optimalPropagate(U=U, I=I, sat=sat)

    sat.delete()

    while(len(Iend - I) > 0):
        # Compute optimal explanation explanation assignment to subset of U.
        expl = bestStep(f, Iend, I)

        # facts used
        Ibest = I & expl

        # New information derived "focused" on  
        Nbest = optimalPropagate(U=U, I=Ibest, sat=sat) - I

        E.append((Ibest, Nbest))

        print(f"\nOptimal explanation \t\t {Ibest} => {Nbest}\n")

        I |= Nbest

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


def test_explain():
    # test on simple case
    s_cnf = simpleProblem()
    s_cnf_ass, assumptions = add_assumptions(s_cnf)

    # transform list cnf into CNF object
    simple_cnf = CNF(from_clauses=s_cnf_ass)
    print(simple_cnf.clauses)
    with Solver(bootstrap_with=simple_cnf) as s:
        print(s.nof_vars())

    # user_vars = s_user_vars + assumptions
    # user_vars_cost = [1] * len(s_user_vars) + [10] * len(assumptions)

    # # if sudoku => int. += initial values of user_vars
    # initial_interpretation = set(assumptions)

    # # unit cost for deriving new information
    # simple_csp = explain(params_cnf, simple_cnf, user_vars=user_vars, user_vars_cost=user_vars_cost, initial_interpretation=initial_interpretation)

    # TODO:
    # - remove all user vars with interpretation => remaining  = to explain.
    # 

    # generate explanations

    # #test on more difficult case
    # frietkot_cnf, frietkot_facts, frietkot_names = frietKotProblem()
    # frietkot_weights = random.choices(list(range(2, 10)), k=len(frietkot_cnf))

    # frietkot_expl = explain_csp(params, cnf=frietkot_cnf, factsToExplain=frietkot_facts, weights=frietkot_weights)


    # params_puzzle = OusParams()
    # params_puzzle.constrained = True
    # params_puzzle.incremental = False
    # params_puzzle.pre_seed = False
    # params_puzzle.sort_lits = False
    # params_puzzle.bounded = False
    # params_puzzle.post_opt = False
    # params_puzzle.post_opt_incremental = False
    # params_puzzle.post_opt_greedy = False
    # params_puzzle.extension = 'maxsat'
    # params_puzzle.ispuzzle = True

    # # test on puzzle problem
    # originProblem()
    # puzzle_hard, puzzle_soft, puzzle_weights, puzzle_facts = originProblem()
    # origin_csp = ExplainCSP(params=params_puzzle, cnf=puzzle_hard, factsToExplain=puzzle_facts, weights=puzzle_weights, indicatorVars=puzzle_soft)
    # origin_csp.explain()

    # puzzle_expl = explain_csp(params, cnf=puzzle_hard, factsToExplain=puzzle_facts, weights=puzzle_weights, indicatorVars=puzzle_soft, is_problem=True)


if __name__ == "__main__":
    test_explain()
