import time
from ous_utils import OusParams, Grower, OptSolver
# from ous import COUS
import random

# pysat imports
from frietkot import simpleProblem, frietKotProblem, originProblem

from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

from gurobipy import GRB

import cProfile
import pstats
from functools import wraps


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


def optPropagate(C, focus=None):
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
        s.solve()

        model = set(s.get_model())
        if focus:
            model &= focus

        bi = CNF(C).nv + 1
        while(True):
            s.add_clause([-bi] + [-lit for lit in model])
            solved = s.solve(assumptions=[bi])

            if not solved:
                new_model = set(s.get_model())
                if focus:
                    new_model &= focus
                model = model.intersection(new_model)
            else:
                return model


def explain(params, C, U, f):
    """
    ExplainCSP constructor uses hard clauses supplied in CNF format to
    explain user variables with associated weights users_vars_cost based
    on the initial interpretation.

    => hyp: cost is linear 

    Args:
        cnf (list): CNF C over V:
            hard puzzle problems with assumptions variables to activate or
            de-active clues.
        U (list):
            User vocabulary V' [set of]
        f (list):
            f is a mapping of user vars to real cost.
    """
    # best-step with multiple implementations possible (OUS/c-OUS/MUS...)
    # 1. rename to best-step-computer
    # 2. warm start to constructor
    # - (optional) sat solver is best to leave how it is, instead of giving it 
    # phases, might be better not modifying it.
    # - check intersection

    # Explanation sequence
    Expl_seq = []

    # Most precise intersection of all models of C project on U
    Iend = optPropagate(C, focus=U)

    # Initial interpretation I0 subset V' (for puzzles: Assumption literals + already derived facts)
    I = set(lit for lit in U if f(-lit) >= GRB.INFINITY)

    ous = COUS(C, U, f, Iend)

    while(len(Iend - I) > 0):
        # Compute optimal explanation explanation
        # rename to best-step:
        # internal state: (cnf, user_Vars, user_Vars_Cost, Iend)
        # input: I
        # output: assignemnt to subset of user_Vars 
        # - {..., ..., ..., ... }
        expl = ous.cOUS(C, f, Iend, I)
        
        # facts used
        Ibest = I & expl
        
        # assumptions used
        Cbest = user_vars & expl

        # New information derived "focused" on  
        Nbest = optPropagate(cnf, I=Ibest + Cbest, focus=(Iend - I))

        Expl_seq.append((Ibest, Cbest, Nbest))

        print(f"\nOptimal explanation \t\t {Ibest} /\\ {Cbest} => {Nbest}\n")

        I |= Nbest

    return Expl_seq



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
    params_cnf = OusParams()
    params_cnf.constrained = True
    params_cnf.incremental = False
    params_cnf.pre_seed = False
    params_cnf.sort_lits = False
    params_cnf.bounded = False
    params_cnf.post_opt = False
    params_cnf.post_opt_incremental = False
    params_cnf.post_opt_greedy = False
    params_cnf.extension = 'maxsat'
    params_cnf.ispuzzle = False

    # test on simple case
    s_cnf, s_user_vars, s_user_var_names = simpleProblem()
    s_cnf_ass, assumptions = add_assumptions(s_cnf)

    # transform list cnf into CNF object
    simple_cnf = CNF(from_clauses=s_cnf_ass)
    print(simple_cnf.clauses)
    print(simple_cnf.nv)

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

# def optPropagate(solver: Solver, I_ass, focus=None):
#     solver.solve(assumptions=I_ass)

#     model = set(solver.get_model())
#     if focus:
#         model &= focus

#     while(True):
#         solver.add_clause(list(-lit for lit in model))
#         solved = solver.solve()

#         if solved:
#             new_model = set(solver.get_model())
#             if focus:
#                 new_model &= focus
#             model = model.intersection(new_model)
#         else:
#             return model

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

# def optPropagate(solver: Solver, cnf: CNF, I: list = [], focus=None, reuse_solver=False):
#     solved = solver.solve(assumptions=I)

#     model = set(solver.get_model())
#     if focus:
#         model &= focus

#     added_assumptions = []
#     while(solved):
#         if reuse_solver:
#             # add new assumption variable
#             assumption = solver.nof_vars() + 1
#             added_assumptions.append([assumption])
#             clause = list(-lit for lit in model) + [assumption]
#             solver.add_clause(clause)

#             # TODO: check if that makes sense
#             solved = solver.solve(assumptions=[-assumption])
#         else:
#             solved = solver.solve()

#         if solved:
#             new_model = set(solver.get_model())
#             if focus:
#                 new_model &= focus
#             model = model.intersection(new_model)

#     if reuse_solver:
#         solver.append_formula(added_assumptions, no_return=True)

#     return model

# def optPropagate(solver: Solver, cnf: CNF, I: list = [], focus=None, reuse_solver=False):
#     solved = solver.solve(assumptions=I)

#     model = set(solver.get_model())
#     if focus:
#         model &= focus

#     added_assumptions = []
#     while(solved):
#         if reuse_solver:
#             # add new assumption variable
#             assumption = solver.nof_vars() + 1
#             added_assumptions.append([assumption])
#             clause = list(-lit for lit in model) + [assumption]
#             solver.add_clause(clause)

#             # TODO: check if that makes sense
#             solved = solver.solve(assumptions=[-assumption])
#         else:
#             solved = solver.solve()

#         if solved:
#             new_model = set(solver.get_model())
#             if focus:
#                 new_model &= focus
#             model = model.intersection(new_model)

#     if reuse_solver:
#         solver.append_formula(added_assumptions, no_return=True)

#     return model