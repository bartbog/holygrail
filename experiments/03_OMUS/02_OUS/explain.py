import time
from ous_utils import OusParams, Grower, OptSolver
# from ous import COUS
import random

# pysat imports
from frietkot import simpleProblem, frietKotProblem, originProblem

from pysat.formula import CNF, WCNF
from pysat.solvers import Solver

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


def explain(params, cnf: CNF, user_vars, user_vars_cost, initial_interpretation):
    """
    ExplainCSP constructor uses hard clauses supplied in CNF format to
    explain user variables with associated weights users_vars_cost based
    on the initial interpretation.

    Args:
        cnf (list): CNF C over V:
            hard puzzle problems with assumptions variables to activate or
            de-active clues.
        user_vars (list):
            User vocabulary V'
        user_vars_cost (list):
            Cost-to-use for each v in V'
        initial_interpretation (set):
            initial partial interpretation where I0 subset V'
    TODO:
        - Add user vars cost to objective function instead of 0.
    """
    print(user_vars)
    print(user_vars_cost)
    print(initial_interpretation)
    print(cnf.clauses)

    vars_expl = (set(user_vars) | set(-lit for lit in user_vars)) - initial_interpretation
    
    # Explanations
    Expl_seq = []
    
    # TODO: option1 End assignment derivable from current cnf and Interpretation
    Iend = optPropagate(cnf, I=initial_interpretation, focus=vars_expl)

    # TODO: option1 End assignment derivable from current cnf and Interpretation
    lit_ass = optPropagate(cnf, I=initial_interpretation)
    Iend = lit_ass.intersection(vars_expl)
    print(Iend)

    # current assignment I0 subset V'
    I = initial_interpretation

    # ous = COUS(cnf, user_vars, user_vars_cost, initial_interpretation, lit_ass)

    if params.warmstart:
        ous.warm_start()

    while(len(Iend - I) > 0):
        # Compute optimal explanation explanation
        # expl = ous.cOUS()
        
        # facts used
        Ibest = I | expl
        
        # assumptions used
        Cbest = user_vars | expl

        # New information derived "focused" on  
        Nbest = optPropagate(cnf, I=Ibest + Cbest, focus=(Iend - I))

        Expl_seq.append((Ibest, Cbest, Nbest))

        print(f"\nOptimal explanation \t\t {Ibest} /\\ {Cbest} => {Nbest}\n")

        I |= Nbest

    return Expl_seq


def optPropagate(cnf: CNF, I=[], focus=None):
    """
    Improvements:
    - Extension 1:
        + Reuse sat-solver bootstrapped with cnf
    - Extension 2:
        + Reuse solver bootstrapped with cnf
        + Add new clause with assumption literal 
            ex: a_i=7
        + solve with assumption literal set to false.
            solve(assumptions=[-7])
        + Add all new assumptions as True to the solver (to disable clause). 
            add_clauses([a_i]).
    Args:
    cnf (list): CNF C over V:
            hard puzzle problems with assumptions variables to activate or
            de-active clues.
    I (list):
        Assumptions + facts (partial assignment to the decision variables of 
        the User vocabulary V')
    focus (set):
        focus on decision variables
    """
    with Solver(bootstrap_with=cnf.clauses) as s:
        s.solve(assumptions=list(I))

        model = set(s.get_model())
        print(model)
        if focus:
            model &= focus

        print(model)
        while(True):
            s.add_clause(list(-lit for lit in model))
            solved = s.solve(assumptions=list(I))
            print(model)

            if solved:
                new_model = set(s.get_model())
                if focus:
                    new_model &= focus
                model = model.intersection(new_model)
            else:
                return model


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

    user_vars = s_user_vars + assumptions
    user_vars_cost = [1] * len(s_user_vars) + [10] * len(assumptions)

    # if sudoku => int. += initial values of user_vars
    initial_interpretation = set(assumptions)

    # unit cost for deriving new information
    simple_csp = explain(params_cnf, simple_cnf, user_vars=user_vars, user_vars_cost=user_vars_cost, initial_interpretation=initial_interpretation)

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