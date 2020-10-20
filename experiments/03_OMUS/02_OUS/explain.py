import random
import time
from ous_utils import OusParams, Clauses
from ous import OUS

# pysat imports
from pysat.formula import CNF
from pysat.solvers import Solver
from frietkot import simpleProblem, frietKotProblem, originProblem

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


def optimalPropagate(cnf, I=None, focus=None):
    # focus: a set of literals to filter, only keep those of the model
    # SET A FOCUS if many auxiliaries...
    with Solver(bootstrap_with=cnf) as s:
        if I is None or len(I) == 0:
            s.solve()
        elif len(I) > 0:
            s.solve(assumptions=list(I))

        model = set(s.get_model())
        if focus:
            model &= focus

        while(True):
            s.add_clause(list(-lit for lit in model))
            solved = s.solve()
            if solved:
                new_model = set(s.get_model())
                if focus:
                    new_model &= focus
                model = model.intersection(new_model)
                #print("oP",c,model,time.time()-ts,new_model)
            else:
                return model


@profile(sort_by='cumulative', lines_to_print=None, strip_dirs=True)
def explain_csp(params: OusParams, cnf: list, factsToExplain: set, weights: list, i_0: set = set(), indicatorVars: list = list(), is_problem=False):
    I = i_0
    I_cnf = []
    expl_seq = []

    if is_problem:
        Iend = optimalPropagate(cnf + indicatorVars)
    else:
        Iend = optimalPropagate(cnf)

    all_unk = factsToExplain | set(-l for l in factsToExplain)
    facts = set(fact if fact in Iend else -fact for fact in factsToExplain)
    # print(facts)

    clauses = Clauses(constrainedOUS=params.constrained)
    clauses.add_hardclauses(cnf)

    if is_problem:
        clauses.add_soft_clauses(added_clauses=indicatorVars, added_weights=weights)
    else:
        clauses.add_indicatorVars(weights)

    clauses.add_I(facts)
    # print(facts)
    print(len(indicatorVars) + len(facts))
    o = OUS(logging=True, params=params, clauses=clauses)
    o.reuse_satSolver()
    # o.print_clauses()
    # return None
    cnt = 0

    while(len(facts - I) > 0):
        ous_start = time.time()
        hs, explanation, _ = o.OUS()
        ous_end = time.time()

        # explaining facts
        E_i = [ci for ci in explanation if ci in I_cnf]

        # constraint used ('and not ci in E_i': dont repeat unit clauses)
        S_i = [ci for ci in explanation if ci in clauses.soft_clauses and ci not in E_i]

        New_info = optimalPropagate(clauses.hard_clauses + E_i + S_i, I, focus=all_unk)
        N_i = New_info.intersection(facts) - I

        # add new info
        I |= N_i
        I_cnf += [frozenset({lit}) for lit in N_i if frozenset({lit}) not in I_cnf]

        o.add_derived_I(N_i)
        expl_seq.append((E_i, S_i, N_i))
        # print(New_info)
        print(f"\nOptimal explanation \t\t {E_i} /\\ {S_i} => {N_i}\n")
        cnt += 1
        if cnt== 4:
            return expl_seq

    o.clean()

    return expl_seq


def test_explain():
    params = OusParams()
    params.constrained = True
    params.incremental = False
    # self.incremental_sat = False
    params.pre_seed = False
    params.sort_lits = False
    params.bounded = False
    params.post_opt = False
    params.post_opt_incremental = False
    params.post_opt_greedy = False
    params.extension = 'maxsat'

    # # # test on simple case
    # simple_cnf, simple_facts, simple_names = simpleProblem()
    # simple_weights = random.choices(list(range(2, 10)), k=len(simple_cnf))

    # simple_expl = explain_csp(params, cnf=simple_cnf, factsToExplain=simple_facts, weights=simple_weights)

    # #test on more difficult case
    # frietkot_cnf, frietkot_facts, frietkot_names = frietKotProblem()
    # frietkot_weights = random.choices(list(range(2, 10)), k=len(frietkot_cnf))

    # # print(frietkot_cnf)
    # frietkot_expl = explain_csp(params, cnf=frietkot_cnf, factsToExplain=frietkot_facts, weights=frietkot_weights)

    # # print(frietkot_cnf)
    # for expl in frietkot_expl:
    #     E_i, S_i, N_i = expl
    #     if len(E_i) > 0:
    #         E_expl = [frietkot_names[abs(next(iter(f_lit)))] for f_lit in E_i]
    #     else:
    #         E_expl = []
    #     if len(S_i) > 0:
    #         S_expl = S_i
    #     else:
    #         S_expl = []
    #     N_expl = [('-' if f_lit < 0 else '')  + frietkot_names[abs(f_lit)] for f_lit in N_i]


    #     print(f"Expl:\n\tE_expl={E_expl}\n\tS_expl={S_expl}\n\tN_expl={N_expl}")

    # # test on puzzle problem
    puzzle_hard, puzzle_soft, puzzle_weights, puzzle_facts = originProblem()
    puzzle_expl = explain_csp(params, cnf=puzzle_hard, factsToExplain=puzzle_facts, weights=puzzle_weights, indicatorVars=puzzle_soft, is_problem=True)

if __name__ == "__main__":
    test_explain()