import time
from ous_utils import OusParams, Clauses, SatChecker, Grower, OptSolver
from ous import OUS

# pysat imports
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


class ExplainCSP:
    def __init__(self, params: OusParams, cnf: list, factsToExplain: set, weights: list, i_0: set = set(), indicatorVars: list = list()) -> None:
        self.params = params
        self.I = i_0
        self.I_cnf = []
        self.expl_seq = []

        # Build clauses from CNF
        self.clauses = Clauses(constrainedOUS=params.constrained)
        self.clauses.add_hard(cnf)

        # hand puzzle problems with indicator variables activate or de-active clues
        # weights = cost of using a clue
        if self.params.ispuzzle:
            self.clauses.add_soft(added_clauses=indicatorVars, added_weights=weights)
        else:
            self.clauses.add_indicators(weights)

        # sat solver
        self.satsolver = SatChecker(self.clauses)
        self.all_unk = factsToExplain | set(-l for l in factsToExplain)
        self.Iend = self.satsolver.optPropagate()

        self.facts = set(fact if fact in self.Iend else -fact for fact in factsToExplain)
        self.clauses.add_I(self.facts)

        # opt solver
        optSolver = OptSolver(self.clauses, params.constrained)

        # grow clauses
        grower = Grower(self.clauses, params.extension)

        self.ous = OUS(params=params, clauses=self.clauses, grower=grower, optSolver=optSolver, satSolver=self.satsolver)

    def explain(self, warmstart=False):
        """
        docstring
        """
        if warmstart:
            self.ous.warmup()

        while(len(self.facts - self.I) > 0):
            ous_start = time.time()
            hs, explanation, _ = self.ous.cOUS()
            ous_end = time.time()
            print("OUS time:", round(ous_end-ous_start, 3))

            # TODO: explaining facts - use indices instead of the clause
            E_i = [ci for ci in explanation if ci in self.I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            # TODO: constraints - use indices instead of the clause
            S_i = [ci for ci in explanation if ci in self.clauses.soft_clauses and ci not in E_i]

            # TODO: Correct NEW facts derivation
            New_info = self.satsolver.optPropagate(E_i + S_i, I=self.I, focus=self.all_unk)
            N_i = New_info.intersection(self.facts) - self.I

            # add new info
            self.I |= N_i
            self.I_cnf += [frozenset({lit}) for lit in N_i if frozenset({lit}) not in self.I_cnf]

            self.clauses.add_derived_Icnf(N_i)
            self.expl_seq.append((E_i, S_i, N_i))
            # print(New_info)
            print(f"\nOptimal explanation \t\t {E_i} /\\ {S_i} => {N_i}\n")

        return self.expl_seq

    def explain_lit(self, lit):
        pass


# @profile(sort_by='cumulative', lines_to_print=20, strip_dirs=True)
# def explain_csp(params: OusParams, cnf: list, factsToExplain: set, weights: list, i_0: set = set(), indicatorVars: list = list()):
#     # I = i_0
#     # I_cnf = []
#     # expl_seq = []



#     # all_unk = factsToExplain | set(-l for l in factsToExplain)

#     # facts = set(fact if fact in Iend else -fact for fact in factsToExplain)
#     # clauses.add_I(facts)
#     # # print(facts)
#     # print(len(indicatorVars) + len(facts))
#     # o = OUS(logging=True, params=params, clauses=clauses)
#     o.warmup()

#     cnt = 0


#     while(len(facts - I) > 0):
#         print("Remaining facts:", len(facts- I))
#         ous_start = time.time()
#         hs, explanation, _ = o.OUS()
#         ous_end = time.time()
#         print("OUS time:", round(ous_end-ous_start, 3))

#         # explaining facts
#         E_i = [ci for ci in explanation if ci in I_cnf]

#         # constraint used ('and not ci in E_i': dont repeat unit clauses)
#         S_i = [ci for ci in explanation if ci in clauses.soft_clauses and ci not in E_i]

#         New_info = optimalPropagate(clauses.hard_clauses + E_i + S_i, I, focus=all_unk)
#         N_i = New_info.intersection(facts) - I

#         # add new info
#         I |= N_i
#         I_cnf += [frozenset({lit}) for lit in N_i if frozenset({lit}) not in I_cnf]

#         o.add_derived_I(N_i)
#         expl_seq.append((E_i, S_i, N_i))
#         # print(New_info)
#         print(f"\nOptimal explanation \t\t {E_i} /\\ {S_i} => {N_i}\n")
#         cnt += 1
#         if cnt== 4:
#             return expl_seq

#     o.clean()

#     return expl_seq


def test_explain():
    params = OusParams()
    params.constrained = True
    params.incremental = False
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
    # originProblem()
    puzzle_hard, puzzle_soft, puzzle_weights, puzzle_facts = originProblem()
    puzzle_expl = explain_csp(params, cnf=puzzle_hard, factsToExplain=puzzle_facts, weights=puzzle_weights, indicatorVars=puzzle_soft, is_problem=True)

if __name__ == "__main__":
    test_explain()