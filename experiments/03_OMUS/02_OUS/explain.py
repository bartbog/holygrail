import time
from ous_utils import OusParams, Clauses, SatChecker, Grower, OptSolver
from ous import COUS
import random

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
        self.Iend = self.satsolver.optPropagate(explanation=self.clauses.all_soft)

        self.facts = set(fact if fact in self.Iend else -fact for fact in factsToExplain)
        self.clauses.add_I(self.facts)
        self.clauses.set_lits(self.Iend)

        # opt solver
        optSolver = OptSolver(self.clauses, params.constrained)

        # grow clauses
        grower = Grower(self.clauses, params.extension)
        self.ous = COUS(params=params, clauses=self.clauses, grower=grower, optSolver=optSolver, satSolver=self.satsolver)

    def explain(self, warmstart=False):
        """
        docstring
        """
        if warmstart:
            self.ous.warm_start()

        while(len(self.facts - self.I) > 0):
            hs, explanation, _ = self.ous.cOUS()

            # TODO: explaining facts - use indices instead of the clause
            E_i = [ci for ci in explanation if ci in self.I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            # TODO: constraints - use indices instead of the clause
            S_i = [ci for ci in explanation if ci in self.clauses.soft and ci not in E_i]

            # TODO: Correct NEW facts derivation
            New_info = self.satsolver.optPropagate(I=self.I, focus=self.all_unk, explanation=E_i + S_i)
            N_i = New_info.intersection(self.facts) - self.I

            # add new info
            self.I |= N_i
            self.I_cnf += [[lit] for lit in N_i if [lit] not in self.I_cnf]

            self.clauses.add_derived_Icnf(N_i)
            self.ous.optSolver.set_objective()
            self.expl_seq.append((E_i, S_i, N_i))
            # print(New_info)
            print(f"\nOptimal explanation \t\t {E_i} /\\ {S_i} => {N_i}\n")

        return self.expl_seq

    def explain_lit(self, lit):
        pass


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

    params_puzzle = OusParams()
    params_puzzle.constrained = True
    params_puzzle.incremental = False
    params_puzzle.pre_seed = False
    params_puzzle.sort_lits = False
    params_puzzle.bounded = False
    params_puzzle.post_opt = False
    params_puzzle.post_opt_incremental = False
    params_puzzle.post_opt_greedy = False
    params_puzzle.extension = 'maxsat'
    params_puzzle.ispuzzle = True

    # # # test on simple case
    simple_cnf, simple_facts, simple_names = simpleProblem()
    simple_weights = random.choices(list(range(2, 10)), k=len(simple_cnf))

    simple_csp = ExplainCSP(params=params_cnf, cnf=simple_cnf, factsToExplain=simple_facts, weights=simple_weights)
    explanations = simple_csp.explain(warmstart=True)

    # #test on more difficult case
    # frietkot_cnf, frietkot_facts, frietkot_names = frietKotProblem()
    # frietkot_weights = random.choices(list(range(2, 10)), k=len(frietkot_cnf))

    # frietkot_expl = explain_csp(params, cnf=frietkot_cnf, factsToExplain=frietkot_facts, weights=frietkot_weights)

    # # test on puzzle problem
    # originProblem()
    # puzzle_hard, puzzle_soft, puzzle_weights, puzzle_facts = originProblem()
    # origin_csp = ExplainCSP(params=params_puzzle, cnf=puzzle_hard, factsToExplain=puzzle_facts, weights=puzzle_weights, indicatorVars=puzzle_soft)
    # origin_csp.explain()

    # puzzle_expl = explain_csp(params, cnf=puzzle_hard, factsToExplain=puzzle_facts, weights=puzzle_weights, indicatorVars=puzzle_soft, is_problem=True)


if __name__ == "__main__":
    test_explain()