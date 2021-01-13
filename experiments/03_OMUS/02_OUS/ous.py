from datetime import datetime
from pathlib import Path
import subprocess
import time
from functools import wraps
import cProfile
from collections import Counter
import pstats


#pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
from pysat.examples.rc2 import RC2

# gurobi imports
import gurobipy as gp
from gurobipy import GRB


def MUSInstances():
    musdir = Path("data/mus_instances/")
    fs = [f for f in musdir.iterdir() if f.name.endswith('.cnf')]
    fs.sort(key=lambda f: f.stat().st_size)
    return fs


def SMUS(cnf_file):
    args = f"./minuc-linux-x86-64 -v -d {cnf_file}".split()
    #Or just:
    #args = "bin/bar -c somefile.xml -d text.txt -r aString -f anotherString".split()
    tstart = time.time()
    popen = subprocess.Popen(args, stdout=subprocess.PIPE)
    popen.wait()
    tend = time.time() - tstart
    return tend
    # for line in popen.stdout:
    #     l = line.decode('utf-8').strip('\n')
    #     print(l)


class OptHS(object):
    def __init__(self, F):
        self.allLits = {l:id for id, l in enumerate(F)}
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
            obj=[1] * self.nAllLits,
            name="x")

        self.opt_model.update()

    def addCorrectionSet(self, C: set):
        """Add new constraint of the form to the optimization model,
        mapped back to decision variable lit => x[i].

            sum x[j] * hij >= 1

        Args:
            C (set): set of assumption literals.
        """
        x = self.opt_model.getVars()

        # add new constraint sum x[j] * hij >= 1
        self.opt_model.addConstr(gp.quicksum(x[self.allLits[lit]] for lit in C) >= 1)

    def OptHittingSet(self):
        """Compute conditional Optimal hitting set.

        Returns:
            set: Conditional optimal hitting mapped to assumption literals.
        """
        self.opt_model.optimize()

        x = self.opt_model.getVars()
        hs = set(lit for i, lit in enumerate(self.allLits) if x[i].x == 1)

        return hs

    def dispose(self):
        self.opt_model.dispose()


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


def greedyHittingSet(Vin):
    # trivial case: empty
    # print(H)
    if len(Vin) == 0:
        return set()

    C = set() # the hitting set

    # build vertical sets
    V = dict(Vin) # for each element in H: which sets it is in


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

        # if len(c_covers) > 1:
        #     # OMUS : find set of unsatisfiable clauses in hitting set with least total cost
        #     # => get the clause with the most coverage but with the least total weight
        #     # print(c_covers, weights)
        #     (c, cover) = min(c_covers, key=lambda tpl: weights[tpl[0]])

        del V[c]
        C.add(c)

        # update vertical views, remove covered sets
        for e in list(V): # V will be changed in this loop
            V[e] -= cover
            # no sets remaining with this element?
            if len(V[e]) == 0:
                del V[e]

    return C


def checkSat(satSolver, hs):
    sat= satSolver.solve(assumptions=list(hs))

    if not sat:
        return sat, hs
    return sat, set(satSolver.get_model())


def maxsat(F, HS):
    wcnf = WCNF()

    # add hard clauses of CNF
    wcnf.extend(F + [[l] for l in HS])
    # wcnf.extend(F - HS, [1 for l ])

    with RC2(wcnf) as rc2:
        t_model = rc2.compute()
        return set(t_model)


def profile(output_file=None, sort_by='cumulative', lines_to_print=None, strip_dirs=False):
    """
    A time profiler decorator.
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



# @profile(output_file=f'profiles/explain_{datetime.now().strftime("%Y%m%d%H%M%S")}.prof', lines_to_print=20, strip_dirs=True)
def OUS(cnf_file=None):
    cnf = CNF(from_file=cnf_file)
    cnf_ass, assumptions = add_assumptions(cnf.clauses)
    satSolver = Solver(bootstrap_with=cnf_ass)
    F = set(assumptions)
    V = dict()

    optHSComputer = OptHS(assumptions)
    tstart = time.time()

    HS = optHSComputer.OptHittingSet()
    C = F - HS
    HCounter = Counter(C)
    V = dict()
    greedy = False
    cnt = 0
    for e in C:
        if not e in V:
            V[e] = set([cnt])
        else:
            V[e].add(cnt)

    while(True):
        while(True):
            while(True):
                c = max(C, key=lambda c: HCounter[c])
                HS.add(c)
                sat, model = checkSat(satSolver, HS)

                if not sat:
                    # skip grow!
                    break

                C = F - model
                optHSComputer.addCorrectionSet(C)
                HCounter.update(C)
                for e in C:
                    if not e in V:
                        V[e] = set([cnt])
                    else:
                        V[e].add(cnt)
                cnt += 1

            if not greedy:
                break
            HS = greedyHittingSet(V)

            if not sat:
                # skip grow!
                break

            C = F - model
            optHSComputer.addCorrectionSet(C)
            for e in C:
                if not e in V:
                    V[e] = set([cnt])
                else:
                    V[e].add(cnt)
            cnt += 1
            HCounter.update(C)

        HS = optHSComputer.OptHittingSet()

        sat, model = checkSat(satSolver, HS)

        if not sat:
            # skip grow!
            tend = time.time() - tstart
            return tend

        C = F - model
        optHSComputer.addCorrectionSet(C)
        HCounter.update(C)
        for e in C:
            if not e in V:
                V[e] = set([cnt])
            else:
                V[e].add(cnt)
        cnt += 1


if __name__ == "__main__":
    for f in MUSInstances():
        print(f)
        smustime = SMUS(f)
        # print("SMUS finished")
        oustime = OUS(f)
        # print("OUS finished")
        winner = "SMUS" if smustime < oustime else "OUS"
        print(f"{winner}: OUS={oustime} - \t\tSMUS={smustime}")