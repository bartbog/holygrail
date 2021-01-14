import time
import json
from pathlib import Path
# import random
from itertools import chain, combinations
import signal

from datetime import datetime

# pysat imports
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
from pysat.examples.musx import MUSX

# datetime object containing current date and time

# Testing samples
from frietkot import originProblem, simpleProblem, frietKotProblem

SECONDS = 1
MINUTES = 60 * SECONDS
HOURS = 60 * MINUTES


def timeoutHandler(signum, frame):
    raise OUSTimeoutError()

class MUSParams(object):
    """basic parameter backup for results interpretation
    """
    def __init__(self):
        self.instance = ""

        # timeout
        self.timeout = 2 * HOURS

        # output file
        self.output_folder = "results/" + datetime.now().strftime("%Y%m%d/")
        self.output_file = datetime.now().strftime("%Y%m%d%H%M%S%f.json")

    def to_dict(self):
        return {
            "instance": self.instance,
            "timeout": self.timeout,
        }


class OUSTimeoutError(Exception):
    """Exception raised for errors in satisfiability check.

    Attributes:
        I -- partial interpretation given as assumptions
    """
    def __init__(self):
        self.message = f"Ous explain Timeout !"
        super().__init__(self.message)

    def __str__(self):
        return f'{self.message}'


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


def print_timings(t_exp, timedout=False):
    if timedout:
        return

    print("texpl=", round(sum(t_exp['t_ous']), 3), "s\n")
    print("\t#HS Opt:", t_exp['#H'], "\t Incr:", t_exp['#H_incr'], "\tGreedy:", t_exp['#H_greedy'], "\n")

    if len(t_exp['t_mip']) > 1:
        print("\tMIP=\t", round(sum(t_exp['t_mip']), 3), f"s [{round(100*sum(t_exp['t_mip'])/sum(t_exp['t_ous']))}%]\t", "t/call=", round(sum(t_exp['t_mip'])/len(t_exp['t_mip']), 3))
    if len(t_exp['t_post']) > 1:
        print("\tPOST=\t", round(sum(t_exp['t_post']), 3), f"s [{round(100*sum(t_exp['t_post'])/sum(t_exp['t_ous']))}%]\t", "t/call=", round(sum(t_exp['t_post'])/len(t_exp['t_post']), 3))
    if len(t_exp['t_sat']) > 1:
        print("\tSAT=\t", round(sum(t_exp['t_sat']), 3), f"s [{round(100*sum(t_exp['t_sat'])/sum(t_exp['t_ous']))}%]\t", "t/call=", round(sum(t_exp['t_sat'])/len(t_exp['t_sat']), 3))
    if len(t_exp['t_grow']) > 1:
        print("\tGROW=\t", round(sum(t_exp['t_grow']), 3), f"s [{round(100*sum(t_exp['t_grow'])/sum(t_exp['t_ous']))}%]\t", "t/call=", round(sum(t_exp['t_grow'])/len(t_exp['t_grow']), 3))


def saveResults(results, t_exp):
    results["results"]["HS"].append(t_exp["#H"])
    results["results"]["HS_greedy"].append(t_exp["#H_greedy"])
    results["results"]["HS_incr"].append(t_exp["#H_incr"])
    results["results"]["HS-opt-time"].append(sum(t_exp["t_mip"]))
    results["results"]["HS-postpone-time"].append(sum(t_exp["t_post"]))
    results["results"]["OUS-time"].append(t_exp["t_ous"])
    results["results"]["SAT-time"].append(sum(t_exp["t_sat"]))
    results["results"]["grow-time"].append(sum(t_exp["t_grow"]))


def print_expl(matching_table, Ibest):
    if matching_table is None:
        return

    for i in Ibest:
        if(i in matching_table['Transitivity constraint']):
            print("trans", i)
        elif(i in matching_table['Bijectivity']):
            print("bij", i)
        elif(i in matching_table['clues']):
            print("clues n°", matching_table['clues'][i])
        else:
            print("Fact:", i)


def orderedSubsets(f, C):
    # https://stackoverflow.com/questions/1482308/how-to-get-all-subsets-of-a-set-powerset
    s = list(C)
    # make subsets
    orderedChain = list(chain.from_iterable(combinations(s, r) for r in range(1, len(s)+1)))
    # sort by difficulty
    orderedChain.sort(key=lambda Subset: sum(f(l) for l in Subset))
    for i in orderedChain:
        yield(set(i))


class MUSExplainer(object):
    def __init__(self, f, cnf, sat, U, Iend, I):
        """
        MUS computer iteratively computes the next explanation
        using mus extraction methods (MUSX):

            https://pysathq.github.io/docs/html/api/examples/musx.html
        """
        self.f = f
        self.sat = sat
        self.cnf = cnf
        self.Iend = set(Iend)
        self.I = set(I)
        self.U = set(U)

    def shrinkMus(self, assump):
        # https://pysathq.github.io/docs/html/api/examples/musx.html 
        # oracle: SAT solver (initialized)
        # assump: full set of assumptions
        i = 0

        while i < len(assump):
            to_test = assump[:i] + assump[(i + 1):]
            if self.sat.solve(assumptions=to_test):
                i += 1
            else:
                assump = to_test

        return assump

    def MUS(self, C):
        solved = self.sat.solve(assumptions=list(C))
        assert not solved, f"Satisfiable ! C={C}"
        mus = set(self.sat.get_core())

        return mus

    def MUSExtraction(self, C):
        wcnf = WCNF()
        wcnf.extend(self.cnf.clauses)
        wcnf.extend([[l] for l in C], [1]*len(C))
        with MUSX(wcnf) as musx:
            mus = musx.compute()
            # gives back positions of the clauses !!
            return set(C[i-1] for i in mus)

    def candidate_explanations(self, I: set, C: set):
        candidates = []
        # kinda hacking here my way through I and C
        J = optimalPropagate(U=self.U, I=I | C, sat=self.sat) - C
        for a in J - (I|C):
            unsat = list(set({-a}) | I | C)
            X = self.MUSExtraction(unsat)
            # print(unsat, [unsat[l-1] for l in X])
            E = I.intersection(X)
            S = C.intersection(X)
            A = optimalPropagate(U=self.U, I=E | S, sat=self.sat)
            candidates.append((E, S, A))
        return candidates

    def min_explanation(self, I, C):
        Candidates = []
        cost_min_candidate = sum(self.f(l) for l in C)

        for s in orderedSubsets(self.f, C):
            cost_subset= sum(self.f(l) for l in s)

            if len(Candidates) > 0 and cost_subset > cost_min_candidate:
                break
            cands = self.candidate_explanations(I, s)
            for cand in cands:
                E, S, _ = cand
                cost_cand = sum(self.f(l) for l in E) + sum(self.f(l) for l in S)
                Candidates.append((cost_cand, cand))

                if cost_cand < cost_min_candidate:
                    cost_min_candidate = cost_cand

        return min(Candidates, key=lambda cand: cand[0])

def explainMUS(C: CNF, U: set, f, I0: set, params: MUSParams):
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
    print("\tcnf:", len(C.clauses), C.nv)
    print("\tU:", len(U))
    print("\tf:", f)
    print("\tI0:", len(I0))

    results = {
        "config": params.to_dict(),
        "results": {
            "#expl": 0,
            "expl_seq": [],
            "MUS-time": [],
            "timeout": False
        }
    }

    tstartExplain = time.time()
    # check literals of I are all user vocabulary
    assert all(True if abs(lit) in U else False for lit in I0), f"Part of supplied literals not in U (user variables): {lits for lit in I if lit not in U}"

    # Initialise the sat solver with the cnf
    sat = Solver(bootstrap_with=C.clauses)
    assert sat.solve(assumptions=I0), f"CNF is unsatisfiable with given assumptions {I}."

    # Explanation sequence
    E = []

    # Most precise intersection of all models of C project on U, not including the constraints.
    Iend = optimalPropagate(U=U, I=I0, sat=sat) - I0

    # print(Iend)
    c = MUSExplainer(f=f, cnf=C, sat=sat, U=U, Iend=Iend, I=I0)

    I = set()
    C = set(I0) # copy

    remaining_time = round(params.timeout - (time.time() - tstartExplain))
    _ = signal.signal(signal.SIGALRM, timeoutHandler)

    # ensure max-time is not exceeded!
    signal.alarm(remaining_time)

    while(len(Iend - I) > 0):
        timedout = False
        remaining_time = params.timeout - (time.time() - tstartExplain)
        tstartMinExplain = time.time()
        # Compute optimal explanation explanation assignment to subset of U.
        try:
            costExpl, (Ei, Ci, Ai) = c.min_explanation(I, C)
        # only handling timeout error!
        except OUSTimeoutError:
            timedout = True
            results['timeout'] = True
        finally:
            tendMinExplain = time.time() - tstartMinExplain
            # ensure we don't get a timeout outside
            signal.alarm(0)
            results['results']['MUS-time'].append(tendMinExplain)

        if timedout:
            break

        # facts used
        Ibest = I & Ei
        Cbest = C & Ci

        # New information derived "focused" on
        Nbest = optimalPropagate(U=U, I=Ibest | Cbest, sat=sat) - (I|C)
        assert len(Nbest - Iend) == 0

        E.append({
            "constraints": list(Ibest | Cbest),
            "derived": list(Nbest)
        })

        print(f"\nOptimal explanation \t\t {Ibest} /\ {Cbest} => {Nbest}\n")

        I |= Nbest

        results["results"]["#expl"] += 1

    sat.delete()
    results["results"]["expl_seq"] = E

    # saving the results
    outputFile = params.instance + "_" + params.output_file
    outputDir = params.output_folder
    write_results(results, outputDir, outputFile)

    return E


def write_results(results, outputdir, outputfile):
    print(outputdir)
    print(Path(outputdir).parent)
    print(outputfile)
    if not Path(outputdir).parent.exists():
        Path(outputdir).parent.mkdir()
    if not Path(outputdir).exists():
        Path(outputdir).mkdir()
    file_path = Path(outputdir) / outputfile
    with file_path.open('w') as f:
        json.dump(results, f)


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


def cost_puzzle(U, I, cost_clue):
    """
    U = user variables
    I = initial intepretation

    bij/trans/clues = subset of user variables w/ specific cost.
    """
    litsU = set(abs(l) for l in U) | set(-abs(l) for l in U)

    I0 = set(I)

    def cost_lit(lit):
        if lit not in litsU:
            raise CostFunctionError(U, lit)
        elif lit in cost_clue:
            return cost_clue[lit]
        else:
            # lit in
            return 1

    return cost_lit


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


def read_json(pathstr):
    f_path = Path(pathstr)
    with f_path.open('r') as fp:
        json_dict = json.load(fp)
    return json_dict


def frietkotMUS(params):
    params.instance = "frietkot-problem"
    f_cnf, f_user_vars = frietKotProblem()
    f_cnf_ass, assumptions = add_assumptions(f_cnf)

    # transform list cnf into CNF object
    frietkot_cnf = CNF(from_clauses=f_cnf_ass)
    U = f_user_vars | set(abs(l) for l in assumptions)
    I = set(assumptions)
    f = cost(U, I)
    explainMUS(C=frietkot_cnf, U=U, f=f, I0=I, params=params)


def simpleMUS(params):
    params.instance = "simple-problem"
    s_cnf = simpleProblem()
    s_cnf_ass, assumptions = add_assumptions(s_cnf)
    # transform list cnf into CNF object
    simple_cnf = CNF(from_clauses=s_cnf_ass)
    U = get_user_vars(simple_cnf)
    I = set(assumptions)
    f = cost(U, I)
    explainMUS(C=simple_cnf, U=U, f=f, I0=I, params=params)


def puzzleMUS(params):
    params.instance = "origin-problem"
    o_clauses, o_assumptions, o_weights, o_user_vars, _ = originProblem()

    o_cnf = CNF(from_clauses=o_clauses)
    U = o_user_vars | set(x for lst in o_assumptions for x in lst)
    I = set(x for lst in o_assumptions for x in lst)
    f = cost_puzzle(U, I, o_weights)
    explainMUS(C=o_cnf, U=U, f=f, I0=I, params=params)

if __name__ == "__main__":
    # Translating the explanation sequence generated to website visualisation
    # Execution parameters
    params = MUSParams()
    params.timeout = 2*HOURS
    params.output_file = "mus_explain"
    params.output_folder = "results/"
    simpleMUS(params)
    frietkotMUS(params)
    puzzleMUS(params)