import random

from ous_utils import OusParams, Clauses
from ous import OUS


# pysat imports
from pysat.formula import CNF
from pysat.solvers import Solver
from frietkot import simpleProblem

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


def explain_csp(clauses, f, factsToExplain, I0=None):
    I = set() if I0 is None else set(I0)
    E = []
    Iend = optimalPropagate(clauses.clauses)
    I_cnf = []
    ousParams = OusParams()
    o = OUS(params=ousParams, clauses=clauses)
    facts = set(fact if fact in Iend else -fact for fact in factsToExplain)

    while(len(facts - I) > 0):
        hs, explanation = o.omusConstr()

        # explaining facts
        E_i = [ci for ci in explanation if ci in I_cnf]

        # constraint used ('and not ci in E_i': dont repeat unit clauses)
        S_i = [ci for ci in explanation if ci in clauses.soft_clauses and ci not in E_i]

        # new fact
        # N_i = {i}

        New_info = optimalPropagate(clauses.hard_clauses + E_i + S_i, I)
        N_i = New_info.intersection(facts) - I

        # add new info
        I |= N_i
        I_cnf += [frozenset({lit}) for lit in N_i if frozenset({lit}) not in I_cnf]

        E.append((E_i, S_i, N_i))

        # @TIAS: printing explanations
        print(f"\nOptimal explanation \t\t {E_i} /\\ {S_i} => {N_i}\n")

    return E


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

    cnf, facts = simpleProblem()
    I_cnf = optimalPropagate(cnf)
    weights = random.choices(list(range(2, 10)), k=len(cnf))
    clauses = Clauses(constrainedOUS=True)
    clauses.add_hardclauses(cnf)
    clauses.add_indicatorVars(weights)
    clauses.add_I(I_cnf)
    print(clauses)
    o = OUS(logging=True, params=params, clauses=clauses)

if __name__ == "__main__":
    test_explain()