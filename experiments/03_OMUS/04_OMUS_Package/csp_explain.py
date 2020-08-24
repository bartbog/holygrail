from omus import OMUS
import json
from frietkot import frietKotProblem
from pysat.solvers import Solver
from pysat.formula import CNF
import sys
sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
from cppy import Model,  BoolVarImpl, Operator, Comparison, cnf_to_pysat


def literalstoDict(literals, literal_match):
    # TODO match literals with their axioms in first-order logic
    dictLiterals = []
    for literal in literals:
        # TODO do the matching of literals with pred-subjects-object-value
        continue

    return dictLiterals


def explanationsToJson(explanations, clue_match, literal_match, output):
    """Generates a .json file for visualizing the explanations in the zebra tutor system. Output
    format follows the following structure:
         {
             # integer value provided by the cost function
             "cost":,
             # type of constraint used
             "clue":,
              # facts used to derive new information
             "assumptions":[
                 {"pred":"", "subject":"", "object":"", "value":true/false},
                 ...
             ],
             # new information derived
             "derivations":[
                {"pred":"", "subject":"", "object":"", "value":true/false},
                 ...
             ]
         }

    Ends with :
        {
            "clue": "Solution!",
            "assumptions": [],
            "derivations": []
        }


    Args:
        explanations {iterable(dict)}: [description]
        clue_match dict(int): Match the clauses to clue or constraint
        literal_match dict(int): Match the literals to the axioms
        output {string}: name of output file
    """
    json_expls = []
    for expl in explanations:

        clue = clue_match[expl["clue"]]
        assumptions = literalstoDict(expl["assumptions"], literal_match)
        derivations = literalstoDict(expl["derived"], literal_match)

        json_expl = {
            "cost": 0,
            "clue": clue,
            "assumptions": assumptions,
            "derivations": derivations
        }

        json_expls.append(json_expl)

    with open(output, 'w') as fp:
        json.dump(json_expls, fp)


def maxPropagate(cnf, I=list()):
    with Solver() as s:
        s.append_formula(cnf, no_return=False)
        solved = s.solve()
        if solved:
            return s.get_model()
        else:
            raise "Problem"


def basecost(constraints, clues):
    # nClues = len(constraints.intersection(clues))
    nClues = 0
    nOthers = len(constraints) - nClues
    # print("constraints = ", constraints)
    if nClues == 0 and nOthers == 1:
        return 0
    elif nClues == 0 and nOthers > 1:
        return 20
    else:
        return nClues * 20


def cost(explanation):
    facts, constraints, new = explanation
    return basecost(constraints, set()) + len(facts) + len(constraints)


def propagate(cnf, I=list()):
    lits = set(lit for ci in cnf for lit in ci) | set(-lit for ci in cnf for lit in ci)

    with Solver() as s:
        s.append_formula(cnf, no_return=False)
        s.solve(assumptions=I)
        model = set(s.get_model())

    cnf_lits = lits.intersection(model)

    return cnf_lits

def optimalPropagate(cnf, I):
    # m1 = [1, 2, 3, ....]
    # m2 = [ -1, 2, 3, ....] => [2, 3]
    # m3 = cnf + [-2, -3] => nieuw model [ .., ....]
    # if sat: nieuw intersection => model zoeken
    # anders: stoppen, huidige intersection gebruike
    s = Solver()
    s.append_formula(cnf, no_return=False)
    s.solve(assumptions=list(I))
    # models = []
    model = None
    for i, m in enumerate(s.enum_models()):
        if i == 2:
            break
        if model is None:
            model = set(m)
        else:
            model.intersection(set(m))

    while(True):
        s.add_clause(list(-lit for lit in model))
        solved = s.solve()
        if solved:
            new_model = set(s.get_model())
            model = model.intersection(new_model)
        else:
            return model - I


def naiveOptimalPropagate(cnf, I):
    # The most precise and most expensive version returns the partial structure in which atoms are unknown 
    # iff they do not have the same truth value in all models
    # I_prop = set(I)
    all_models = set()
    with Solver() as s:
        s.append_formula(cnf, no_return=False)
        for m in s.enum_models():
            all_models |= set(m)
    lits = set(lit for lit in all_models if -lit not in all_models and lit not in I)
    return lits


def omusExplain(cnf, I_0=set(), weights=None, parameters=None, output='explanation.json', incremental=False):
    # initial interpretation
    I = I_0
    I_cnf = [frozenset(lit) for lit in I_0]
    I_end = set(maxPropagate(cnf, I_0))
    
    # explanation sequence
    expl_seq = []
    o = OMUS(from_clauses=cnf, parameters=parameters, weights=weights, logging=True, reuse_mss=True)

    while len(I_end - I) > 0:
        cost_best = None
        E_best, S_best, N_best = None, None, None

        # existing facts
        w_I = [1 for _ in I] + [1]

        for i in I_end - I:
            o.add_clauses(add_clauses=I_cnf + [[-i]], add_weights=w_I)

            # Match MSS
            if incremental:
                hs, explanation = o.omusIncr()
            else:
                hs, explanation = o.omus()

            # explaining facts
            E_i = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in explanation if ci in cnf and ci not in E_i]

            # new fact
            N_i = {i}

            if cost_best is None or cost((E_i, S_i, N_i)) < cost_best:
                E_best, S_best, N_best = E_i, S_i, N_i
                cost_best = cost((E_i, S_i, N_i))

        # propagate as much info as possible
        print(E_best, S_best, I)
        N_best = optimalPropagate(E_best + S_best, I) 
        # print(N_best)

        # add new info 
        I = I | N_best
        I_cnf += [frozenset({lit}) for lit in N_best]

        expl_seq.append((E_best, S_best, N_best))

        print(f"Facts:\n\t{E_best}  \nClause:\n\t{S_best} \n=> Derive (at cost {cost_best}) \n\t{N_best}")

    print(o.steps)
    assert all(False if -lit in I or lit not in I_end else True for lit in I)

    return expl_seq


def main():
    # explain
    parameters = {'extension': 'greedy_no_param','output': 'log.json'}
    cppy_model = frietKotProblem()
    cnf = cnf_to_pysat(cppy_model.constraints)
    seq = omusExplain(cnf, weights=[len(c) for c in cnf], parameters=parameters, incremental=True)
    # print()
    # print(seq)
    # optimalPropagate([[1, 2], [-1, -2], [3, 2], [3, 4]], [])

if __name__ == "__main__":
    main()
