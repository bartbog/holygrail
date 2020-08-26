import json
import sys

from pysat.formula import CNF
from pysat.solvers import Solver

sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')

from cppy import BoolVarImpl, Comparison, Model, Operator, cnf_to_pysat
from cppy.model_tools.to_cnf import *
from frietkot import frietKotProblem, originProblem, p5
from omus import OMUS



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
            return set(s.get_model())
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
    I_cnf = [frozenset({lit}) for lit in I_0]
    I_end = maxPropagate(cnf, list(I_0))
    print(I_end)
    print(cnf)
    # explanation sequence
    expl_seq = []

    # add unit literals to Interpretation
    for id, cl in enumerate(list(cnf)):
        if len(cl) == 1:
            lit = next(iter(cl))
            I.add(lit)
            I_cnf.append(frozenset({lit}))
            cnf.remove(cl)
            del weights[id]

    # all possible formulas = cnf + valid literals + negation of valid literals
    all_cnf = cnf + [frozenset({lit}) for lit in I_end] + [frozenset({-lit}) for lit in I_end]

    # OMUS model with all clauses 
    o = OMUS(all_clauses=all_cnf, from_clauses=cnf, parameters=parameters, weights=weights, logging=True, reuse_mss=False)

    while len(I_end - I) > 0:
        cost_best = None
        E_best, S_best, N_best = None, None, None

        # existing facts
        w_I = [1 for _ in I] + [1]

        for i in I_end - I:
            print("Explaining:", i)
            # Match MSS
            if incremental:

                hs, explanation = o.omusIncr(add_clauses=I_cnf + [frozenset({-i})], add_weights=w_I)
            else:
                hs, explanation = o.omus(add_clauses=I_cnf + [frozenset({-i})], add_weights=w_I)

            # explaining facts
            E_i = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            S_i = [ci for ci in explanation if ci in cnf and ci not in E_i]

            # new fact
            N_i = {i}

            if cost_best is None or cost((E_i, S_i, N_i)) < cost_best:
                E_best, S_best, N_best = E_i, S_i, N_i
                cost_best = cost((E_i, S_i, N_i))
                print(f"Facts:\n\t{E_best}  \nClause:\n\t{S_best} \n=> Derive (at cost {cost_best}) \n\t{N_best}")

        # propagate as much info as possible
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


def origin_test():
    parameters = {'extension': 'greedy_no_param','output': 'log.json'}

    model = originProblem()
    constraints = model.constraints
    cnf = to_cnf(constraints)
    pysat_cnf = cnf_to_pysat(cnf)
    # print(pysat_cnf)
    seq = omusExplain(pysat_cnf, weights=[len(c) for c in pysat_cnf], parameters=parameters, incremental=False)




def p5_test():
    parameters = {'extension': 'greedy_no_param','output': 'log.json'}
    (bv_trans, bv_bij, bv_clues), (trans, bij, clues), clue_text = p5()
    # trans_cnf = to_cnf(trans)
    # bij_cnf = to_cnf(bij)
    # clues_cnf = to_cnf(clues)
    # print(len(bij))
    # print(len(trans))
    # print(len(clues))
    constraintsIdx = dict()

    cnf = []
    weights = []
    cnt = 0
    clue_ids = {i for i in range(len(clues))}
    bij_ids = {i for i in range(len(clues), len(clues)+len(bij))}
    trans_ids = {i for i in range(len(clues)+len(bij), len(clues)+len(bij)+len(trans))}

    for clue_id, clue in zip(clue_ids, clues):
        # Clue -> cnf
        clue_cnf = cnf_to_pysat(to_cnf(clue))
        cnf += clue_cnf
        weights += [20 for _ in range(len(clue_cnf))]

        # matching table clause number => constraint
        constraintsIdx.update({i: clue_id for i in range(cnt, cnt + len(clue_cnf))})
        cnt += len(clue_cnf)
    

    # for bij_id, bij_constr in zip(bij_ids, bij):
    #     # Bijectivity constraint -> cnf
    #     bij_cnf = cnf_to_pysat(to_cnf(bij_constr))
    #     cnf += bij_cnf
    #     weights += [1 for _ in range(len(bij_cnf))]

    #     # matching table clause number => constraint
    #     constraintsIdx.update({i: bij_id for i in range(cnt, cnt + len(bij_cnf))})
    #     cnt += len(bij_cnf)

    # for trans_id, trans_constr in zip(trans_ids, trans):
    #     # Transitivity constraint -> cnf
    #     trans_cnf = cnf_to_pysat(to_cnf(trans_constr))
    #     cnf += trans_cnf
    #     weights += [1 for _ in range(len(trans_cnf))]

    #     # matching table clause number => constraint
    #     constraintsIdx.update({i: trans_id for i in range(cnt, cnt + len(trans_cnf))})
    #     cnt += len(trans_cnf)

    print(all(type(clause) == frozenset for clause in cnf))
    frozen_cnf = [frozenset(c) for c in cnf]
    seq = omusExplain(frozen_cnf, weights=weights, parameters=parameters, incremental=True)
def main():
    # explain
    parameters = {'extension': 'greedy_no_param','output': 'log.json'}
    cppy_model = frietKotProblem()
    cnf = cnf_to_pysat(cppy_model.constraints)
    frozen_cnf = [frozenset(c) for c in cnf]
    seq = omusExplain(frozen_cnf, weights=[len(c) for c in cnf], parameters=parameters, incremental=False)
    # print(seq)


if __name__ == "__main__":
    p5_test()
