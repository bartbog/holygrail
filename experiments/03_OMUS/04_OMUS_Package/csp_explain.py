import json
import sys

from pysat.formula import CNF
from pysat.solvers import Solver

sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')

from cppy import BoolVarImpl, Comparison, Model, Operator, cnf_to_pysat
from cppy.model_tools.to_cnf import *
from frietkot import frietKotProblem, p5, Relation, exactly_one
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

    # OMUS model with all clauses 
    o = OMUS(from_clauses=cnf, I=I_end, parameters=parameters, weights=weights, logging=True, reuse_mss=False)

    print(o.base_clauses)
    print(o.base_weights)

    while len(I_end - I) > 0:
        cost_best = None
        E_best, S_best, N_best = None, None, None

        # existing facts
        w_I = [1 for _ in I] + [1]

        for i in I_end - I:
            print("Explaining:", i)
            # Match MSS
            if incremental:

                hs, explanation = o.omusIncr(add_clauses=I_cnf + [frozenset({-i})],
                                             add_weights=w_I)
            else:
                hs, explanation = o.omus(add_clauses=I_cnf + [frozenset({-i})],
                                         add_weights=w_I)

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


def originProblem():
    """
    Logic grid puzzle: 'origin' in CPpy

    Based on... to check originally, currently part of ZebraTutor
    Probably part of Jens Claes' master thesis, from a 'Byron...' booklet
    """

    person = ['Mattie', 'Ernesto', 'Roxanne', 'Zachary', 'John']
    age = ['109', '110', '111', '112', '113']
    city = ['Brussels', 'Tehama', 'Zearing', 'Plymouth', 'Shaver Lake']
    birthplace = ['Mexico', 'Oregon', 'Kansas', 'Washington', 'Alaska']

    types = [person, age, city, birthplace]
    n = len(types)
    m = len(types[0])
    assert all(len(types[i]) == m for i in range(n)), "all types should have equal length"

    is_old = Relation(person, age)
    lives_in = Relation(person, city)
    native = Relation(person, birthplace)
    age_city = Relation(age, city)
    age_birth = Relation(age, birthplace)
    city_birth = Relation(city, birthplace)

    # Bijectivity
    bij = []
    for rel in [is_old, lives_in, native, age_city, age_birth, city_birth]:
        # for each relation
        for col_ids in rel.df:
            # one per column
            bij += exactly_one(rel[:, col_ids])
        for (_,row) in rel.df.iterrows():
            # one per row
            bij += exactly_one(row)

    # Transitivity
    trans = []
    for p in person:
        for c in city:
            trans.append([implies(is_old[p, a] & age_city[a, c],
                                  lives_in[p, c]) for a in age])
        for b in birthplace:
            trans.append([implies(is_old[p, a] & age_birth[a, b],
                                  native[p, b]) for a in age])
            trans.append([implies(lives_in[p, c] & city_birth[c, b],
                                  native[p, b]) for c in city])
    for a in age:
        for b in birthplace:
            trans.append([implies(age_city[a, c] & city_birth[c, b],
                                  age_birth[a, b]) for c in city])

    # Clues
    clues = []
    # Mattie is 113 years old
    clues.append(is_old['Mattie', '113'])

    # The person who lives in Tehama is a native of either Kansas or Oregon
    clues.append([implies(lives_in[p, 'Tehama'],
                          native[p, 'Kansas'] | native[p, 'Oregon']) for p in person])

    # The Washington native is 1 year older than Ernesto
    clues.append([implies(age_birth[a, 'Washington'],
                          is_old['Ernesto', str(int(a)-1)]) for a in age])

    # Roxanne is 2 years younger than the Kansas native
    clues.append([implies(is_old['Roxanne', a],
                          age_birth[str(int(a)+2), 'Kansas']) for a in age])

    # The person who lives in Zearing isn't a native of Alaska
    clues.append([implies(lives_in[p, 'Zearing'],
                          ~native[p, 'Alaska']) for p in person])

    # The person who is 111 years old doesn't live in Plymouth
    clues.append([implies(is_old[p, '111'],
                          ~lives_in[p, 'Plymouth']) for p in person])

    # The Oregon native is either Zachary or the person who lives in Tehama
    clues.append([implies(native[p, 'Oregon'],
                          (p == 'Zachary') | lives_in[p, 'Tehama']) for p in person])

    # The person who lives in Shaver Lake is 1 year younger than Roxanne
    clues.append([implies(age_city[a, 'Shaver Lake'],
                          is_old['Roxanne', str(int(a)+1)]) for a in age])

    # The centenarian who lives in Plymouth isn't a native of Alaska
    clues.append([implies(lives_in[p, 'Plymouth'],
                          ~native[p, 'Alaska']) for p in person])

    # Of the person who lives in Tehama and Mattie, one is a native of Alaska and the other is from Kansas
    clues.append([implies(lives_in[p, 'Tehama'],
                          (p != 'Mattie') &
                          ((native['Mattie', 'Alaska'] & native[p, 'Kansas']) |
                           (native[p, 'Alaska'] & native['Mattie', 'Kansas']))) for p in person])

    # model = Model(bij + trans + clues)
    # model = Model(bij + trans + clues)
    return bij, trans, clues

def test_MSSes():
    cppy_model = frietKotProblem()
    cnf = cnf_to_pysat(cppy_model.constraints)
    frozen_cnf = [frozenset(c) for c in cnf]
    seq = omusExplain(frozen_cnf, weights=[len(c) for c in cnf], parameters=parameters, incremental=True)

def explain_frietkot(parameters, incremental):
    # explain
    cppy_model = frietKotProblem()
    cnf = cnf_to_pysat(cppy_model.constraints)
    frozen_cnf = [frozenset(c) for c in cnf]
    seq = omusExplain(frozen_cnf, weights=[len(c) for c in cnf], parameters=parameters, incremental=True)
    # print(seq)

def explain_origin(parameters, incremental):
    # model constraints
    bij, trans, clues = originProblem()
    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))
    cnf = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    weights = [5 for clause in clues_cnf] + \
              [1 for clause in trans_cnf] + \
              [1 for clause in bij_cnf]

if __name__ == "__main__":
    parameters = {'extension': 'greedy_no_param','output': 'log.json'}
    # explain_origin(parameters, False)
    explain_frietkot(parameters, False)
