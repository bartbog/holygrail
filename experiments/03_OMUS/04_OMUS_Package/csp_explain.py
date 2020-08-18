from omus import OMUS
import json
from frietkot import frietKotProblem
from pysat.solvers import Solver
from pysat.formula import CNF
import sys
sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
from cppy import Model,  BoolVarImpl, Operator, Comparison, cnf_to_pysat

# TODO : 
# - OMUS without incremental
# - OMUS with incremental
# - OMUS w/o reuse of MSS 
# - OMUS with reuse of MSS (w/ or w/o models)


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
    # clauses = [frozenset(ci) for ci in cnf]
    # print(cnf)
    I_end = set(maxPropagate(cnf, I_0))
    I = I_0
    M = {i: [] for i in I_end - I}
    seq = []
    cnf_idx = {i for i in range(len(cnf))}

    # clausesUsed = set()
    while len(I_end - I) > 0:
        I_cnf = [set({li}) for li in I]
        I_idx = {len(cnf) + i for i in range(len(I))}
        w_I = [1 for _ in I]

        cost_best, i_best = None, None
        E_best, S_best, N_best = None, None, None

        for i in I_end - I:
            unsat_cnf = cnf + I_cnf + [[-i]]
            w_cnf = weights + w_I + [1]

            # Match MSS
            o = OMUS(from_clauses=unsat_cnf, parameters=parameters, weights=w_cnf)
            if incremental:
                MSS_i = []
                for mss_cnf_idx, mss_I, model in M[i]:
                    # mss = MSS[cnf] + MSS[mss_I] + pos(-i)
                    mss_i = mss_cnf_idx | set({len(cnf) + I_cnf.index(li) for li in mss_I}) | set({len(cnf) + len(I)})
                    mss_cnf_lits = {abs(lit) for clause_idx in mss_cnf_idx for lit in cnf[clause_idx]}
                    model_i = set()
                    # elements of I are set to true
                    for lit in model:
                        # lit in already derived facts must be true because added as single literals
                        if [lit] in I_cnf:
                            model_i.add(lit)
                        # lit in remaining cnfs of MSS
                        elif abs(lit) in mss_cnf_lits:
                            model_i.add(lit)
                    MSS_i.append((mss_i, model_i))
                    
                hs, explanation = o.omusIncr(MSSes=MSS_i)
            else:
                hs, explanation = o.omusIncr()

            # explaining facts
            E_i = [ci for ci in explanation if ci in I_cnf]

            # constraint used ('and not ci in E_i': dont repeat unit clauses)
            # TODO: aanpassen constraints
            S_i = [ci for ci in explanation if ci in cnf and ci not in E_i]
            # new fact
            N_i = {i}

            if cost_best is None or cost((E_i, S_i, N_i)) < cost_best:
                E_best, S_best, N_best = E_i, S_i, N_i
                cost_best = cost((E_i, S_i, N_i))
                i_best = i

            MSSes = o.MSSes
            # M[i].append()
            for mss, mss_model in MSSes:
                # seperate components mss [cnf, I, -i]
                # order of cnf part will never change!
                mss_cnf = mss.intersection(cnf_idx)
                # order of I might change!
                mss_I = [unsat_cnf[idx] for idx in mss.intersection(I_idx)]

                M[i].append((mss_cnf, mss_I, mss_model))

        del M[i_best]
        I |= N_best
        # I |= (N_i - model)
        seq.append((E_best, S_best, N_best))

        print(f"Facts:\n\t{E_best}  \nClause:\n\t{S_best} \n=> Derive (at cost {cost_best}) \n\t{N_best}")

    assert all(False if -lit in I else True for lit in I)

    return seq


def main():
    # explain
    parameters = {'extension': 'greedy_no_param','output': 'log.json'}
    cppy_model = frietKotProblem()
    cnf = cnf_to_pysat(cppy_model.constraints)
    seq = omusExplain(cnf, weights=[len(c) for c in cnf], parameters=parameters, incremental=True)
    # print(seq)


if __name__ == "__main__":
    main()
