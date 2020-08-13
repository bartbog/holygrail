from OMUS import omus, omusIncremental
import json
from frietkot import frietKotProblem
from pysat.solvers import Solver
from pysat.formula import CNF
import sys
sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
from cppy import Model, tseitin, BoolVarImpl, Operator, Comparison, cnf_to_pysat

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
    nClues =  0
    nOthers = len(constraints) - nClues
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
    I_prop = set(I)
    
    return I_prop


def omusExplain(cnf, I_0=set(), weights=None, parameters=None, output='explanation.json'):
    cnf_idx = set(i for i in range(len(cnf)))
    I_end = frozenset(maxPropagate(cnf, I_0))
    I = I_0
    seq = []

    # print(set(I_end) - set(I))
    print(I_end - I)
    # clausesUsed = set()
    while len(I_end - I) > 0:
        # expls = []
        unsat_cnf = list(cnf)
        w_cnf = list(weights)

        if len(I) > 0:
            unsat_cnf += [[li] for li in I]
            w_cnf += [1 for li in I]

        E_best, S_best, N_best = None, None, None
        cost_best = 100000

        for i in I_end - I:
            unsat_cnf = cnf + [[-i]]
            w_cnf = weights + [1]

            omus_idx = omusIncremental(CNF(from_clauses=unsat_cnf), parameters=parameters, weights=w_cnf)
            explanation = [unsat_cnf[idx] for idx in omus_idx]

            # constraint used
            S_i = [ci for ci in explanation if ci in cnf]

            # explaining facts
            E_i = [ci for ci in explanation if ci in [[li] for li in I]]

            # new fact
            N_i = {i}

            # print("cnf=", unsat_cnf)
            # print("expl=", explanation)
            # print("S_i=", S_i)
            # print("E_i=", E_i, "\n")
            if cost((E_i, S_i, N_i)) < cost_best:
                E_best, S_best, N_best = E_i, S_i, N_i
                cost_best = cost((E_i, S_i, N_i))

        # find min cost explanation
        # print(E_best,"----", explanation,"----", S_best)
        # print(I, E_best)
        # S_cnf = [ci for i, ci in enumerate(cnf) if i in S_best]
        # propagate to find new information covered by current assignment
        # N_best = propagate(S_cnf, I=list(E_best))

        I |= N_best
        seq.append((E_best, S_best, N_best))


    for (E_i, S_i, N_i) in seq:

        print(f"Facts:\n\t{E_i}  \nClause:\n\t{S_i} \n=> Derive \n\t{N_i}")
        # print((E_i, S_i, N_i))
    assert all(False if -lit in I else True for lit in I)
    # I = I.union(N_best)

    # while I != I_end:
    #     expls = []
        # for i in I_end - I:
        #     omus_cnf = [[-i], [I]] + cnf
        #     X_i = omus(omus_cnf, parameters, f=f)
        #     lits = X_i
        #     E_i = I.intersection(X_i)
        #     S_i = X_i
        #     N_i = propagate(S_i, E_i)
        #     expls.append((E_i, S_i, N_i))

        # seq.append((E_best, S_best, N_best))
        # I.add({N_best})

    return seq


# def omusExplainIncr(cnf, f, i0, parameters=None, output='explanation.json'):
#     I_end = propagate(cnf, I_0)
#     I = I_0
#     seq = []
#     M = []

#     while I != I_end:
#         expls = []
#         for i in I_end - I:
#             omus_cnf = [[-i], [I]] + cnf
#             X_i, MSSes = omusIncremental(omus_cnf, parameters, f=f, M=None)
#             lits = X_i
#             E_i = I.intersection(X_i)
#             S_i = X_i
#             N_i = propagate(S_i, E_i)
#             expls.append((E_i, S_i, N_i))
#             M += MSSes

#         (E_best, S_best, N_best) = min(expls, lambda e: f(e[0], e[1], e[2]))
#         seq.append((E_best, S_best, N_best))
#         I.add({N_best})

#     return seq


def main():
    # explain
    parameters = {'extension': 'greedy_no_param','output': 'log.json'}
    cppy_model = frietKotProblem()
    cnf = cnf_to_pysat(cppy_model.constraints)
    seq = omusExplain(cnf, weights=[len(c) for c in cnf], parameters=parameters)
    # print(seq)


if __name__ == "__main__":
    main()