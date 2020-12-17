import itertools
import sys

# import numpy
import pandas as pd

sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
sys.path.append('/home/emilio/Documents/cppy_src/')
sys.path.append('/home/emilio/documents/cppy_mysrc/')
sys.path.append('/user/brussel/101/vsc10143/cppy_src')

from cppy import BoolVarImpl, Comparison, Model, Operator, cnf_to_pysat

from cppy import *
from cppy.model_tools.to_cnf import *

# Relation between 'rows' and 'cols', Boolean Variables in a pandas dataframe
class Relation(object):
    # rows, cols: list of names
    def __init__(self, rows, cols):
        rel = BoolVar((len(rows), len(cols)))
        self.df = pd.DataFrame(index=rows, columns=cols)
        for i,r in enumerate(rows):
            for j,c in enumerate(cols):
                self.df.loc[r,c] = rel[i,j]
    # use as: rel['a','b']
    def __getitem__(self, key):
        try:
            return self.df.loc[key]
        except KeyError:
            return False


def exactly_one(lst):
    # return sum(lst) == 1
    # (l1|l2|..|ln) & (-l1|-l2) & ...
    allpairs = [(-a|-b) for a,b in itertools.combinations(lst, 2)]
    return [any(lst)] + allpairs


def originProblemReify():
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
    cnt = 0
    bij = []
    bv_bij = [BoolVar() for i in range(60)]

    for rel in [is_old, lives_in, native, age_city, age_birth, city_birth]:
        # for each relation
        for col_ids in rel.df:
            # one per column
            [bij.append(bv_bij[cnt] == clause) for clause in exactly_one(rel[:, col_ids])]
            cnt += 1
        for (_,row) in rel.df.iterrows():
            # one per row
            [bij.append( bv_bij[cnt] == clause) for clause in exactly_one(row)]
            cnt += 1

    # # Transitivity
    # trans = []
    # bv_trans = [BoolVar() for i in range(12)]
    # for x in person:
    #     for z in birthplace:
    #         for y in age:
    #             # ! x y z:  from(x, z) & is_linked_with_1(y, z) => is_old(x, y).
    #             # t0 = to_cnf(implies( native[x, z] & age_birth[y, z], is_old[x, y]))
    #             trans.append(implies(bv_trans[0], ( ~native[x, z] | ~age_birth[y, z] | is_old[x, y] )))

    #              # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[1], ( native[x, z] | ~age_birth[y, z] | ~is_old[x, y] )))

    #              # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[2], ( ~native[x, z] | age_birth[y, z] | ~is_old[x, y] )))

    # for x in person :
    #     for y in age :
    #         for z in city :

    #             # ! x y z:  lives_in(x, z) & is_linked_with_2(y, z) => is_old[x, y].

    #             trans.append(implies(bv_trans[3], ( ~lives_in[x, z] | ~age_city[y, z] | is_old[x, y] )))

    #              # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[4], ( lives_in[x, z] | ~age_city[y, z] | ~is_old[x, y] )))

    #              # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[5], ( ~lives_in[x, z] | age_city[y, z] | ~is_old[x, y] )))



    # for x in person :
    #     for y in birthplace :
    #         for z in city :
    #             # ! x y z:  lives_in(x, z) & is_linked_with_2(y, z) => is_old[x, y].
    #             trans.append(implies(bv_trans[6], ( ~lives_in[x, z] | ~city_birth[z, y] | native[x, y] )))
    #              # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[7], ( lives_in[x, z] | ~city_birth[z, y] | ~native[x, y] )))
    #              # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[8], ( ~lives_in[x, z] | city_birth[z, y] | ~native[x, y] )))




    # for x in age :
    #     for y in birthplace:
    #         for z in city :
    #             #  ! x y z:  is_linked_with_2(x, z) & is_linked_with_3(y, z) => is_linked_with_1(x, y).
    #             trans.append(implies(bv_trans[9], ( ~age_city[x, z] | ~city_birth[z, y] | age_birth[x, y] )))

    #             # ! x y z:  ~is_linked_with_2(x, z) & is_linked_with_3(y, z) => ~is_linked_with_1(x, y).
    #             trans.append(implies(bv_trans[10], ( age_city[x, z] | ~city_birth[z, y] | ~age_birth[x, y] )))

    #             # ! x y z:  is_linked_with_2(x, z) & ~is_linked_with_3(y, z) => ~is_linked_with_1(x, y).
    #             trans.append(implies(bv_trans[11], ( ~age_city[x, z] | city_birth[z, y] | ~age_birth[x, y] )))

    # clues = []
    # bv_clues = [BoolVar() for i in range(10)]
    # clues.append(implies(bv_clues[0], is_old['Mattie', '113']))

    # # The person who lives in Tehama is a native of either Kansas or Oregon
    # [clues.append(implies(bv_clues[1], (~lives_in[p, 'Tehama'] | native[p, 'Kansas'] | native[p, 'Oregon']))) for p in person]

    # # The Washington native is 1 year older than Ernesto
    # [clues.append(implies(bv_clues[2], (~age_birth[a, 'Washington'] | is_old['Ernesto', str(int(a)-1)]) )) for a in age]

    # # Roxanne is 2 years younger than the Kansas native
    # [clues.append(implies(bv_clues[3], ( ~is_old['Roxanne', a] | age_birth[str(int(a)+2), 'Kansas']))) for a in age]

    # # The person who lives in Zearing isn't a native of Alaska
    # c4a = to_cnf([implies(lives_in[p, 'Zearing'], ~native[p, 'Alaska']) for p in person])
    # [clues.append(implies(bv_clues[4], clause)) for clause in c4a]

    # # The person who is 111 years old doesn't live in Plymouth
    # c5a = to_cnf([implies(is_old[p, '111'], ~lives_in[p, 'Plymouth']) for p in person])
    # [clues.append(implies(bv_clues[5], clause)) for clause in c5a]

    # # The Oregon native is either Zachary or the person who lives in Tehama
    # c6a = to_cnf([implies(native[p, 'Oregon'], (p == 'Zachary') | lives_in[p, 'Tehama']) for p in person])
    # [clues.append(implies(bv_clues[6], clause)) for clause in c6a]

    # # The person who lives in Shaver Lake is 1 year younger than Roxanne
    # c7a = to_cnf([implies(age_city[a, 'Shaver Lake'], is_old['Roxanne', str(int(a)+1)]) for a in age])
    # [clues.append(implies(bv_clues[7], clause)) for clause in c7a]

    # # The centenarian who lives in Plymouth isn't a native of Alaska
    # c8a = to_cnf([implies(lives_in[p, 'Plymouth'], ~native[p, 'Alaska']) for p in person])

    # [clues.append(implies(bv_clues[8], clause)) for clause in c8a]

    # # Of the person who lives in Tehama and Mattie, one is a native of Alaska and the other is from Kansas
    # c9a = to_cnf([implies(lives_in[p, 'Tehama'],
    #                       (p != 'Mattie') &
    #                       ((native['Mattie', 'Alaska'] & native[p, 'Kansas']) |
    #                        (native[p, 'Alaska'] & native['Mattie', 'Kansas']))) for p in person])
    # [clues.append(implies(bv_clues[9], clause)) for clause in c9a]
    # Transitivity
    trans = []
    bv_trans = [BoolVar() for i in range(12)]
    for x in person:
        for z in birthplace:
            for y in age:
                # ! x y z:  from(x, z) & is_linked_with_1(y, z) => is_old(x, y).
                # t0 = to_cnf(implies( native[x, z] & age_birth[y, z], is_old[x, y]))
                trans.append(bv_trans[0] == ( ~native[x, z] | ~age_birth[y, z] | is_old[x, y] ))

                 # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
                trans.append(bv_trans[1] == ( native[x, z] | ~age_birth[y, z] | ~is_old[x, y] ))

                 # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
                trans.append(bv_trans[2] == ( ~native[x, z] | age_birth[y, z] | ~is_old[x, y] ))

    for x in person :
        for y in age :
            for z in city :

                # ! x y z:  lives_in(x, z) & is_linked_with_2(y, z) => is_old[x, y].

                trans.append(bv_trans[3] == ( ~lives_in[x, z] | ~age_city[y, z] | is_old[x, y] ))

                 # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
                trans.append(bv_trans[4] == ( lives_in[x, z] | ~age_city[y, z] | ~is_old[x, y] ))

                 # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
                trans.append(bv_trans[5] == ( ~lives_in[x, z] | age_city[y, z] | ~is_old[x, y] ))

    for x in person :
        for y in birthplace :
            for z in city :
                # ! x y z:  lives_in(x, z) & is_linked_with_2(y, z) => is_old[x, y].
                trans.append(bv_trans[6] == ( ~lives_in[x, z] | ~city_birth[z, y] | native[x, y] ))
                 # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
                trans.append(bv_trans[7] == ( lives_in[x, z] | ~city_birth[z, y] | ~native[x, y] ))
                 # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
                trans.append(bv_trans[8]== ( ~lives_in[x, z] | city_birth[z, y] | ~native[x, y] ))


    for x in age :
        for y in birthplace:
            for z in city :
                #  ! x y z:  is_linked_with_2(x, z) & is_linked_with_3(y, z) => is_linked_with_1(x, y).
                trans.append(bv_trans[9] == ( ~age_city[x, z] | ~city_birth[z, y] | age_birth[x, y] ))

                # ! x y z:  ~is_linked_with_2(x, z) & is_linked_with_3(y, z) => ~is_linked_with_1(x, y).
                trans.append(bv_trans[10] == ( age_city[x, z] | ~city_birth[z, y] | ~age_birth[x, y] ))

                # ! x y z:  is_linked_with_2(x, z) & ~is_linked_with_3(y, z) => ~is_linked_with_1(x, y).
                trans.append(bv_trans[11] == ( ~age_city[x, z] | city_birth[z, y] | ~age_birth[x, y] ))

    clues = []
    bv_clues = [BoolVar() for i in range(10)]
    clues.append(bv_clues[0] == is_old['Mattie', '113'])

    # The person who lives in Tehama is a native of either Kansas or Oregon
    [clues.append(bv_clues[1] == (~lives_in[p, 'Tehama'] | native[p, 'Kansas'] | native[p, 'Oregon'])) for p in person]

    # The Washington native is 1 year older than Ernesto
    [clues.append(bv_clues[2] == (~age_birth[a, 'Washington'] | is_old['Ernesto', str(int(a)-1)]) ) for a in age]

    # Roxanne is 2 years younger than the Kansas native
    [clues.append(bv_clues[3] == ( ~is_old['Roxanne', a] | age_birth[str(int(a)+2), 'Kansas'])) for a in age]

    # The person who lives in Zearing isn't a native of Alaska
    [clues.append(bv_clues[4] == (~lives_in[p, 'Zearing'] | ~native[p, 'Alaska'])) for p in person]

    # The person who is 111 years old doesn't live in Plymouth
    [clues.append( bv_clues[5] == (~is_old[p, '111'] | ~lives_in[p, 'Plymouth'])) for p in person]

    # The Oregon native is either Zachary or the person who lives in Tehama
    [clues.append(bv_clues[6] == (~native[p, 'Oregon'] | (p == 'Zachary') | lives_in[p, 'Tehama'])) for p in person]

    # The person who lives in Shaver Lake is 1 year younger than Roxanne
    [clues.append(bv_clues[7] == (~age_city[a, 'Shaver Lake'] | is_old['Roxanne', str(int(a)+1)])) for a in age]

    # The centenarian who lives in Plymouth isn't a native of Alaska
    [clues.append(bv_clues[8] == (~lives_in[p, 'Plymouth'] | ~native[p, 'Alaska'])) for p in person]

    # Of the person who lives in Tehama and Mattie, one is a native of Alaska and the other is from Kansas
    c9a = to_cnf([implies(lives_in[p, 'Tehama'],
                          (p != 'Mattie') &
                          ((native['Mattie', 'Alaska'] & native[p, 'Kansas']) |
                           (native[p, 'Alaska'] & native['Mattie', 'Kansas']))) for p in person])
    [clues.append(bv_clues[9] == clause) for clause in c9a]

    rels = [is_old, lives_in, native, age_city, age_birth, city_birth]

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))
    # print(len(clues_cnf))

    hard_clauses = [c for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [[bv1.name + 1] for bv1 in bv_clues]
    soft_clauses += [[bv1.name + 1]  for bv1 in bv_bij]
    soft_clauses += [[bv1.name + 1]  for bv1 in bv_trans]

    weights = {}
    weights.update({bv.name + 1: 100 for bv in bv_clues})
    weights.update({bv.name + 1: 60 for bv in bv_trans})
    weights.update({bv.name + 1: 60 for bv in bv_bij})
    weights.update({-(bv.name + 1): 100 for bv in bv_clues})
    weights.update({-(bv.name + 1): 60 for bv in bv_trans})
    weights.update({-(bv.name + 1): 60 for bv in bv_bij})

    explainable_facts = set()
    for rel in rels:
        print(rel.df)
        # print()
        for item in rel.df.values:
            explainable_facts |= set(i.name+1 for i in item)

    return hard_clauses, soft_clauses, weights, explainable_facts


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
    cnt = 0
    bij = []
    bv_bij = [BoolVar() for i in range(60)]

    for rel in [is_old, lives_in, native, age_city, age_birth, city_birth]:
        # for each relation
        for col_ids in rel.df:
            # one per column
            # bij += exactly_one(rel[:, col_ids])
            # b1 = to_cnf(exactly_one(rel[:, col_ids]))
            [bij.append(implies(bv_bij[cnt], clause)) for clause in exactly_one(rel[:, col_ids])]

            # [bij.append(implies(bv_bij[cnt], clause)) for clause in b1]
            cnt += 1
        for (_,row) in rel.df.iterrows():
            # one per row
            # bij += exactly_one(row)
            # b2 = to_cnf(exactly_one(row))
            [bij.append( implies(bv_bij[cnt], clause) ) for clause in exactly_one(row)]
            cnt += 1

    # # Transitivity
    trans = []
    bv_trans = [BoolVar() for i in range(12)]
    # for x in person:
    #     for z in birthplace:
    #         for y in age:
    #             # ! x y z:  from(x, z) & is_linked_with_1(y, z) => is_old(x, y).
    #             # t0 = to_cnf(implies( native[x, z] & age_birth[y, z], is_old[x, y]))
    #             trans.append(implies(bv_trans[0], ( ~native[x, z] | ~age_birth[y, z] | is_old[x, y] )))

    #              # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[1], ( native[x, z] | ~age_birth[y, z] | ~is_old[x, y] )))

    #              # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[2], ( ~native[x, z] | age_birth[y, z] | ~is_old[x, y] )))

    # for x in person :
    #     for y in age :
    #         for z in city :

    #             # ! x y z:  lives_in(x, z) & is_linked_with_2(y, z) => is_old[x, y].

    #             trans.append(implies(bv_trans[3], ( ~lives_in[x, z] | ~age_city[y, z] | is_old[x, y] )))

    #              # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[4], ( lives_in[x, z] | ~age_city[y, z] | ~is_old[x, y] )))

    #              # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[5], ( ~lives_in[x, z] | age_city[y, z] | ~is_old[x, y] )))



    # for x in person :
    #     for y in birthplace :
    #         for z in city :
    #             # ! x y z:  lives_in(x, z) & is_linked_with_2(y, z) => is_old[x, y].
    #             trans.append(implies(bv_trans[6], ( ~lives_in[x, z] | ~city_birth[z, y] | native[x, y] )))
    #              # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[7], ( lives_in[x, z] | ~city_birth[z, y] | ~native[x, y] )))
    #              # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
    #             trans.append(implies(bv_trans[8], ( ~lives_in[x, z] | city_birth[z, y] | ~native[x, y] )))




    # for x in age :
    #     for y in birthplace:
    #         for z in city :
    #             #  ! x y z:  is_linked_with_2(x, z) & is_linked_with_3(y, z) => is_linked_with_1(x, y).
    #             trans.append(implies(bv_trans[9], ( ~age_city[x, z] | ~city_birth[z, y] | age_birth[x, y] )))

    #             # ! x y z:  ~is_linked_with_2(x, z) & is_linked_with_3(y, z) => ~is_linked_with_1(x, y).
    #             trans.append(implies(bv_trans[10], ( age_city[x, z] | ~city_birth[z, y] | ~age_birth[x, y] )))

    #             # ! x y z:  is_linked_with_2(x, z) & ~is_linked_with_3(y, z) => ~is_linked_with_1(x, y).
    #             trans.append(implies(bv_trans[11], ( ~age_city[x, z] | city_birth[z, y] | ~age_birth[x, y] )))

    # clues = []
    # bv_clues = [BoolVar() for i in range(10)]
    # clues.append(implies(bv_clues[0], is_old['Mattie', '113']))

    # # The person who lives in Tehama is a native of either Kansas or Oregon
    # [clues.append(implies(bv_clues[1], (~lives_in[p, 'Tehama'] | native[p, 'Kansas'] | native[p, 'Oregon']))) for p in person]

    # # The Washington native is 1 year older than Ernesto
    # [clues.append(implies(bv_clues[2], (~age_birth[a, 'Washington'] | is_old['Ernesto', str(int(a)-1)]) )) for a in age]

    # # Roxanne is 2 years younger than the Kansas native
    # [clues.append(implies(bv_clues[3], ( ~is_old['Roxanne', a] | age_birth[str(int(a)+2), 'Kansas']))) for a in age]

    # # The person who lives in Zearing isn't a native of Alaska
    # [clues.append(implies(bv_clues[4], ~lives_in[p, 'Zearing']| ~native[p, 'Alaska'])) for p in person]

    # # The person who is 111 years old doesn't live in Plymouth
    # [clues.append(implies(bv_clues[5], ~is_old[p, '111']| ~lives_in[p, 'Plymouth'])) for p in person]

    # # The Oregon native is either Zachary or the person who lives in Tehama
    # [clues.append(implies(bv_clues[6], ~native[p, 'Oregon'] | (p == 'Zachary') | lives_in[p, 'Tehama'])) for p in person]

    # # The person who lives in Shaver Lake is 1 year younger than Roxanne
    # [clues.append(implies(bv_clues[7], ~age_city[a, 'Shaver Lake'] | is_old['Roxanne', str(int(a)+1)])) for a in age]

    # # The centenarian who lives in Plymouth isn't a native of Alaska
    # [clues.append(implies(bv_clues[8], ~lives_in[p, 'Plymouth'] | ~native[p, 'Alaska'])) for p in person]

    # # Of the person who lives in Tehama and Mattie, one is a native of Alaska and the other is from Kansas
    # c9a = to_cnf([implies(lives_in[p, 'Tehama'],
    #                       (p != 'Mattie') &
    #                       ((native['Mattie', 'Alaska'] & native[p, 'Kansas']) |
    #                        (native[p, 'Alaska'] & native['Mattie', 'Kansas']))) for p in person])
    # [clues.append(implies(bv_clues[9], clause)) for clause in c9a]
    # for rel in [is_old, lives_in, native, age_city, age_birth, city_birth]:
    #     # for each relation
    #     for col_ids in rel.df:
    #         # one per column
    #         # bij += exactly_one(rel[:, col_ids])
    #         b1 = to_cnf(exactly_one(rel[:, col_ids]))
    #         [bij.append(implies(bv_bij[cnt], clause)) for clause in b1]
    #         cnt += 1
    #     for (_,row) in rel.df.iterrows():
    #         # one per row
    #         # bij += exactly_one(row)
    #         b2 = to_cnf(exactly_one(row))
    #         [bij.append( implies(bv_bij[cnt] , clause) ) for clause in b2]
    #         cnt += 1

    # # Transitivity
    # trans = []
    # bv_trans =  [BoolVar() for i in range(12)]
    for x in person:
        for z in birthplace:
            for y in age:
                # ! x y z:  from(x, z) & is_linked_with_1(y, z) => is_old(x, y).
                t0 = to_cnf(implies( native[x, z] & age_birth[y, z], is_old[x, y]))
                [trans.append(implies(bv_trans[0], clause)) for clause in t0]
                # trans.append( ~bv_trans[0] |  ~native[x, z] | ~age_birth[y, z] | is_old[x, y] )

                 # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
                # trans.append(implies(bv_trans[1], ( native[x, z] | ~age_birth[y, z] | ~is_old[x, y] )))
                t1 = to_cnf(implies( ~native[x, z] & age_birth[y, z], ~is_old[x, y]))
                [trans.append(implies(bv_trans[1], clause)) for clause in t1]
                # trans.append(~ bv_trans[1] |  native[x, z] | ~ age_birth[y, z] | ~is_old[x, y])

                # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
                t2 = to_cnf(implies( native[x, z] & ~age_birth[y, z], ~is_old[x, y]))
                [trans.append(implies(bv_trans[2], clause)) for clause in t2]
                # trans.append(implies(bv_trans[2], ( ~native[x, z] | age_birth[y, z] | ~is_old[x, y] )))

    for x in person :
        for y in age :
            for z in city :
                # ! x y z:  lives_in(x, z) & is_linked_with_2(y, z) => is_old[x, y].
                t3 = to_cnf(implies( lives_in[x, z] & age_city[y, z], is_old[x, y]))
                [trans.append(implies(bv_trans[3], clause)) for clause in t3]

                # ! x y z:  ~lives_in(x, z) & is_linked_with_2(y, z) => ~is_old(x, y).
                t4 = to_cnf(implies( ~lives_in[x, z] & age_city[y, z], ~is_old[x, y]))
                [trans.append(implies(bv_trans[4], clause)) for clause in t4]

                # ! x y z:  lives_in(x, z) & ~is_linked_with_2(y, z) => ~is_old(x, y).
                t5 = to_cnf(implies( lives_in[x, z] & ~age_city[y, z], ~is_old[x, y]))
                [trans.append(implies(bv_trans[5], clause)) for clause in t5]

    for x in person :
        for y in birthplace :
            for z in city :
                #  ! x y z:  lives_in(x, z) & is_linked_with_3(y, z) => from(x, y).
                t6 =to_cnf(implies( lives_in[x, z] & city_birth[z, y] , native[x, y] ))
                [trans.append(implies(bv_trans[6], clause)) for clause in t6]

                # ! x y z:  ~lives_in(x, z) & is_linked_with_3(y, z) => ~from(x, y).
                t7 = to_cnf(implies( ~lives_in[x, z] & city_birth[z, y] , ~native[x, y]))
                [trans.append(implies(bv_trans[7], clause)) for clause in t7]

                # ! x y z:  lives_in(x, z) & ~is_linked_with_3(y, z) => ~from(x, y).
                t8 = to_cnf(implies( lives_in[x, z] & ~city_birth[z, y] , ~native[x, y] ))
                [trans.append(implies(bv_trans[8], clause)) for clause in t8]

    for x in age :
        for y in birthplace:
            for z in city :
                #  ! x y z:  is_linked_with_2(x, z) & is_linked_with_3(y, z) => is_linked_with_1(x, y).
                t9 = to_cnf(implies( age_city[x, z] & city_birth[z, y], age_birth[x, y]))
                [trans.append(implies(bv_trans[9], clause)) for clause in t9]

                # ! x y z:  ~is_linked_with_2(x, z) & is_linked_with_3(y, z) => ~is_linked_with_1(x, y).
                t10 = to_cnf(implies( ~age_city[x, z] & city_birth[z, y], ~age_birth[x, y]))
                [trans.append(implies(bv_trans[10], clause)) for clause in t10]

                # ! x y z:  is_linked_with_2(x, z) & ~is_linked_with_3(y, z) => ~is_linked_with_1(x, y).
                t11 = to_cnf(implies( age_city[x, z] & ~city_birth[z, y], ~age_birth[x, y]))
                [trans.append(implies(bv_trans[11], clause)) for clause in t11]

    clues = []
    bv_clues = [BoolVar() for i in range(10)]
    clues.append(implies(bv_clues[0], is_old['Mattie', '113']))

    # The person who lives in Tehama is a native of either Kansas or Oregon
    c1a = to_cnf([implies(lives_in[p, 'Tehama'], native[p, 'Kansas'] | native[p, 'Oregon']) for p in person])

    [clues.append(implies(bv_clues[1], clause)) for clause in c1a]

    # The Washington native is 1 year older than Ernesto
    c2a = to_cnf([implies(age_birth[a, 'Washington'], is_old['Ernesto', str(int(a)-1)]) for a in age])
    [clues.append(implies(bv_clues[2], clause)) for clause in c2a]

    # Roxanne is 2 years younger than the Kansas native
    c3a = to_cnf([implies(is_old['Roxanne', a], age_birth[str(int(a)+2), 'Kansas']) for a in age])
    [clues.append(implies(bv_clues[3], clause)) for clause in c3a]

    # The person who lives in Zearing isn't a native of Alaska
    c4a = to_cnf([implies(lives_in[p, 'Zearing'], ~native[p, 'Alaska']) for p in person])
    [clues.append(implies(bv_clues[4], clause)) for clause in c4a]

    # The person who is 111 years old doesn't live in Plymouth
    c5a = to_cnf([implies(is_old[p, '111'], ~lives_in[p, 'Plymouth']) for p in person])
    [clues.append(implies(bv_clues[5], clause)) for clause in c5a]

    # The Oregon native is either Zachary or the person who lives in Tehama
    c6a = to_cnf([implies(native[p, 'Oregon'], (p == 'Zachary') | lives_in[p, 'Tehama']) for p in person])
    [clues.append(implies(bv_clues[6], clause)) for clause in c6a]

    # The person who lives in Shaver Lake is 1 year younger than Roxanne
    c7a = to_cnf([implies(age_city[a, 'Shaver Lake'], is_old['Roxanne', str(int(a)+1)]) for a in age])
    [clues.append(implies(bv_clues[7], clause)) for clause in c7a]

    # The centenarian who lives in Plymouth isn't a native of Alaska
    c8a = to_cnf([implies(lives_in[p, 'Plymouth'], ~native[p, 'Alaska']) for p in person])
    [clues.append(implies(bv_clues[8], clause)) for clause in c8a]

    # Of the person who lives in Tehama and Mattie, one is a native of Alaska and the other is from Kansas
    c9a = to_cnf([implies(lives_in[p, 'Tehama'],
                          (p != 'Mattie') &
                          ((native['Mattie', 'Alaska'] & native[p, 'Kansas']) |
                           (native[p, 'Alaska'] & native['Mattie', 'Kansas']))) for p in person])
    [clues.append(implies(bv_clues[9], clause)) for clause in c9a]

    rels = [is_old, lives_in, native, age_city, age_birth, city_birth]

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))
    # print(len(clues_cnf))

    hard_clauses = [c for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [[bv1.name + 1] for bv1 in bv_clues]
    soft_clauses += [[bv1.name + 1]  for bv1 in bv_bij]
    soft_clauses += [[bv1.name + 1]  for bv1 in bv_trans]

    weights = {}
    weights.update({bv.name + 1: 100 for bv in bv_clues})
    weights.update({bv.name + 1: 60 for bv in bv_trans})
    weights.update({bv.name + 1: 60 for bv in bv_bij})
    weights.update({-(bv.name + 1): 100 for bv in bv_clues})
    weights.update({-(bv.name + 1): 60 for bv in bv_trans})
    weights.update({-(bv.name + 1): 60 for bv in bv_bij})

    explainable_facts = set()
    for rel in rels:
        print(rel.df)
        # print()
        for item in rel.df.values:
            explainable_facts |= set(i.name+1 for i in item)
    
    return hard_clauses, soft_clauses, weights, explainable_facts, {'trans': [bv.name + 1 for bv in bv_trans], 'bij': [bv.name + 1 for bv in bv_bij], 'clues' : {bv.name + 1: i for i, bv in enumerate(bv_clues)}}


def simplestProblemReify():
    (mayo, ketchup) = BoolVar(2)
    b = BoolVar(2)
    c0 = (b[0] == mayo)
    c1 = (b[1] == (~mayo | ketchup))

    constraints = [c0, c1]
    c = to_cnf(constraints)
    cnf = cnf_to_pysat(c)
    user_vars = [mayo.name+1, ketchup.name+1]
    return cnf, [bi.name + 1 for bi in b], user_vars


def simpleProblem():
    (mayo, ketchup, andalouse) = BoolVar(3)
    print("Mayo=", mayo.name+1)
    print("ketchup=", ketchup.name+1)
    print("andalouse=", andalouse.name+1)

    c0 = mayo
    c1 = ~mayo | ~andalouse | ketchup
    c2 = ~mayo | andalouse | ketchup
    c3 = ~ketchup | ~andalouse

    constraints = [c0, c1, c2, c3]
    # print()

    cnf = cnf_to_pysat(constraints)

    return [list(c) for c in cnf]


def frietKotProblemReify():
    # Construct the model.
    (mayo, ketchup, curry, andalouse, samurai) = BoolVar(5)

    print("Mayo=", mayo.name+1)
    print("ketchup=", ketchup.name+1)
    print("andalouse=", andalouse.name+1)
    print("curry=", curry.name+1)
    print("samurai=", samurai.name+1)

    print(f"6.  Nora = {mayo.name+1} | {ketchup.name+1}", )
    print(f"7.  Leander = ~{samurai.name+1} | {mayo.name+1}")
    print(f"8.  Benjamin = ~{andalouse.name+1} | ~{curry.name+1} | ~{samurai.name+1}")
    print(f"9.  Behrouz = {ketchup.name+1} | {curry.name+1} | {andalouse.name+1}")
    print(f"10. Guy = ~{ketchup.name+1} | {curry.name+1} | {andalouse.name+1}")
    print(f"11. Daan = ~{ketchup.name+1} | ~{curry.name+1} | {andalouse.name+1}")
    print(f"12. Celine = ~{samurai.name+1}")
    print(f"13. Anton = {mayo.name+1} | ~{curry.name+1} | ~{andalouse.name+1}")
    print(f"14. Danny = ~{mayo.name+1} | {ketchup.name+1} | {andalouse.name+1} | {samurai.name+1}")
    print(f"15. Luc = ~{mayo.name+1} | {samurai.name+1}")

    Nora = mayo | ketchup
    Leander = ~samurai | mayo
    Benjamin = ~andalouse | ~curry | ~samurai
    Behrouz = ketchup | curry | andalouse
    Guy = ~ketchup | curry | andalouse
    Daan = ~ketchup | ~curry | andalouse
    Celine = ~samurai
    Anton = mayo | ~curry | ~andalouse
    Danny = ~mayo | ketchup | andalouse | samurai
    Luc = ~mayo | samurai


    wishes = [Nora, Leander, Benjamin, Behrouz, Guy, Daan, Celine, Anton, Danny, Luc]
    bvs = BoolVar(len(wishes))
    allwishes = [bv == wish for bv, wish in zip(bvs, wishes)]

    cnf = cnf_to_pysat(to_cnf(allwishes))
    explainable_facts = set([mayo.name+1, ketchup.name+1,andalouse.name+1, curry.name+1, samurai.name+1])

    return [list(c) for c in cnf], [bi.name + 1 for bi in bvs], explainable_facts


def frietKotProblem():
    # Construct the model.
    (mayo, ketchup, curry, andalouse, samurai) = BoolVar(5)

    print("Mayo=", mayo.name+1)
    print("ketchup=", ketchup.name+1)
    print("andalouse=", andalouse.name+1)
    print("curry=", curry.name+1)
    print("samurai=", samurai.name+1)

    print(f"6.  Nora = {mayo.name+1} | {ketchup.name+1}", )
    print(f"7.  Leander = ~{samurai.name+1} | {mayo.name+1}")
    print(f"8.  Benjamin = ~{andalouse.name+1} | ~{curry.name+1} | ~{samurai.name+1}")
    print(f"9.  Behrouz = {ketchup.name+1} | {curry.name+1} | {andalouse.name+1}")
    print(f"10. Guy = ~{ketchup.name+1} | {curry.name+1} | {andalouse.name+1}")
    print(f"11. Daan = ~{ketchup.name+1} | ~{curry.name+1} | {andalouse.name+1}")
    print(f"12. Celine = ~{samurai.name+1}")
    print(f"13. Anton = {mayo.name+1} | ~{curry.name+1} | ~{andalouse.name+1}")
    print(f"14. Danny = ~{mayo.name+1} | {ketchup.name+1} | {andalouse.name+1} | {samurai.name+1}")
    print(f"15. Luc = ~{mayo.name+1} | {samurai.name+1}")

    Nora = mayo | ketchup
    Leander = ~samurai | mayo
    Benjamin = ~andalouse | ~curry | ~samurai
    Behrouz = ketchup | curry | andalouse
    Guy = ~ketchup | curry | andalouse
    Daan = ~ketchup | ~curry | andalouse
    Celine = ~samurai
    Anton = mayo | ~curry | ~andalouse
    Danny = ~mayo | ketchup | andalouse | samurai
    Luc = ~mayo | samurai

    allwishes = [Nora, Leander, Benjamin, Behrouz, Guy, Daan, Celine, Anton, Danny, Luc]
    cnf = cnf_to_pysat(allwishes)
    explainable_facts = set([mayo.name+1, ketchup.name+1,andalouse.name+1, curry.name+1, samurai.name+1])

    return [list(c) for c in cnf], explainable_facts

