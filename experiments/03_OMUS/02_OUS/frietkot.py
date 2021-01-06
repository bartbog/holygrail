import itertools
import sys

# import numpy
import pandas as pd

sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src/')
sys.path.append('/home/emilio/Documents/cppy_src/')
sys.path.append('/home/emilio/documents/cppy_mysrc/')
sys.path.append('/user/brussel/101/vsc10143/cppy_src/')

from cppy import cnf_to_pysat

from cppy import *
from cppy.model_tools.to_cnf import *

# Relation between 'rows' and 'cols', Boolean Variables in a pandas dataframe
class Relation(object):
    # rows, cols: list of names
    def __init__(self, rows, cols):
        self.cols = cols
        self.rows = rows
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
    allpairs = [(-a|-b) for a, b in itertools.combinations(lst, 2)]
    return [any(lst)] + allpairs


def exactly_one_at_most(lst):
    allpairs = [(-a|-b) for a, b in itertools.combinations(lst, 2)]
    return any(lst), allpairs


def pastaPuzzle():
    """
    Logic grid puzzle: 'pasta' in CPpy
    Based on... to check originally, currently part of ZebraTutor
    Probably part of Jens Claes' master thesis, from a 'Byron...' booklet
    """
    # type1 = sauce
    # type2 = pasta
    # type3 = differences between values of type dollar
    # type4 = differences between values of type dollar
    # type5 = differences between values of type dollar
    dollar = ['4', '8', '12', '16']
    person = ['angie', 'damon', 'claudia', 'elisa']
    sauce = ['the_other_type1', 'arrabiata_sauce', 'marinara_sauce', 'puttanesca_sauce'] # type1
    pasta = ['capellini', 'farfalle', 'tagliolini', 'rotini']  # type2

    types = [dollar, person, sauce, pasta]
    n = len(types)
    m = len(types[0])
    assert all(len(types[i]) == m for i in range(n)), "all types should have equal length"

    chose = Relation(person, sauce)
    paid = Relation(person, dollar)
    ordered = Relation(person, pasta)
    sauce_dollar = Relation(sauce, dollar) # is_linked_with_1(sauce, dollar)
    sauce_pasta = Relation(sauce, pasta) # is_linked_with_2(sauce, pasta)
    dollar_pasta = Relation(dollar, pasta) # is_linked_with_3(dollar, pasta)
    rels = [chose, paid, ordered, sauce_dollar, sauce_pasta, dollar_pasta]

    # Bijectivity
    cnt = 0
    bij = []
    bv_bij = []

    for rel in rels:
        # bijection for all columns inside relation
        bv1 = BoolVar()
        bv2 = BoolVar()
        # for each relation
        for col_ids in rel.df:
            # one per column
            atleast, atmost = exactly_one_at_most(rel[:, col_ids])
            [bij.append(implies(bv1, clause)) for clause in atmost]
            bij.append(implies(bv2, atleast))
        bv_bij.append(bv1)
        bv_bij.append(bv2)

        # bijection for all rows inside relation
        bv3 = BoolVar()
        bv4 = BoolVar()
        for (_,row) in rel.df.iterrows():
            # one per row
            atleast, atmost = exactly_one_at_most(row)
            [bij.append(implies(bv3, clause)) for clause in atmost]
            bij.append(implies(bv4, atleast))
        bv_bij.append(bv3)
        bv_bij.append(bv4)

    # Transitivity
    trans = []
    bv_trans =  [BoolVar() for i in range(12)]

    for rel in rels:
        type1_1 = rel.rows
        type1_2= rel.cols
        for rel2 in rels:
            type2_1=rel2.rows
            type2_2=rel2.cols
            if type2_1:
                break
            for rel3 in rels:
                if not rel3 > rel 2:
                    break
                bv1 = BoolVar()
                bv2 = BoolVar()
                bv3 = BoolVar()
                #GENERATE ALLE SETS OF THREE "MATHCING RELATIONS"
                # e.g. p(T1,T2) p2(T2,T3), p3(T1,T3)
                # or p(T1,T2) p2(T2,T3), p3(T3,T1)
                # EASIER: GENERATE ALL SETS OF THREE DIFFERENT TYPES. 
                # Make procedure that gives you the right relation given two types (possibly "swapped")
                # map constructed when making relations. R
                for x in person:
                    for y in sauce:
                        for z in dollar:

                            t0 = to_cnf(implies(paid[x, z] & sauce_dollar[y, z], chose[x, y]))
                            [trans.append(implies(bv_trans[0], clause)) for clause in t0]

                            t1 = to_cnf(implies(~paid[x, z] & sauce_dollar[y, z], ~chose[x, y]))
                            [trans.append(implies(bv_trans[1], clause)) for clause in t1]

                            t2 = to_cnf(implies(paid[x, z] & ~sauce_dollar[y, z], ~chose[x, y]))
                            [trans.append(implies(bv_trans[2], clause)) for clause in t2]


    for x in person:
        for y in sauce:
            for z in dollar:
                t0 = to_cnf(implies(paid[x, z] & sauce_dollar[y, z], chose[x, y]))
                [trans.append(implies(bv_trans[0], clause)) for clause in t0]

                t1 = to_cnf(implies(~paid[x, z] & sauce_dollar[y, z], ~chose[x, y]))
                [trans.append(implies(bv_trans[1], clause)) for clause in t1]

                t2 = to_cnf(implies(paid[x, z] & ~sauce_dollar[y, z], ~chose[x, y]))
                [trans.append(implies(bv_trans[2], clause)) for clause in t2]

    for x in person:
        for y in sauce:
            for z in pasta:
                t3 = to_cnf(implies(ordered[x, z] & sauce_pasta[y, z], chose[x, y]))
                [trans.append(implies(bv_trans[3], clause)) for clause in t3]

                t4 = to_cnf(implies(~ordered[x, z] & sauce_pasta[y, z], ~chose[x, y]))
                [trans.append(implies(bv_trans[4], clause)) for clause in t4]

                t5 = to_cnf(implies(ordered[x, z] & ~sauce_pasta[y, z], ~chose[x, y]))
                [trans.append(implies(bv_trans[5], clause)) for clause in t5]

    for x in person:
        for y in dollar:
            for z in pasta:
                t6 = to_cnf(implies(ordered[x, z] & dollar_pasta[y, z], paid[x, y]))
                [trans.append(implies(bv_trans[6], clause)) for clause in t6]

                t7 = to_cnf(implies(~ordered[x, z] & dollar_pasta[y, z], ~paid[x, y]))
                [trans.append(implies(bv_trans[7], clause)) for clause in t7]

                t8 = to_cnf(implies(ordered[x, z] & ~dollar_pasta[y, z], ~paid[x, y]))
                [trans.append(implies(bv_trans[8], clause)) for clause in t8]


    for x in sauce:
        for y in dollar:
            for z in pasta:
                t9 = to_cnf(implies(sauce_pasta[x, z] & dollar_pasta[y, z], sauce_dollar[x, y]))
                [trans.append(implies(bv_trans[9], clause)) for clause in t9]

                t10 = to_cnf(implies(~sauce_pasta[x, z] & dollar_pasta[y, z], ~sauce_dollar[x, y]))
                [trans.append(implies(bv_trans[10], clause)) for clause in t10]

                t11 = to_cnf(implies(sauce_pasta[x, z] & ~dollar_pasta[y, z], ~sauce_dollar[x, y]))
                [trans.append(implies(bv_trans[11], clause)) for clause in t11]

    clues = []
    bv_clues = [BoolVar() for i in range(8)]

    # 0.The person who ordered capellini paid less than the person who chose arrabiata sauce
    # assumption_satisfied( 0  ) => ?a [person] b [type3] c [dollar] d [person] e [dollar]: ordered(a,capellini) & b>0 & chose(d,arrabiata_sauce) & paid(d,c) & e = c-b & paid(a,e).

    clue0 =  [ ordered[a, "capellini"] & chose[d, "arrabiata_sauce"] & paid[d, c] & paid[a, e]     for a in person for b in [-4, 4, -8, 8,  -12, 12] for c in dollar  for d in person for e in dollar if b > 0 and int(e) == int(c)-b]
    [clues.append(implies(bv_clues[0], cl)) for cl in to_cnf(any(clue0)) ]

    # 1. The person who chose arrabiata sauce ordered farfalle
    # assumption_satisfied( 0  ) => ?f [person]: chose(f,arrabiata_sauce) & ordered(f,farfalle).
    clue1 = any( [ chose[f,  "arrabiata_sauce"] & ordered[f, "farfalle"] for f in person])
    [clues.append(implies(bv_clues[1], cl)) for cl in to_cnf(clue1) ]

    # assumption_satisfied( 0  ) => !f [person]: chose(f,arrabiata_sauce) => ordered(f,farfalle).
    # was ok maar vertaling van iets anders:
    #c1a = to_cnf([implies(chose[p, "arrabiata_sauce"], ordered[p, "farfalle"]) for p in person])
    # [clues.append(implies(bv_clues[1], clause)) for clause in c1a]

    # 2. The person who ordered tagliolini paid less than the person who chose marinara sauce
    # assumption_satisfied( 0  ) => ?g [person] h [type4] i [dollar] j [person] k [dollar]: ordered(g,tagliolini) & h>0 & chose(j,marinara_sauce) & paid(j,i) & k = i-h & paid(g,k).
    c2a = []
    for g in person:
        # h > 0
        for h in [4, 8, 12]:
            for i in dollar:
                for j in person:
                    for k in dollar:
                        if int(k) == int(i) - h:
                            c2a.append(ordered[g, "taglioni"] & chose[j, "marinara_sauce"] & paid[str(j), str(i)] & paid[g, str(k)])
    [clues.append(implies(bv_clues[2], clause)) for clause in to_cnf(any(c2a))]

    #  3. The person who ordered tagliolini paid more than Angie
    # assumption_satisfied( 0  ) => ?l [person] m [type5] n [dollar] o [dollar]: ordered(l,tagliolini) & m>0 & paid(angie,n) & o = n+m & paid(l,o).
    c3a = []
    for p in person:
        for o in dollar:
            for n in dollar:
                for m in [4, 8, 12]:
                    if int(o) == int(n) + m:
                        c3a.append(ordered[p, "taglioni"] & paid["angie", str(n)] & paid[p, str(o)])

    [clues.append(implies(bv_clues[3], clause)) for clause in to_cnf(exactly_one(c3a))]

    #  4. The person who ordered rotini is either the person who paid $8 more than Damon or the person who paid $8 less than Damon
    # assumption_satisfied( 0  ) => ?
    # p [person]: ordered(p,rotini) & 
    #           ((?q [person] r [dollar] s [dollar]: paid(damon,r) & s = r+8 & paid(q,s) & q = p) 
    #           | (?t [person] u [dollar] v [dollar]: paid(damon,u) & v = u-8 & paid(t,v) & t = p)).

    #list with: for every person: two options
    c4a = []
    for p in person:
        formule1 = any(
            [paid["damon", r] & paid(q,s) for q in person for r in dollar for s in dollar if int(s) == int(r) + 8 and q == p]
        )
        formule2 = any(
            [paid["damon", r] & paid(q,s) for q in person for r in dollar for s in dollar if int(s) == int(r) - 8 and q == p]
        )
        groteformule = formule1 | formule2
        c4a.append(ordered[p, "rotini"] & groteformule)
    for clause in to_cnf(any(c4a)):
        clues.append(implies(bv_clues[4], clause))


    # 5. Claudia did not choose puttanesca sauce
    # assumption_satisfied( 0  ) => ~ chose(claudia,puttanesca_sauce).
    clues.append(implies(bv_clues[5],  ~chose["claudia", "puttanesca_sauce"]))

    #  6. The person who ordered capellini is either Damon or Claudia
    # assumption_satisfied( 0  ) => ?w [person]: ordered(w,capellini) & (damon = w | claudia = w).
    c6a = [ordered[p, 'capellini'] & ( (p == 'claudia') | (p == 'damon')) for p in person]
    [clues.append(implies(bv_clues[6], clause)) for clause in to_cnf(any(c6a))]

    # 7. The person who chose arrabiata sauce is either Angie or Elisa => XOR
    # assumption_satisfied( 0  ) => ?x [person]: chose(x,arrabiata_sauce) & (angie = x | elisa = x).
    c7a = [chose[p, 'arrabiata_sauce'] &( (p == 'angie') | (p == 'elisa'))  for p in person]
    [clues.append(implies(bv_clues[7], clause)) for clause in to_cnf(any(c7a))]

    clueTexts = [
        "The person who ordered capellini paid less than the person who chose arrabiata sauce",
        "The person who chose arrabiata sauce ordered farfalle",
        "The person who ordered tagliolini paid less than the person who chose marinara sauce",
        "The person who ordered tagliolini paid more than Angie",
        "The person who ordered rotini is either the person who paid $8 more than Damon or the person who paid $8 less than Damon",
        "Claudia did not choose puttanesca sauce",
        "The person who ordered capellini is either Damon or Claudia",
        "The person who chose arrabiata sauce is either Angie or Elisa"
    ]

    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))

    hard_clauses = [c for c in clues_cnf + bij_cnf + trans_cnf]
    soft_clauses = []
    soft_clauses += [[bv1.name + 1] for bv1 in bv_clues]
    soft_clauses += [[bv1.name + 1]  for bv1 in bv_bij]
    soft_clauses += [[bv1.name + 1]  for bv1 in bv_trans]

    weights = {}
    weights.update({bv.name + 1: 100 for bv in bv_clues})
    weights.update({bv.name + 1: 60 for bv in bv_trans})
    weights.update({bv.name + 1: 60 for bv in bv_bij})

    explainable_facts = set()
    bvRels = {}
    for rel, relStr in zip(rels, ["chose", "paid", "ordered", "sauce_dollar", "sauce_pasta", "dollar_pasta"]):
        rowNames = list(rel.df.index)
        columnNames = list(rel.df.columns)

        # production of explanations json file
        for r in rowNames:
            for c in columnNames:
                bvRels[rel.df.at[r, c].name + 1] = {"pred" : relStr.lower(), "subject" : r.lower(), "object": c.lower()}

        # facts to explain
        for item in rel.df.values:
            explainable_facts |= set(i.name+1 for i in item)

    matching_table = {
        'bvRel': bvRels,
        'Transitivity constraint': [bv.name + 1 for bv in bv_trans],
        'Bijectivity': [bv.name + 1 for bv in bv_bij],
        'clues' : {
            bv.name + 1: clueTexts[i] for i, bv in enumerate(bv_clues)
        }
    }

    return hard_clauses, soft_clauses, weights, explainable_facts, matching_table


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
    bv_bij = []

    for rel in [is_old, lives_in, native, age_city, age_birth, city_birth]:
        # for each relation
        for col_ids in rel.df:
            bv1 = BoolVar()
            bv2 = BoolVar()
            # one per column
            atleast, atmost = exactly_one_at_most(rel[:, col_ids])
            [bij.append(bv1 == clause) for clause in atmost]
            bij.append(bv2 == atleast)
            bv_bij.append(bv1)
            bv_bij.append(bv2)

        for (_,row) in rel.df.iterrows():
            bv3 = BoolVar()
            bv4 = BoolVar()
            # one per row
            atleast, atmost = exactly_one_at_most(row)
            [bij.append(bv3 == clause) for clause in atmost]
            bij.append(bv4 == atleast)
            bv_bij.append(bv3)
            bv_bij.append(bv4)

    # # Transitivity
    trans = []
    bv_trans = BoolVar(12)

    # Transitivity
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

    # # The person who lives in Tehama is a native of either Kansas or Oregon
    # c1a = to_cnf([implies(lives_in[p, 'Tehama'], native[p, 'Kansas'] | native[p, 'Oregon']) for p in person])

    # [clues.append(implies(bv_clues[1], clause)) for clause in c1a]

    # # The Washington native is 1 year older than Ernesto
    # c2a = to_cnf([implies(age_birth[a, 'Washington'], is_old['Ernesto', str(int(a)-1)]) for a in age])
    # [clues.append(implies(bv_clues[2], clause)) for clause in c2a]

    # # Roxanne is 2 years younger than the Kansas native
    # c3a = to_cnf([implies(is_old['Roxanne', a], age_birth[str(int(a)+2), 'Kansas']) for a in age])
    # [clues.append(implies(bv_clues[3], clause)) for clause in c3a]

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


    # clues = []
    # bv_clues = [BoolVar() for i in range(10)]
    

    # # The person who lives in Tehama is a native of either Kansas or Oregon
    c1a = [(~lives_in[p, 'Tehama'] | native[p, 'Kansas'] | native[p, 'Oregon']) for p in person]

    # # The Washington native is 1 year older than Ernesto
    c2a = [(~age_birth[a, 'Washington']| is_old['Ernesto', str(int(a)-1)]) for a in age]

    # # Roxanne is 2 years younger than the Kansas native
    c3a = [(~is_old['Roxanne', a]| age_birth[str(int(a)+2), 'Kansas']) for a in age]

    # # The person who lives in Zearing isn't a native of Alaska
    c4a = [(~lives_in[p, 'Zearing'] | ~native[p, 'Alaska']) for p in person]

    # # The person who is 111 years old doesn't live in Plymouth
    c5a = [(~is_old[p, '111'] | ~lives_in[p, 'Plymouth']) for p in person]

    # # The Oregon native is either Zachary or the person who lives in Tehama
    c6a = [(~native[p, 'Oregon'] | (p == 'Zachary') | lives_in[p, 'Tehama']) for p in person]

    # # The person who lives in Shaver Lake is 1 year younger than Roxanne
    c7a = [(~age_city[a, 'Shaver Lake'] | is_old['Roxanne', str(int(a)+1)]) for a in age]

    # # The centenarian who lives in Plymouth isn't a native of Alaska
    c8a = [(~lives_in[p, 'Plymouth'] | ~native[p, 'Alaska']) for p in person]

    # # Of the person who lives in Tehama and Mattie, one is a native of Alaska and the other is from Kansas
    c9a = [(~lives_in[p, 'Tehama'] | ((p != 'Mattie') &
                          ((native['Mattie', 'Alaska'] & native[p, 'Kansas']) |
                           (native[p, 'Alaska'] & native['Mattie', 'Kansas'])))) for p in person]

    [clues.append((bv_clues[1] == clause)) for clause in c1a]
    [clues.append((bv_clues[2] == clause)) for clause in c2a]
    [clues.append((bv_clues[3] == clause)) for clause in c3a]
    [clues.append((bv_clues[4] == clause)) for clause in c4a]
    [clues.append((bv_clues[5] == clause)) for clause in c5a]
    [clues.append((bv_clues[6] == clause)) for clause in c6a]
    [clues.append((bv_clues[7] == clause)) for clause in c7a]
    [clues.append((bv_clues[8] == clause)) for clause in c8a]
    [clues.append((bv_clues[9] == clause)) for clause in c9a]

    print(bv_clues)

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
    print(soft_clauses)

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
    # bv_bij = [BoolVar() for i in range(60)]

    bv_bij = []

    for rel in [is_old, lives_in, native, age_city, age_birth, city_birth]:
        # for each relation
        for col_ids in rel.df:
            bv1 = BoolVar()
            bv2 = BoolVar()
            # one per column
            atleast, atmost = exactly_one_at_most(rel[:, col_ids])
            [bij.append(implies(bv1, clause)) for clause in atmost]
            bij.append(implies(bv2, atleast))
            bv_bij.append(bv1)
            bv_bij.append(bv2)

        for (_,row) in rel.df.iterrows():
            bv3 = BoolVar()
            bv4 = BoolVar()
            # one per row
            atleast, atmost = exactly_one_at_most(row)
            [bij.append(implies(bv3, clause)) for clause in atmost]
            bij.append(implies(bv4, atleast))
            bv_bij.append(bv3)
            bv_bij.append(bv4)

    # Transitivity
    trans = []
    bv_trans =  [BoolVar() for i in range(12)]
    for x in person:
        for z in birthplace:
            for y in age:
                # ! x y z:  from(x, z) & is_linked_with_1(y, z) => is_old(x, y).
                t0 = to_cnf(implies( native[x, z] & age_birth[y, z], is_old[x, y]))
                [trans.append(implies(bv_trans[0], clause)) for clause in t0]

                 # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
                t1 = to_cnf(implies( ~native[x, z] & age_birth[y, z], ~is_old[x, y]))
                [trans.append(implies(bv_trans[1], clause)) for clause in t1]

                 # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
                t2 = to_cnf(implies( native[x, z] & ~age_birth[y, z], ~is_old[x, y]))
                [trans.append(implies(bv_trans[2], clause)) for clause in t2]

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

    # match clue in cnf to textual representation
    clueTexts = [
        "Mattie is 113 years old",
        "The person who lives in Tehama is a native of either Kansas or Oregon",
        "The Washington native is 1 year older than Ernesto",
        "Roxanne is 2 years younger than the Kansas native",
        "The person who lives in Zearing isn't a native of Alaska",
        "The person who is 111 years old doesn't live in Plymouth",
        "The Oregon native is either Zachary or the person who lives in Tehama",
        "The person who lives in Shaver Lake is 1 year younger than Roxanne",
        "The centenarian who lives in Plymouth isn't a native of Alaska",
        "Of the person who lives in Tehama and Mattie, one is a native of Alaska and the other is from Kansas"
    ]

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

    explainable_facts = set()
    bvRels = {}
    for rel, relStr in zip(rels, ["is_old", "lives_in", "native", "age_city", "age_birth", "city_birth"]):
        rowNames = list(rel.df.index)
        columnNames = list(rel.df.columns)
        for r in rowNames:
            for c in columnNames:
                print(relStr, "row=",r, "col=", c, rel.df.at[r, c])
                bvRels[rel.df.at[r, c].name + 1] = {"pred" : relStr.lower(), "subject" : r.lower(), "object": c.lower()}
        for item in rel.df.values:
            explainable_facts |= set(i.name+1 for i in item)


    matching_table = {
        'bvRel': bvRels,
        'Transitivity constraint': [bv.name + 1 for bv in bv_trans],
        'Bijectivity': [bv.name + 1 for bv in bv_bij],
        'clues' : {
            bv.name + 1: clueTexts[i] for i, bv in enumerate(bv_clues)
        }
    }

    return hard_clauses, soft_clauses, weights, explainable_facts, matching_table


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
    # print("Mayo=", mayo.name+1)
    # print("ketchup=", ketchup.name+1)
    # print("andalouse=", andalouse.name+1)

    c0 = mayo
    c1 = ~mayo | ~andalouse | ketchup
    c2 = ~mayo | andalouse | ketchup
    c3 = ~ketchup | ~andalouse

    constraints = [c0, c1, c2, c3]

    cnf = cnf_to_pysat(constraints)
    return cnf


def simpleProblemReify():
    (mayo, ketchup, andalouse) = BoolVar(3)
    b = BoolVar(4)
    # print("Mayo=", mayo.name+1)
    # print("ketchup=", ketchup.name+1)
    # print("andalouse=", andalouse.name+1)

    c0 = (b[0] == mayo)
    c1 = (b[1] == (~mayo | ~andalouse | ketchup))
    c2 = (b[2] == (~mayo | andalouse | ketchup))
    c3 = (b[3] == (~ketchup | ~andalouse))

    constraints = [c0, c1, c2, c3]

    c = to_cnf(constraints)
    cnf = cnf_to_pysat(c)
    user_vars = [mayo.name+1, ketchup.name+1, andalouse.name+1]
    return cnf, [bi.name + 1 for bi in b], user_vars


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
    offset = samurai.name+1

    print("Mayo=", mayo.name+1)
    print("ketchup=", ketchup.name+1)
    print("andalouse=", andalouse.name+1)
    print("curry=", curry.name+1)
    print("samurai=", samurai.name+1)

    print(f"{offset + 1}. Nora = {mayo.name+1} | {ketchup.name+1}", )
    print(f"{offset + 2}. Leander = ~{samurai.name+1} | {mayo.name+1}")
    print(f"{offset + 3}. Benjamin = ~{andalouse.name+1} | ~{curry.name+1} | ~{samurai.name+1}")
    print(f"{offset + 4}. Behrouz = {ketchup.name+1} | {curry.name+1} | {andalouse.name+1}")
    print(f"{offset + 5}. Guy = ~{ketchup.name+1} | {curry.name+1} | {andalouse.name+1}")
    print(f"{offset + 6}. Daan = ~{ketchup.name+1} | ~{curry.name+1} | {andalouse.name+1}")
    print(f"{offset + 7}. Celine = ~{samurai.name+1}")
    print(f"{offset + 8}. Anton = {mayo.name+1} | ~{curry.name+1} | ~{andalouse.name+1}")
    print(f"{offset + 9}. Danny = ~{mayo.name+1} | {ketchup.name+1} | {andalouse.name+1} | {samurai.name+1}")
    print(f"{offset + 10}. Luc = ~{mayo.name+1} | {samurai.name+1}")

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

