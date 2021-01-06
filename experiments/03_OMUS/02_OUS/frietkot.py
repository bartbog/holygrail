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


def buildBijectivity(rels):
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
    return bij, bv_bij


def p19():
    pass


def p18():
    type1 = ["the_other_type1", "glendale", "olema", "evansdale", "lakota"]
    person = ["the_other_person", "al_allen", "kelly_kirby", "bev_baird", "ed_ewing"]
    candidate = ["the_other_candidate", "academic", "teacher", "writer", "doctor"]
    vote = ["8500", "9000", "9500", "10000", "10500"] # isa int
    type2 = [-500, 500, -1000, 1000, -1500, 1500, -2000, 2000] # differences between values of type vote

    types = [type1, person, candidate, vote]
    n = len(types)
    m = len(types[0])
    assert all(len(types[i]) == m for i in range(n)), "all types should have equal length"

    person_type1 = Relation(person, type1) # from(person, type1)
    acts_as = Relation(person, candidate) # acts_as(person, candidate)
    finished_with = Relation(person, vote) # finished_with(person, vote)
    received = Relation(candidate, vote) # received(candidate, vote)
    is_linked_with_1 = Relation(type1, candidate) # is_linked_with_1(type1, candidate)
    is_linked_with_2 = Relation(type1, vote) # is_linked_with_2(type1, vote)

    rels = [person_type1, acts_as, finished_with, received, is_linked_with_1, is_linked_with_2]

    # Bijectivity
    bij, bv_bij = buildBijectivity(rels)

    # Transitivity
    trans = []
    bv_trans =  [BoolVar() for i in range(12)]
    for x in person:
        for y in type1:
            for z in candidate:
                t0 = to_cnf(implies(acts_as[x, z] & is_linked_with_1[y, z], person_type1[x, y]))
                [trans.append(implies(bv_trans[0], clause)) for clause in t0]

                t1 = to_cnf(implies(~acts_as[x, z] & is_linked_with_1[y, z], ~person_type1[x, y]))
                [trans.append(implies(bv_trans[1], clause)) for clause in t1]

                t2 = to_cnf(implies(acts_as[x, z] & ~is_linked_with_1[y, z], ~person_type1[x, y]))
                [trans.append(implies(bv_trans[2], clause)) for clause in t2]

    for x in person:
        for y in type1:
            for z in vote:
                t3 = to_cnf(implies(finished_with[x, z] & is_linked_with_2[y, z], person_type1[x, y]))
                [trans.append(implies(bv_trans[3], clause)) for clause in t3]

                t4 = to_cnf(implies(~finished_with[x, z] & is_linked_with_2[y, z], ~person_type1[x, y]))
                [trans.append(implies(bv_trans[4], clause)) for clause in t4]

                t5 = to_cnf(implies(finished_with[x, z] & ~is_linked_with_2[y, z], ~person_type1[x, y]))
                [trans.append(implies(bv_trans[5], clause)) for clause in t5]

    for x in person:
        for y in candidate:
            for z in vote:
                t6 = to_cnf(implies(finished_with[x, z] & received[y, z], acts_as[x, y]))
                [trans.append(implies(bv_trans[6], clause)) for clause in t6]

                t7 = to_cnf(implies(~finished_with[x, z] & received[y, z], ~acts_as[x, y]))
                [trans.append(implies(bv_trans[7], clause)) for clause in t7]

                t8 = to_cnf(implies(finished_with[x, z] & ~received[y, z], ~acts_as[x, y]))
                [trans.append(implies(bv_trans[8], clause)) for clause in t8]

    for x in candidate:
        for y in vote:
            for z in type1:
                t9 = to_cnf(implies(is_linked_with_1[z, x] & is_linked_with_2[z, y], received[x, y]))
                [trans.append(implies(bv_trans[9], clause)) for clause in t9]

                t10 = to_cnf(implies(~is_linked_with_1[z, x] & is_linked_with_2[z, y], ~received[x, y]))
                [trans.append(implies(bv_trans[10], clause)) for clause in t10]

                t11 = to_cnf(implies(is_linked_with_1[z, x] & ~is_linked_with_2[z, y], ~received[x, y]))
                [trans.append(implies(bv_trans[11], clause)) for clause in t11]

    clues = []
    bv_clues = [BoolVar() for i in range(12)]

    # 0. Al allen is from glendale
    # assumption_satisfied( 0  ) => person_type1(al_allen,glendale).
    clues.append(implies(bv_clues[0], person_type1["al_allen","glendale"]))

    # 1. Kelly Kirby finished 1000 votes ahead of the person who acts as the academic
    # assumption_satisfied( 0  ) => ?a [vote] b [person] c [vote]: acts_as(b,academic) & finished_with(b,a) & c = a+1000 & finished_with(kelly_kirby,c).
    c1a = []
    for a in vote:
        for b in person:
            for c in vote:
                if int(c) == int(a) + 1000:
                    c1a.append(acts_as[b,"academic"] & finished_with[b,a] & finished_with["kelly_kirby",c])

    for cl in to_cnf(any(c1a)):
        clues.append(implies(bv_clues[1], cl))
    # 2.The academic received 500 votes less than the teacher
    # assumption_satisfied( 0  ) => ?d [vote] e [vote]: received(teacher,d) & e = d-500 & received(academic,e).
    c2a = []
    for d in vote:
        for e in vote:
            if int(e) == int(d) - 500:
                c2a.append(received["teacher",d] & received["academic",e])

    for cl in to_cnf(any(c2a)):
        clues.append(implies(bv_clues[2], cl))

    # 3. The candidate who received 10500 votes isn't the writer
    # assumption_satisfied( 0  ) => ?f [candidate]: received(f,10500) & ~ (writer = f).
    c3a = []
    for f in candidate:
        c3a.append(received[f, "10500"] & ~ ("writer" == f) )

    for cl in to_cnf(any(c3a)):
        clues.append(implies(bv_clues[3], cl))
    # 4. Kelly Kirby isn't from Olema
    # assumption_satisfied( 0  ) => ~ person_type1(kelly_kirby,olema).
    clues.append(implies(bv_clues[4],  ~ person_type1["kelly_kirby","olema"]))

    # 5. The glendale native finished somewhat ahead of the Olema native
    # assumption_satisfied( 0  ) => ?g [person] h [type2] i [vote] j [person] k [vote]: h>0 & finished_with(j,i) & person_type1(j,olema) & k = i+h & finished_with(g,k) & person_type1(g,glendale).
    c5a = []
    for g in person:
        for h in type2:
            for i in vote:
                for j in person:
                    for k in vote:
                        if int(h) > 0 and int(k) == int(i) + int(h):
                            c5a.append(finished_with[j,i] & person_type1[j,"olema"] & finished_with[g,k] & person_type1[g,"glendale"])

    for cl in to_cnf(any(c5a)):
        clues.append(implies(bv_clues[5], cl))
    # 6. Bev Baird ended up with 8500 votes
    # assumption_satisfied( 0  ) => finished_with(bev_baird,8500).
    clues.append(implies(bv_clues[6],  finished_with["bev_baird","8500"]))

    # 7. Ed Ewing finished 500 votes ahead of the Evansdale native
    # assumption_satisfied( 0  ) => ?l [vote] m [person] n [vote]: finished_with(m,l) & person_type1(m,evansdale) & n = l+500 & finished_with(ed_ewing,n).
    c7a = []
    for l in vote:
        for m in person:
            for n in vote:
                if int(n) == int(l) + 500:
                    c7a.append(finished_with[m,l] & person_type1[m,"evansdale"] & finished_with["ed_ewing",n])

    for cl in to_cnf(any(c7a)):
        clues.append(implies(bv_clues[7], cl))
    # 8. The man who received 9500 votes isn't the doctor
    # assumption_satisfied( 0  ) =>  ?o [candidate]: received(o,9500) & ~ (doctor = o).

    c8a = []
    for o in candidate:
        c8a.append(received[o,9500] & ~("doctor" == o))

    for cl in to_cnf(any(c8a)):
        clues.append(implies(bv_clues[8], cl))
    # 9. Of the person acting as academic and Al Allen, one ended up with 10000 votes and the other ended up with 8500 votes
    # assumption_satisfied( 0  ) => ? p [person]: acts_as(p,academic) & ~ (p = al_allen) & (finished_with(p,10000) & finished_with(al_allen,8500) | finished_with(al_allen,10000) & finished_with(p,8500)).
    c9a = []
    for p in person:
        if not (p == "al_allen"):
            c9a.append(acts_as[p,"academic"] & ((finished_with[p,"10000"] & finished_with["al_allen","8500"]) | (finished_with["al_allen","10000"] & finished_with[p,"8500"])))

    for cl in to_cnf(any(c9a)):
        clues.append(implies(bv_clues[9], cl))
    # 10. The politician who finished with 10500 votes isn't from Lakota
    # assumption_satisfied( 0  ) => ?q [person]: finished_with(q,10500) & ~ person_type1(q,lakota).
    c10a = []
    for q in person:
        c10a.append(finished_with[q,"10500"] & ~ person_type1[q,"lakota"])

    for cl in to_cnf(any(c10a)):
        clues.append(implies(bv_clues[10], cl))
    # 11. The person acting as doctor was either the politician who finished with 10000 votes or Kelly Kirby
    # assumption_satisfied( 0  ) => ?r [person]: acts_as(r,doctor) & ((?s [person]: finished_with(s,10000) & s = r) | kelly_kirby = r).
    c11a = []
    for r in person:
        subformula = any(
            finished_with[s,"10000"] & (s == r)
            for s in person
        )
        c11a.append(acts_as[r,"doctor"] & (subformula | "kelly_kirby" == r))

    for cl in to_cnf(any(c11a)):
        clues.append(implies(bv_clues[11], cl))

    clueTexts =[
        "Al allen is from glendale",
        "Kelly Kirby finished 1000 votes ahead of the person who acts as the academic",
        "The academic received 500 votes less than the teacher",
        "The candidate who received 10500 votes isn't the writer",
        "Kelly Kirby isn't from Olema",
        "The glendale native finished somewhat ahead of the Olema native",
        "Bev Baird ended up with 8500 votes",
        "Ed Ewing finished 500 votes ahead of the Evansdale native",
        "The man who received 9500 votes isn't the doctor",
        "Of the person acting as academic and Al Allen, one ended up with 10000 votes and the other ended up with 8500 votes",
        "The politician who finished with 10500 votes isn't from Lakota",
        "The person acting as doctor was either the politician who finished with 10000 votes or Kelly Kirby"
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
    for rel, relStr in zip(rels, ["person_type1", "acts_as", "finished_with", "received", "is_linked_with_1", "is_linked_with_2"]):
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

def p16():
    type1 = ["the_other_type1", "rings", "mobile_phones", "flashlights", "rubber_balls"]
    juggler = ["the_other_juggler", "howard", "otis", "gerald", "floyd"]
    type2 = ["the_other_type2", "quasqueton", "kingsburg", "carbon", "nice"]
    spot = ["1", "2", "3", "4", "5"]

    used = Relation(juggler, type1)
    juggler_type2 = Relation(juggler, type2) #from
    went = Relation(juggler, spot) 
    type1_type2 = Relation(type1, type2) #is_linked_with_1
    type1_spot = Relation(type1, spot) #is_linked_with_2
    type2_spot = Relation(type2, spot) #is_linked_with_3

    types = [type1, juggler, type2, spot]
    n = len(types)
    m = len(types[0])
    assert all(len(types[i]) == m for i in range(n)), "all types should have equal length"

    rels = [used, juggler_type2, went, type1_type2, type1_spot, type2_spot]

    # Bijectivity
    bij, bv_bij = buildBijectivity(rels)

    # Transitivity
    trans = []
    bv_trans =  [BoolVar() for i in range(12)]
    for x in juggler:
        for y in type1:
            for z in type2:
                t0 = to_cnf(implies(juggler_type2[x, z] & type1_type2[y, z], used[x, y]))
                [trans.append(implies(bv_trans[0], clause)) for clause in t0]

                t1 = to_cnf(implies(~juggler_type2[x, z] & type1_type2[y, z], ~used[x, y]))
                [trans.append(implies(bv_trans[1], clause)) for clause in t1]

                t2 = to_cnf(implies(juggler_type2[x, z] & ~type1_type2[y, z], ~used[x, y]))
                [trans.append(implies(bv_trans[2], clause)) for clause in t2]

    for x in juggler:
        for y in type1:
            for z in spot:
                t3 = to_cnf(implies(went[x, z] & type1_spot[y, z], used[x, y]))
                [trans.append(implies(bv_trans[3], clause)) for clause in t3]

                t4 = to_cnf(implies(~went[x, z] & type1_spot[y, z], ~used[x, y]))
                [trans.append(implies(bv_trans[4], clause)) for clause in t4]

                t5 = to_cnf(implies(went[x, z] & ~type1_spot[y, z], ~used[x, y]))
                [trans.append(implies(bv_trans[5], clause)) for clause in t5]

    for x in juggler:
        for y in type2:
            for z in spot:
                t6 = to_cnf(implies(went[x, z] & type2_spot[y, z], juggler_type2[x, y]))
                [trans.append(implies(bv_trans[6], clause)) for clause in t6]

                t7 = to_cnf(implies(~went[x, z] & type2_spot[y, z], ~juggler_type2[x, y]))
                [trans.append(implies(bv_trans[7], clause)) for clause in t7]

                t8 = to_cnf(implies(went[x, z] & ~type2_spot[y, z], ~juggler_type2[x, y]))
                [trans.append(implies(bv_trans[8], clause)) for clause in t8]

    for x in type1:
        for y in type2:
            for z in spot:
                t9 = to_cnf(implies(type1_spot[x, z] & type2_spot[y, z], type1_type2[x, y]))
                [trans.append(implies(bv_trans[9], clause)) for clause in t9]

                t10 = to_cnf(implies(~type1_spot[x, z] & type2_spot[y, z], ~type1_type2[x, y]))
                [trans.append(implies(bv_trans[10], clause)) for clause in t10]

                t11 = to_cnf(implies(type1_spot[x, z] & ~type2_spot[y, z], ~type1_type2[x, y]))
                [trans.append(implies(bv_trans[11], clause)) for clause in t11]

    clues = []
    bv_clues = [BoolVar() for i in range(11)]
    # 0. The juggler who went fourth was either the performer from Quasqueton or the juggler who used rings
    # assumption_satisfied( 0  ) => ?a [juggler]: went(a,4) & ((?b [juggler]: from(b,quasqueton) & b = a) | (?c [juggler]: used(c,rings) & c = a)).
    c0a = []
    for a in juggler:
        formule1 = any(
            juggler_type2[b,"quasqueton"]
            for b in juggler if b == a
        )
        formule2 = any(
            used[c, "rings"]
            for c in juggler if c == a
        )
        c0a.append(went[a, "4"] & (formule1 | formule2))

    for cl in to_cnf(any(c0a)):
        clues.append(implies(bv_clues[0], cl))
    # 1. The juggler who used flashlights performed one spot after the person who used mobile phones
    # assumption_satisfied( 0  ) => ?d [juggler] e [spot] f [juggler] g [spot]: used(d,flashlights) & used(f,mobile_phones) & went(f,e) & g = e+1 & went(d,g).
    c1a = []
    for d in juggler:
        for e in spot:
            for f in juggler:
                for g in spot:
                    if int(g) == int(e) + 1:
                        c1a.append(used[d,"flashlights"] & used[f,"mobile_phones"] & went[f,e] & went[d,g])

    for cl in to_cnf(any(c1a)):
        clues.append(implies(bv_clues[1], cl))
    # 2. The performer from Kingsburg performed one spot before Howard
    # assumption_satisfied( 0  ) => ?h [juggler] i [spot] j [spot]: from(h,kingsburg) & went(howard,i) & j = i-1 & went(h,j).
    c2a = []
    for h in juggler:
        for i in spot:
            for j in spot:
                if int(j) == int(i) - 1:
                    c2a.append(juggler_type2[h,"kingsburg"] & went["howard",i] & went[h,j])

    for cl in to_cnf(any(c2a)):
        clues.append(implies(bv_clues[2], cl))
    # 3. Otis wasn't from Carbon
    # assumption_satisfied( 0  ) => ~ from(otis,carbon).
    clues.append(implies(bv_clues[3], juggler_type2["otis","carbon"]))

    # 4. Of the performer who went second and the juggler who used rings, one was from Carbon and the other is Howard
    # assumption_satisfied( 0  ) => ?k [juggler] l [juggler]: went(k,2) & used(l,rings) & ~ (k = l) & (from(k,carbon) & howard = l | from(l,carbon) & howard = k).
    c4a = []
    for k in juggler:
        for l in juggler:
            if not (k == l):
                c4a.append(went[k,"2"] & used[l,"rings"] & (juggler_type2[k,"carbon"] & "howard" == l | juggler_type2[l,"carbon"] & "howard" == k))

    for cl in to_cnf(any(c4a)):
        clues.append(implies(bv_clues[4], cl))
    # 5. The performer who went third, Gerald and the person from Kingsburg are three different people
    # assumption_satisfied( 0  ) => ?m [juggler] n [juggler]: ~ (m = gerald) & ~ (m = n) & ~ (gerald = n) & went(m,3) & from(n,kingsburg).
    c5a = []
    for m in juggler:
        for n in juggler:
            if not (m == "gerald") and not(m == n) and not("gerald" == n):
                c5a.append(went[m,"3"] & juggler_type2[n,"kingsburg"])

    for cl in to_cnf(any(c5a)):
        clues.append(implies(bv_clues[5], cl))
    # 6. Floyd was either the juggler who went second or the juggler from Quasqueton
    # assumption_satisfied( 0  ) => (?o [juggler]: went(o,2) & o = floyd) | (?p [juggler]: from(p,quasqueton) & p = floyd).
    c6a = []
    for o in juggler:
        c6a.append(went[o,"2"] & (o == "floyd"))

    c6b = []
    for p in juggler:
        c6b.append(juggler_type2[p,"quasqueton"] & (p == "floyd"))

    for cl in to_cnf(any(c6a) | c6b):
        clues.append(implies(bv_clues[6], cl))

    # 7. The person who went third used rings
    # assumption_satisfied( 0  ) => ?q [juggler]: went(q,3) & used(q,rings).
    c7a = []
    for q in juggler:
        c7a.append(went[q,"3"] & used[q,"rings"])

    for cl in to_cnf(any(c7a)):
        clues.append(implies(bv_clues[7], cl))

    # 8. The juggler who went second wasn't from Nice
    # assumption_satisfied( 0  ) =>  ?r [juggler]: went(r,2) & ~ from(r,nice).
    c8a = []
    for r in juggler:
        c8a.append(went[r, "2"] & ~juggler_type2[r, "nice"])

    for cl in to_cnf(any(c8a)):
        clues.append(implies(bv_clues[8], cl))

    # 9. Floyd juggles rubber balls
    # assumption_satisfied( 0  ) => used(floyd,rubber_balls).
    clues.append(implies(bv_clues[9], used["floyd","rubber_balls"]))


    clueTexts =[
        "The juggler who went fourth was either the performer from Quasqueton or the juggler who used rings",
        "The juggler who used flashlights performed one spot after the person who used mobile phones",
        "The performer from Kingsburg performed one spot before Howard",
        "Otis wasn't from Carbon",
        "Of the performer who went second and the juggler who used rings, one was from Carbon and the other is Howard",
        "The performer who went third, Gerald and the person from Kingsburg are three different people",
        "Floyd was either the juggler who went second or the juggler from Quasqueton",
        "The person who went third used rings",
        "The juggler who went second wasn't from Nice",
        "Floyd juggles rubber balls"
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
    for rel, relStr in zip(rels, ["used", "juggler_type2", "went", "type1_type2", "type1_spot", "type2_spot"]):
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

def p13():
    dollar = ["750", "1000", "1250", "1500", "1750"]
    piece = ["the_other_piece", "valencia", "waldarama", "tombawomba", "sniffletoe"]
    person = ["kelly", "isabel", "lucas", "nicole", "herman"]
    city = ["the_other_type2", "vancouver", "ypsilanti", "mexico_city", "st_moritz"]
    diffdollar = [-250, 250, -500, 500, -750, 750, -1000, 1000]


    types = [dollar, piece, person, city]
    n = len(types)
    m = len(types[0])
    assert all(len(types[i]) == m for i in range(n)), "all types should have equal length"

    #type1 = person
    #type2 = city
    #type3 = diffdollar

    # from(piece, type1) = piece_person  = Relation(piece, person)
    # is_linked_with_1(dollar, type1)     dollar_person = Relation(dollar, person)
    # is_linked_with_2(dollar, type2)    dollar_city = Relation(dollar, city)
    # is_linked_with_3(type1, type2)    person_city = Relation(person, city)

    cost = Relation(piece, dollar)
    go_to = Relation(piece, city)
    piece_person = Relation(piece, person)
    dollar_person = Relation(dollar, person)
    dollar_city = Relation(dollar, city)
    person_city = Relation(person, city)
    rels = [cost, go_to, piece_person, dollar_person, dollar_city, person_city]

    # Bijectivity
    bij, bv_bij = buildBijectivity(rels)

    # Transitivity
    trans = []
    bv_trans =  [BoolVar() for i in range(12)]

    for x in piece:
        for y in dollar:
            for z in city:
                t0 = to_cnf(implies(go_to[x, z] & dollar_city[y, z], cost[x, y]))
                [trans.append(implies(bv_trans[0], clause)) for clause in t0]

                t1 = to_cnf(implies(~go_to[x, z] & dollar_city[y, z], ~cost[x, y]))
                [trans.append(implies(bv_trans[1], clause)) for clause in t1]

                t2 = to_cnf(implies(go_to[x, z] & ~dollar_city[y, z], ~cost[x, y]))
                [trans.append(implies(bv_trans[2], clause)) for clause in t2]

    for x in piece:
        for y in dollar:
            for z in person:
                t3 = to_cnf(implies(piece_person[x, z] & dollar_person[y, z], cost[x, y]))
                [trans.append(implies(bv_trans[3], clause)) for clause in t3]

                t4 = to_cnf(implies(~piece_person[x, z] & dollar_person[y, z], ~cost[x, y]))
                [trans.append(implies(bv_trans[4], clause)) for clause in t4]

                t5 = to_cnf(implies(piece_person[x, z] & ~dollar_person[y, z], ~cost[x, y]))
                [trans.append(implies(bv_trans[5], clause)) for clause in t5]

    for x in piece:
        for y in person:
            for z in city:
                t6 = to_cnf(implies(go_to[x, z] & person_city[y, z], piece_person[x, y]))
                [trans.append(implies(bv_trans[6], clause)) for clause in t6]

                t7 = to_cnf(implies(~go_to[x, z] & person_city[y, z], ~piece_person[x, y]))
                [trans.append(implies(bv_trans[7], clause)) for clause in t7]

                t8 = to_cnf(implies(go_to[x, z] & ~person_city[y, z], ~piece_person[x, y]))
                [trans.append(implies(bv_trans[8], clause)) for clause in t8]

    for x in dollar:
        for y in person:
            for z in city:
                t9 = to_cnf(implies(dollar_city[x, z] & person_city[y, z], dollar_person[x, y]))
                [trans.append(implies(bv_trans[9], clause)) for clause in t9]

                t10 = to_cnf(implies(~dollar_city[x, z] & person_city[y, z], ~dollar_person[x, y]))
                [trans.append(implies(bv_trans[10], clause)) for clause in t10]

                t11 = to_cnf(implies(dollar_city[x, z] & ~person_city[y, z], ~dollar_person[x, y]))
                [trans.append(implies(bv_trans[11], clause)) for clause in t11]

    clues = []
    bv_clues = [BoolVar() for i in range(11)]

    # 0. Kelly's piece didn't cost $1250
    # assumption_satisfied( 0  ) => ?a [piece]: ~ cost(a,1250) & from(a,kelly).
    c0a = []
    for a in piece:
        c0a.append(~cost[a, "1250"] & piece_person[a, "kelly"])

    for clause in to_cnf(any(c0a)):
        clues.append(implies(bv_clues[0], clause))

    #type1 = person
    #type2 = city
    #type3 = diffdollar
    # from(piece, type1) = piece_person  = Relation(piece, person)
    # is_linked_with_1(dollar, type1)     dollar_person = Relation(dollar, person)
    # is_linked_with_2(dollar, type2)    dollar_city = Relation(dollar, city)
    # is_linked_with_3(type1, type2)    person_city = Relation(person, city)

    # 1. Valencia cost somewhat more than Isabel's dummy
    # assumption_satisfied( 0  ) => ?b [type3] c [dollar] d [piece] e [dollar]: b>0 & cost(d,c) & from(d,isabel) & e = c+b & cost(valencia,e).
    c1a = []
    for b in diffdollar:
        for c in dollar:
            for d in piece:
                for e in dollar:
                    if (b > 0) and int(e) == int(c) + b:
                        c1a.append(cost[d, c] & piece_person[d, "isabel"] & cost["valencia",e])


    for clause in to_cnf(any(c1a)):
        clues.append(implies(bv_clues[1], clause))

    # 2. The puppet going to Vancouver, the $750 dummy and the $1500 piece are three different dummies
    # assumption_satisfied( 0  ) => ?f [piece] g [piece] h [piece]: ~ (f = g) & ~ (f = h) & ~ (g = h) & go_to(f,vancouver) & cost(g,750) & cost(h,1500).
    c2a = []
    for f in piece:
        for g in piece:
            for h in piece:
                if not (f == g) and not (f ==h) and not (g == h):
                    c2a.append(go_to[f,"vancouver"] & cost[g,"750"] & cost[h,"1500"])

    for clause in to_cnf(any(c2a)):
        clues.append(implies(bv_clues[2], clause))

    # 3. Waldarama didn't cost $750 or $1500
    # assumption_satisfied( 0  ) => ~ (cost(waldarama,750) | cost(waldarama,1500)).
    clues.append(implies(bv_clues[3], ~ (cost["waldarama","750"] | cost["waldarama","1500"])))


    # 4. Kelly's puppet isn't going to Ypsilanti
    # assumption_satisfied( 0  ) => ?i [piece]: ~ go_to(i,ypsilanti) & from(i,kelly).
    c4a = []
    for i in piece:
        c4a.append(~ go_to[i,"ypsilanti"] & piece_person[i,"kelly"])

    for clause in to_cnf(any(c4a)):
        clues.append(implies(bv_clues[4], clause))

    # 5. The dummy going to Mexico City is either Tombawomba or Lucas's puppet
    # assumption_satisfied( 0  ) => ?j [piece]: go_to(j,mexico_city) & (tombawomba = j | (?k [piece]: k = j & from(k,lucas))).
    c5a = []
    for j in piece:
        formule = any([piece_person[k,"lucas"] for k in piece if k == j])
        c5a.append(go_to[j,"mexico_city"] & ("tombawomba" == j | formule))

    for clause in to_cnf(any(c5a)):
        clues.append(implies(bv_clues[5], clause))


    # 6. Nicole's puppet, the $1000 piece and the puppet going to Ypsilanti are three different dummies
    # assumption_satisfied( 0  ) => ?l [piece] m [piece] n [piece]: ~ (l = m) & ~ (l = n) & ~ (m = n) & from(l,nicole) & cost(m,1000) & go_to(n,ypsilanti).
    c6a = []
    for l in piece:
        for m in piece:
            for n in piece:
                if not (l == m) and not (l == n) and not (m == n):
                    c6a.append(piece_person[l,"nicole"] & cost[m,"1000"] & go_to[n,"ypsilanti"])

    for clause in to_cnf(any(c6a)):
        clues.append(implies(bv_clues[6], clause))

    # 7. Of the $750 puppet and the piece going to Mexico City, one is Tombawomba and the other is Isabel's puppet
    # assumption_satisfied( 0  ) => ?o [piece] p [piece]: go_to(p,mexico_city) & ~ (o = p) & ((?q [piece]: tombawomba = o & q = p & from(q,isabel)) | (?r [piece]: tombawomba = p & r = o & from(r,isabel)) ) & cost(o,750).
    c7a = []
    for o in piece:
        for p in piece:
            if not o == p:
                # (?q [piece]: tombawomba = o & q = p & from(q,isabel))
                formule1 = any(
                    [("tombawomba" == o) & (q == p) & piece_person[q,"isabel"] for q in piece]
                )
                # (?r [piece]: tombawomba = p & r = o & from(r,isabel))
                formule2 = any(
                    [("tombawomba" == p) & (r == o) & piece_person[r,"isabel"] for r in piece]
                )
                groteformule = formule1 | formule2
                c7a.append(go_to[p, "mexico_city"] & groteformule & cost[o, "750"])

    for clause in to_cnf(any(c7a)):
        clues.append(implies(bv_clues[7], clause))

    # 8. The puppet going to Ypsilanti cost $250 more than the puppet going to St. Moritz.
    # assumption_satisfied( 0  ) => ?s [piece] t [dollar] u [piece] v [dollar]: go_to(s,ypsilanti) & go_to(u,st_moritz) & cost(u,t) & v = t+250 & cost(s,v).
    c8a = []
    for s in piece:
        for t in dollar:
            for u in piece:
                for v in dollar:
                    if int(v) == int(t) + 250:
                        c8a.append(go_to[s,"ypsilanti"] & go_to[u,"st_moritz"] & cost[u,t] & cost[s,v])

    for clause in to_cnf(any(c8a)):
        clues.append(implies(bv_clues[8], clause))

    # 9. Of the $1000 dummy and the $1250 dummy, one is from Herman and the other is going to Mexico City
    # assumption_satisfied( 0  ) => ?w [piece] x [piece]: ~ (w = x) & (from(w,herman) & go_to(x,mexico_city) | from(x,herman) & go_to(w,mexico_city)) & cost(x,1250) & cost(w,1000).
    c9a = []
    for w in piece:
        for x in piece:
            if not (w == x):
                c9a.append((piece_person[w,"herman"] & go_to[x,"mexico_city"] | piece_person[x,"herman"] & go_to[w,"mexico_city"]) & cost[x,"1250"] & cost[w,"1000"])

    for clause in to_cnf(any(c9a)):
        clues.append(implies(bv_clues[9], clause))

    # 10. Sniffletoe sold for $1000
    # assumption_satisfied( 0  ) => cost(sniffletoe,1000).
    clues.append(implies(bv_clues[9], cost["sniffletoe","1000"]))

    clueTexts =[
        "Kelly's piece didn't cost $1250",
        "Valencia cost somewhat more than Isabel's dummy",
        "The puppet going to Vancouver, the $750 dummy and the $1500 piece are three different dummies",
        "Waldarama didn't cost $750 or $1500",
        "Kelly's puppet isn't going to Ypsilanti",
        "The dummy going to Mexico City is either Tombawomba or Lucas's puppet",
        "Nicole's puppet, the $1000 piece and the puppet going to Ypsilanti are three different dummies",
        "Of the $750 puppet and the piece going to Mexico City, one is Tombawomba and the other is Isabel's puppet",
        "The puppet going to Ypsilanti cost $250 more than the puppet going to St. Moritz.",
        "Of the $1000 dummy and the $1250 dummy, one is from Herman and the other is going to Mexico City",
        "Sniffletoe sold for $1000"
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
    for rel, relStr in zip(rels, ["cost", "go_to", "piece_person", "dollar_person", "dollar_city", "person_city"]):
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


def p12():
    """
    Logic grid puzzle: 'p12' in CPpy
    Based on... to check originally, currently part of ZebraTutor
    Probably part of Jens Claes' master thesis, from a 'Byron...' booklet
    """
    # type1 = drink
    # type2 = food
    drink = ["the_other_type1", "water", "lemonade", "iced_tea", "orange_soda"]
    order = ["the_other_order", "homer", "glen", "wallace", "oliver"]
    dollar = ["5", "6", "7", "8", "9"]
    food = ["the_other_type2", "sloppy_joe", "spaghetti", "hamburger", "turkey_plate"]

    types = [drink, order, dollar, food]
    n = len(types)
    m = len(types[0])
    assert all(len(types[i]) == m for i in range(n)), "all types should have equal length"

    order_drink = Relation(order, drink) #with
    cost = Relation(order, dollar)
    ordered = Relation(order, food)
    drink_dollar = Relation(drink, dollar) #     is_linked_with_1(type1, dollar)
    drink_food = Relation(drink, food) #     is_linked_with_2(type1, type2)
    dollar_food = Relation(dollar, food) #     is_linked_with_3(dollar, type2)
    rels = [order_drink, cost, ordered, drink_dollar, drink_food, dollar_food]

    # Bijectivity
    cnt = 0
    bij, bv_bij = buildBijectivity(rels)

    # Transitivity
    trans = []
    bv_trans =  [BoolVar() for i in range(12)]

    for x in order:
        for y in drink:
            for z in dollar:
                t0 = to_cnf(implies(cost[x, z] & drink_dollar[y, z], order_drink[x, y]))
                [trans.append(implies(bv_trans[0], clause)) for clause in t0]

                t1 = to_cnf(implies(~cost[x, z] & drink_dollar[y, z], ~order_drink[x, y]))
                [trans.append(implies(bv_trans[1], clause)) for clause in t1]

                t2 = to_cnf(implies(cost[x, z] & ~drink_dollar[y, z], ~order_drink[x, y]))
                [trans.append(implies(bv_trans[2], clause)) for clause in t2]

    for x in order:
        for y in drink:
            for z in food:
                t3 = to_cnf(implies(ordered[x, z] & drink_food[y, z], order_drink[x, y]))
                [trans.append(implies(bv_trans[3], clause)) for clause in t3]

                t4 = to_cnf(implies(~ordered[x, z] & drink_food[y, z], ~order_drink[x, y]))
                [trans.append(implies(bv_trans[4], clause)) for clause in t4]

                t5 = to_cnf(implies(ordered[x, z] & ~drink_food[y, z], ~order_drink[x, y]))
                [trans.append(implies(bv_trans[5], clause)) for clause in t5]

    for x in order:
        for y in dollar:
            for z in food:
                t6 = to_cnf(implies(ordered[x, z] & dollar_food[y, z], cost[x, y]))
                [trans.append(implies(bv_trans[6], clause)) for clause in t6]

                t7 = to_cnf(implies(~ordered[x, z] & dollar_food[y, z], ~cost[x, y]))
                [trans.append(implies(bv_trans[7], clause)) for clause in t7]

                t8 = to_cnf(implies(ordered[x, z] & ~dollar_food[y, z], ~cost[x, y]))
                [trans.append(implies(bv_trans[8], clause)) for clause in t8]

    for x in drink:
        for y in dollar:
            for z in food:
                t9 = to_cnf(implies(drink_food[x, z] & dollar_food[y, z], drink_dollar[x, y]))
                [trans.append(implies(bv_trans[9], clause)) for clause in t9]

                t10 = to_cnf(implies(~drink_food[x, z] & dollar_food[y, z], ~drink_dollar[x, y]))
                [trans.append(implies(bv_trans[10], clause)) for clause in t10]

                t11 = to_cnf(implies(drink_food[x, z] & ~dollar_food[y, z], ~drink_dollar[x, y]))
                [trans.append(implies(bv_trans[11], clause)) for clause in t11]

    clues = []
    bv_clues = [BoolVar() for i in range(8)]
    # 0. The order with the lemonade cost $1 more than the order with the water
    # assumption_satisfied( 0  ) => ?a [order] b [dollar] c [order] d [dollar]: with(a,lemonade) & with(c,water) & cost(c,b) & d = b+1 & cost(a,d).
    c0a = []
    for a in order:
        for b in dollar:
            for c in order:
                for d in dollar:
                    if int(d) == int(b) + 1:
                        c0a.append(order_drink[a, "lemonade"] & order_drink[c, "water"] & cost[c, b] & cost[a, d])
    for clause in to_cnf(any(c0a)):
        clues.append(implies(bv_clues[0], clause))

    # 1. Homer paid $7
    # assumption_satisfied( 0  ) => cost(homer,7).
    clues.append(implies(bv_clues[0], cost["homer", "7"]))

    # 2. Glen paid $3 less than whoever ordered the sloppy joe
    # assumption_satisfied( 0  ) => ?e [dollar] f [order] g [dollar]: ordered(f,sloppy_joe) & cost(f,e) & g = e-3 & cost(glen,g).
    c2a = []
    for e in dollar:
        for f in order:
            for g in dollar:
                if int(g) == int(e) - 3:
                    c2a.append(ordered[f,"sloppy_joe"] & cost[f, e] & cost["glen", g])

    for clause in to_cnf(any(c2a)):
        clues.append(implies(bv_clues[2], clause))

    # 3. Wallace didn't have the iced tea
    # assumption_satisfied( 0  ) => ~ with(wallace,iced_tea).
    clues.append(implies(bv_clues[3], ~order_drink["wallace","iced_tea"]))

    # 4. Of the diner who paid $6 and Homer, one ordered the spaghetti and the other drank the water
    # assumption_satisfied( 0  ) => ?h [order]: cost(h,6) & ~ (h = homer) & (ordered(h,spaghetti) & with(homer,water) | ordered(homer,spaghetti) & with(h,water)).
    c4a = []
    for h in order:
        c4a.append(cost[h, "6"] & (ordered[h,"spaghetti"] & order_drink["homer", "water"] | ordered["homer", "spaghetti"] & order_drink[h, "water"]))

    for clause in to_cnf(any(c4a)):
        clues.append(implies(bv_clues[4], clause))

    # 5. Oliver ordered the hamburger
    # assumption_satisfied( 0  ) => ordered(oliver,hamburger).
    clues.append(implies(bv_clues[5], ordered["oliver","hamburger"]))

    # 6. The five diners were whoever ordered the turkey plate, Oliver, Glen, the person who got the iced tea and the person who paid $5
    # assumption_satisfied( 0  ) => ?i [order] j [order] k [order]: ~ (i = oliver) & ~ (i = glen) & ~ (i = j) & ~ (i = k) & ~ (oliver = glen) & ~ (oliver = j) & ~ (oliver = k) & ~ (glen = j) & ~ (glen = k) & ~ (j = k) & ordered(i,turkey_plate) & with(j,iced_tea) & cost(k,5).
    c6a = []
    for i in order:
        for j in order:
            for k in order:
                if not (i == "oliver") and not (i == "glen") and not (i == j) and not (i == k) and not ("oliver" == j) and not ("oliver" == k) and not("glen" == j) and not ("glen" == k) and not (j == k):
                    c6a.append(ordered[i,"turkey_plate"] & order_drink[j,"iced_tea"] & cost[k, "5"])

    for clause in to_cnf(any(c6a)):
        clues.append(implies(bv_clues[6], clause))

    # 7. Glen didn't have the orange soda
    # assumption_satisfied( 0  ) => ~ with(glen,orange_soda).
    clues.append(implies(bv_clues[7], ~order_drink["glen", "orange_soda"]))

    clueTexts = [
        "The order with the lemonade cost $1 more than the order with the water",
        "Homer paid $7",
        "Glen paid $3 less than whoever ordered the sloppy joe",
        "Wallace didn't have the iced tea",
        "Of the diner who paid $6 and Homer, one ordered the spaghetti and the other drank the water",
        "Oliver ordered the hamburger",
        "The five diners were whoever ordered the turkey plate, Oliver, Glen, the person who got the iced tea and the person who paid $5",
        "Glen didn't have the orange soda"
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
    for rel, relStr in zip(rels, ["order_drink", "cost", "ordered", "drink_dollar", "drink_food", "dollar_food"]):
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

    # for rel in rels:
    #     type1_1 = rel.rows
    #     type1_2= rel.cols
    #     for rel2 in rels:
    #         type2_1=rel2.rows
    #         type2_2=rel2.cols
    #         if type2_1:
    #             break
    #         for rel3 in rels:
    # for rel in rels:
    #     type1_1 = rel.rows
    #     type1_2= rel.cols
    #     for rel2 in rels:
    #         type2_1=rel2.rows
    #         type2_2=rel2.cols
    #         if type2_1:
    #             break
    #         for rel3 in rels:
    #             if not rel3 > rel 2:
    #                 break
    #             bv1 = BoolVar()
    #             bv2 = BoolVar()
    #             bv3 = BoolVar()
    #             #GENERATE ALLE SETS OF THREE "MATHCING RELATIONS"
    #             # e.g. p(T1,T2) p2(T2,T3), p3(T1,T3)
    #             # or p(T1,T2) p2(T2,T3), p3(T3,T1)
    #             # EASIER: GENERATE ALL SETS OF THREE DIFFERENT TYPES. 
    #             # Make procedure that gives you the right relation given two types (possibly "swapped")
    #             # map constructed when making relations. R
    #             for x in person:
    #                 for y in sauce:
    #                     for z in dollar:

    #                         t0 = to_cnf(implies(paid[x, z] & sauce_dollar[y, z], chose[x, y]))
    #                         [trans.append(implies(bv_trans[0], clause)) for clause in t0]

    #                         t1 = to_cnf(implies(~paid[x, z] & sauce_dollar[y, z], ~chose[x, y]))
    #                         [trans.append(implies(bv_trans[1], clause)) for clause in t1]

    #                         t2 = to_cnf(implies(paid[x, z] & ~sauce_dollar[y, z], ~chose[x, y]))
    #                         [trans.append(implies(bv_trans[2], clause)) for clause in t2]
    #             if not rel3 > rel 2:
    #                 break
    #             bv1 = BoolVar()
    #             bv2 = BoolVar()
    #             bv3 = BoolVar()
    #             #GENERATE ALLE SETS OF THREE "MATHCING RELATIONS"
    #             # e.g. p(T1,T2) p2(T2,T3), p3(T1,T3)
    #             # or p(T1,T2) p2(T2,T3), p3(T3,T1)
    #             # EASIER: GENERATE ALL SETS OF THREE DIFFERENT TYPES. 
    #             # Make procedure that gives you the right relation given two types (possibly "swapped")
    #             # map constructed when making relations. R
    #             for x in person:
    #                 for y in sauce:
    #                     for z in dollar:

    #                         t0 = to_cnf(implies(paid[x, z] & sauce_dollar[y, z], chose[x, y]))
    #                         [trans.append(implies(bv_trans[0], clause)) for clause in t0]

    #                         t1 = to_cnf(implies(~paid[x, z] & sauce_dollar[y, z], ~chose[x, y]))
    #                         [trans.append(implies(bv_trans[1], clause)) for clause in t1]

    #                         t2 = to_cnf(implies(paid[x, z] & ~sauce_dollar[y, z], ~chose[x, y]))
    #                         [trans.append(implies(bv_trans[2], clause)) for clause in t2]

# angie puttanesca => 4
# angie 4 => 17
# puttanesca 4 => 61


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
    clue0 =  [ordered[a, "capellini"] & chose[d, "arrabiata_sauce"] & paid[d, c] & paid[a, e]
                for a in person
                for b in [-4, 4, -8, 8,  -12, 12]
                for c in dollar
                for d in person
                for e in dollar if (b > 0) and (int(e) == int(c)-b)]
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

        for h in [-4, 4, -8, 8, -12, 12]:
            if h > 0:
                for i in dollar:
                    for j in person:
                        for k in dollar:
                            if int(k) == int(i) - h:
                                c2a.append(ordered[g, "taglioni"] & chose[j, "marinara_sauce"] & paid[j, i] & paid[g, k])
    print(any.__code__)
    [clues.append(implies(bv_clues[2], clause)) for clause in to_cnf(any(c2a))]

    #  3. The person who ordered tagliolini paid more than Angie
    # assumption_satisfied( 0  ) => ?l [person] m [type5] n [dollar] o [dollar]: ordered(l,tagliolini) & m>0 & paid(angie,n) & o = n+m & paid(l,o).
    c3a = []
    for l in person:
        for m in [-4, 4, -8, 8, -12, 12]:
            if m > 0:
                for n in dollar:
                    for o in dollar:
                        if int(o) == int(n) + m:
                            c3a.append(ordered[l, "taglioni"] & paid["angie", n] & paid[l, o])
    [clues.append(implies(bv_clues[3], clause)) for clause in to_cnf(any(c3a))]

    #  4. The person who ordered rotini is either the person who paid $8 more than Damon or the person who paid $8 less than Damon
    # assumption_satisfied( 0  ) => ?
    # p [person]: ordered(p,rotini) & 
    #           ((?q [person] r [dollar] s [dollar]: paid(damon,r) & s = r+8 & paid(q,s) & q = p) 
    #           | (?t [person] u [dollar] v [dollar]: paid(damon,u) & v = u-8 & paid(t,v) & t = p)).

    #list with: for every person: two options
    c4a = []
    for p in person:
        formule1 = any(
            [paid["damon", r] & paid[q,s] for q in person for r in dollar for s in dollar if (int(s) == int(r) - 8) and (q == p)]
        )
        formule2 = any(
            [paid["damon", r] & paid[q,s] for q in person for r in dollar for s in dollar if (int(s) == int(r) + 8) and (q == p)]
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
    c7a = [chose[p, 'arrabiata_sauce'] &  ( (p == 'angie') | (p == 'elisa'))  for p in person] 
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

    for rel in rels:
        rowNames = list(rel.df.index)
        columnNames = list(rel.df.columns)
        for r in rowNames:
            for c in columnNames:
                print(r, c, rel.df.at[r, c].name + 1)

    print(explainable_facts)
    # true_facts = [67, 50, 9, 70, 56, 14, 73, 59, 7, 80, 61, 4]
    true_facts = [67, 50, 9, 70, 56, 14, 73]

    matching_table = {
        'bvRel': bvRels,
        'Transitivity constraint': [bv.name + 1 for bv in bv_trans],
        'Bijectivity': [bv.name + 1 for bv in bv_bij],
        'clues' : {
            bv.name + 1: clueTexts[i] for i, bv in enumerate(bv_clues)
        }
    }

    return hard_clauses, soft_clauses, weights, explainable_facts, matching_table, [[l] for l in true_facts], rels


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
        bv1 = BoolVar()
        bv2 = BoolVar()
        for col_ids in rel.df:
            # one per column
            atleast, atmost = exactly_one_at_most(rel[:, col_ids])
            [bij.append(implies(bv1, clause)) for clause in atmost]
            bij.append(implies(bv2, atleast))
        bv_bij.append(bv1)
        bv_bij.append(bv2)

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

