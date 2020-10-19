import itertools
import sys

# import numpy
import pandas as pd

sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
sys.path.append('/home/emilio/Documents/cppy_src/')
sys.path.append('/home/emilio/documents/cppy_mysrc/')

from cppy import *
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
            trans.append( [implies(is_old[p,a] & age_city[a,c],
                                        lives_in[p,c]) for a in age] )
        for b in birthplace:
            trans.append( [implies(is_old[p,a] & age_birth[a,b],
                                        native[p,b]) for a in age] )
            trans.append( [implies(lives_in[p,c] & city_birth[c,b],
                                        native[p,b]) for c in city] )
    for a in age:
        for b in birthplace:
            trans.append( [implies(age_city[a,c] & city_birth[c,b],
                                        age_birth[a,b]) for c in city] )

    # Clues
    clues = []
    # Mattie is 113 years old
    clues.append( is_old['Mattie', '113'] )

    # The person who lives in Tehama is a native of either Kansas or Oregon
    clues.append( [implies(lives_in[p,'Tehama'],
                            native[p,'Kansas'] | native[p,'Oregon']) for p in person] )

    # The Washington native is 1 year older than Ernesto
    clues.append( [implies(age_birth[a,'Washington'],
                            is_old['Ernesto',str(int(a)-1)]) for a in age] )

    # Roxanne is 2 years younger than the Kansas native
    clues.append( [implies(is_old['Roxanne',a], 
                            age_birth[str(int(a)+2), 'Kansas']) for a in age] )

    # The person who lives in Zearing isn't a native of Alaska
    clues.append( [implies(lives_in[p,'Zearing'],
                            ~native[p,'Alaska']) for p in person] )

    # The person who is 111 years old doesn't live in Plymouth
    clues.append( [implies(is_old[p,'111'],
                            ~lives_in[p,'Plymouth']) for p in person] )

    # The Oregon native is either Zachary or the person who lives in Tehama
    clues.append( [implies(native[p,'Oregon'],
                            (p == 'Zachary') | lives_in[p,'Tehama']) for p in person] )

    # The person who lives in Shaver Lake is 1 year younger than Roxanne
    clues.append( [implies(age_city[a,'Shaver Lake'],
                            is_old['Roxanne',str(int(a)+1)]) for a in age] )

    # The centenarian who lives in Plymouth isn't a native of Alaska
    clues.append( [implies(lives_in[p,'Plymouth'],
                            ~native[p,'Alaska']) for p in person] )

    # Of the person who lives in Tehama and Mattie, one is a native of Alaska and the other is from Kansas
    clues.append( [implies(lives_in[p,'Tehama'],
                            (p != 'Mattie') &
                            ((native['Mattie','Alaska'] & native[p,'Kansas']) |
                            (native[p,'Alaska'] & native['Mattie','Kansas']))) for p in person] )

    # model = Model(bij + trans + clues)
    model = Model(clues)
    return model


def simpleProblem():
    (mayo, ketchup, andalouse) = BoolVar(3)

    c0 = mayo
    c1 = ~mayo | ~andalouse | ketchup
    c2 = ~mayo | andalouse | ketchup
    c3 = ~ketchup | ~andalouse
    
    constraints = [c0, c1, c2, c3]
    cnf = cnf_to_pysat(constraints)
    explainable_facts = set({mayo.name+1, ketchup.name+1, andalouse.name+1})

    return cnf, explainable_facts


def frietKotProblem():
    # Construct the model.
    (mayo, ketchup, curry, andalouse, samurai) = BoolVar(5)

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
    explainable_facts = {
        mayo.name+1:"mayo", 
        ketchup.name+1:"ketchup", 
        andalouse.name+1:"andalouse", 
        curry.name+1:"curry", 
        samurai.name+1:"samurai"}


    return cnf, explainable_facts.keys(), explainable_facts.values()

