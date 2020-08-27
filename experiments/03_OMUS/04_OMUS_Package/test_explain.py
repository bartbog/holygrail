import itertools
import sys

# import numpy
import pandas as pd

# csp explanations

from csp_explain import omusExplain

sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
# sys.path.append('/home/emilio/Documents/cppy/')
from cppy import BoolVarImpl, Comparison, Model, Operator, cnf_to_pysat
# from cppy.solver_interfaces.pysat_tools import 
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
    allpairs = [(-a|-b) for a,b in itertools.combinations(lst,2)]
    return [any(lst)] + allpairs


def p93():
    # bv for tracking clues during explanation generation
    trans_bv = [implies(bv, tr) for bv, tr  in zip(bv_trans, trans) ]
    bij_bv = [implies(bv, bi) for bv, bi  in zip(bv_bij, bij) ]
    clues_bv = [implies(bv, clue) for bv, clue  in zip(bv_clues, clues) ]

    model = Model([bij_bv, trans_bv, clues_bv])
    return model


def p25():
    # bv for tracking clues during explanation generation
    trans_bv = [implies(bv, tr) for bv, tr  in zip(bv_trans, trans) ]
    bij_bv = [implies(bv, bi) for bv, bi  in zip(bv_bij, bij) ]
    clues_bv = [implies(bv, clue) for bv, clue  in zip(bv_clues, clues) ]

    model = Model([bij_bv, trans_bv, clues_bv])
    return model


def p20():
    # bv for tracking clues during explanation generation
    trans_bv = [implies(bv, tr) for bv, tr  in zip(bv_trans, trans) ]
    bij_bv = [implies(bv, bi) for bv, bi  in zip(bv_bij, bij) ]
    clues_bv = [implies(bv, clue) for bv, clue  in zip(bv_clues, clues) ]

    model = Model([bij_bv, trans_bv, clues_bv])
    return model


def p19():
    # bv for tracking clues during explanation generation
    trans_bv = [implies(bv, tr) for bv, tr  in zip(bv_trans, trans) ]
    bij_bv = [implies(bv, bi) for bv, bi  in zip(bv_bij, bij) ]
    clues_bv = [implies(bv, clue) for bv, clue  in zip(bv_clues, clues) ]

    model = Model([bij_bv, trans_bv, clues_bv])
    return model


def p18():
    # bv for tracking clues during explanation generation
    trans_bv = [implies(bv, tr) for bv, tr  in zip(bv_trans, trans) ]
    bij_bv = [implies(bv, bi) for bv, bi  in zip(bv_bij, bij) ]
    clues_bv = [implies(bv, clue) for bv, clue  in zip(bv_clues, clues) ]

    model = Model([bij_bv, trans_bv, clues_bv])
    return model


def p17():
    # bv for tracking clues during explanation generation
    trans_bv = [implies(bv, tr) for bv, tr  in zip(bv_trans, trans) ]
    bij_bv = [implies(bv, bi) for bv, bi  in zip(bv_bij, bij) ]
    clues_bv = [implies(bv, clue) for bv, clue  in zip(bv_clues, clues) ]

    model = Model([bij_bv, trans_bv, clues_bv])
    return model


def p16():
    # type1 = vocabulary
    objects = ['the_other_type1', 'rings', 'mobile_phones', 'flashlights', 'rubber_balls']
    juggler = ['the_other_juggler', 'howard', 'otis', 'gerald', 'floyd']
    # type2 = material
    material = ['the_other_type2', 'quasqueton', 'kingsburg', 'carbon', 'nice']
    spot = ['1', '2', '3', '4', '5']

    types = [objects, juggler, material, spot]
    n_types = len(types)
    n_dom = len(types[0])
    n_bij = 24
    n_trans = 12
    n_clues = 10
    assert all(len(types[i]) == n_dom for i in range(n_types)), "all types should have equal length"

    used = Relation(juggler, objects)
    made_of = Relation(juggler, material)
    went = Relation(juggler, spot)
    object_material = Relation(objects, material)
    object_spot = Relation(objects, spot)
    material_spot = Relation(material, spot)

    relations = [drinks, pays, ordered, drink_dollar, drink_food, dollar_food]

    # Bijectivity
    bij = []
    bv_bij = [BoolVar() for i in range(n_bij)]
    for rel in relations:
        # for each relation
        for col in rel.df:
            # one per column
            #TODO: Possible to encode it as ? bij.append( sum(rel[:,col]) == 1 )
            bij.append( implies(bv1, sum(rel[:,col]) >= 1 ))
            bij.append( implies(bv2, sum(rel[:,col]) <= 1 ))

        for (_,row) in rel.df.iterrows():
            # one per row
            #TODO: Possible to encode it as ? bij.append( sum(row) == 1 )
            bij.append( implies(bv1, sum(row) >= 1 ))
            bij.append( implies(bv2, sum(row) <= 1 ))

    # Transitivity
    trans = [ [] for i in range(n_trans)]
    bv_trans = [BoolVar() for i in range(n_trans)]


    for x in  juggler:
        for y in  objects:
            for z in  material:
                # ! x y z: from(x, z) & is_linked_with_1(y, z)=>  used(x, y).
                trans[0].append( implies( made_of[x, z] & object_material[y, z], used[x, y]) )
                # ! x y z: ~from(x, z) & is_linked_with_1(y, z)=> ~ used(x, y).
                trans[1].append( implies( ~made_of[x, z] & object_material[y, z], ~used[x, y]) )
                # ! x y z: from(x, z) & ~is_linked_with_1(y, z)=> ~ used(x, y).
                trans[2].append( implies( made_of[x, z] & ~object_material[y, z], ~used[x, y]) )

    for x in  juggler:
        for y in  objects:
            for z in spot :
                # ! x y z: went(x, z) & is_linked_with_2(y, z)=>  used(x, y).
                trans[3].append( implies( went[x, z] & object_spot[y, z], used[x, y]) )
                # ! x y z: ~went(x, z) & is_linked_with_2(y, z)=> ~ used(x, y).
                trans[4].append( implies( ~went[x, z] & object_spot[y, z], ~used[x, y]) )
                # ! x y z: went(x, z) & ~is_linked_with_2(y, z)=> ~ used(x, y).
                trans[5].append( implies( went[x, z] & ~object_spot[y, z], ~used[x, y]) )

    for x in juggler :
        for y in material :
            for z in spot :
                # ! x y z: went(x, z) & is_linked_with_3(y, z)=>  from(x, y).
                trans[6].append( implies( went[y, z] & material_spot[y, z],made_of[x, y]))
                # ! x y z: ~went(x, z) & is_linked_with_3(y, z)=> ~ from(x, y).
                trans[7].append( implies( ~went[y, z] & material_spot[y, z],~made_of[x, y]))
                # ! x y z: went(x, z) & ~is_linked_with_3(y, z)=> ~from(x, y) .
                trans[8].append( implies( went[y, z] & ~material_spot[y, z],~made_of[x, y]))
    for x in objects :
        for y in material :
            for z in spot :
                # ! x y z: is_linked_with_2(x, z) & is_linked_with_3(y, z)=>  is_linked_with_1(x, y).
                trans[9].append(implies( object_spot[x, z] & material_spot[y, z], object_material[x, y]))
                # ! x y z: ~is_linked_with_2(x, z) & is_linked_with_3(y, z)=> ~ is_linked_with_1(x, y).
                trans[10].append(implies( ~object_spot[x, z] & material_spot[y, z], ~object_material[x, y]))
                # ! x y z: is_linked_with_2(x, z) & ~is_linked_with_3(y, z)=> ~ is_linked_with_1(x, y).
                trans[11].append(implies( object_spot[x, z] & ~material_spot[y, z], ~object_material[x, y]))

    # Clues
    clues = []
    bv_clues = [BoolVar() for i in range(n_clues)]

    # used = Relation(juggler, objects)
    # from: made_of = Relation(juggler, material)
    # went = Relation(juggler, spot)
    # is_linked_with_1: object_material = Relation(objects, material)
    # is_linked_with_2: object_spot = Relation(objects, spot)
    # is_linked_with3: material_spot = Relation(material, spot)

    # # type1 = vocabulary
    # objects = ['the_other_type1', 'rings', 'mobile_phones', 'flashlights', 'rubber_balls']
    # juggler = ['the_other_juggler', 'howard', 'otis', 'gerald', 'floyd']
    # # type2 = material
    # material = ['the_other_type2', 'quasqueton', 'kingsburg', 'carbon', 'nice']
    # spot = ['1', '2', '3', '4', '5']

    # The juggler who went fourth was either the performer from Quasqueton or the juggler who used rings
    clues.append([ ])
    # The juggler who used flashlights performed one spot after the person who used mobile phones
    clues.append([ ])
    # The performer from Kingsburg performed one spot before Howard
    clues.append([implies() for p in juggler])
    # Otis wasn't from Carbon
    clues.append(~made_of['otis', 'carbon'])
    # Of the performer who went second and the juggler who used rings, one was from Carbon and the other is Howard
    clues.append( )
    # TODO: The performer who went third, Gerald and the person from Kingsburg are three different people
    clues.append( )
    # Floyd was either the juggler who went second or the juggler from Quasqueton
    clues.append( went['floyd', '2'] | made_of['floyd', 'quasqueton'] )

    # The person who went third used rings
    clues.append([went[r, '3'] & used[r , 'rings'] for r in juggler])
    # The juggler who went second wasn't from Nice
    clues.append([went[r, '2'] & ~made_of[r, 'nice']  for r in juggler])
    # Floyd juggles rubber balls
    clues.append(used('floyd', 'rubber_balls'))

    # bv for tracking clues during explanation generation
    # TODO : change implementation of bv for tr/bij/clues
    # TODO: for every clause in 1 tr/bij/clues use same bv
    trans_bv = [implies(bv, tr) for bv, tr  in zip(bv_trans, trans) ]
    bij_bv = [implies(bv, bi) for bv, bi  in zip(bv_bij, bij) ]
    clues_bv = [implies(bv, clue) for bv, clue  in zip(bv_clues, clues) ]

    model = Model([bij_bv, trans_bv, clues_bv])
    return model

def p12():
    # type1 = drink
    # type2 = food
    # order = person
    drink = ['the_other_type1', 'water', 'lemonade', 'iced_tea', 'orange_soda']
    person = ['the_other_order', 'homer', 'glen', 'wallace', 'oliver']
    dollar = ['5', '6', '7', '8', '9']
    food = ['the_other_type2', 'sloppy_joe', 'spaghetti', 'hamburger', 'turkey_plate']

    # is_linked_with_1 = drink_dollar
    # is_linked_with_2 = drink_food
    # is_linked_with_3 = dollar_food
    # with = drinks
    # cost = pays
    drinks = Relation(person, drink)
    pays = Relation(person, dollar)
    ordered = Relation(person, food)
    drink_dollar = Relation(drink, dollar)
    drink_food = Relation(drink, food)
    dollar_food = Relation(dollar, food)

    relations = [drinks, pays, ordered, drink_dollar, drink_food, dollar_food]

    types = [drink, person, dollar, food]
    n_types = len(types)
    n_dom = len(types[0])
    assert all(len(types[i]) == n_dom for i in range(n_types)), "all types should have equal length"
    n_clues = 8
    n_bij = 24
    n_trans = 12

    # Bijectivity
    bij = []
    bv_bij = [BoolVar() for i in range(n_bij)]
    for rel in relations:
        # for each relation
        for col in rel.df:
            # one per column
            #TODO: Possible to encode it as ? bij.append( sum(rel[:,col]) == 1 )
            bij.append( implies(bv1, sum(rel[:,col]) >= 1 ))
            bij.append( implies(bv2, sum(rel[:,col]) <= 1 ))

        for (_,row) in rel.df.iterrows():
            # one per row
            #TODO: Possible to encode it as ? bij.append( sum(row) == 1 )
            bij.append( implies(bv1, sum(row) >= 1 ))
            bij.append( implies(bv2, sum(row) <= 1 ))

    # Transitivity
    trans = [ [] for i in range(n_trans)]
    bv_trans = [BoolVar() for i in range(n_trans)]

    for x in person :
        for y in drink :
            for z in dollar :
                # ! x y z: cost(x, z) & is_linked_with_1(y, z)  =>  with(x, y).
                trans[0].append( implies( pays[x, z] & drink_dollar[y, z], drinks[x, y] ))
                # ! x y z:   cost(x, z) & ~is_linked_with_1(y, z)  => ~ with(x, y).
                trans[1].append( ~implies( pays[x, z] & drink_dollar[y, z],~ drinks[x, y] ))
                # ! x y z:  ~cost(x, z) & is_linked_with_1(y, z)  => ~with(x, y).
                trans[2].append( implies( pays[x, z] & ~drink_dollar[y, z], ~drinks[x, y] ))
    for x in person :
        for y in drink :
            for z in food :
                # ! x y z:  ordered(x, z) & is_linked_with_2(y, z)  =>  with(x, y).
                trans[3].append( implies(  ordered[x, z] & drink_food[y, z], drinks[x, y]))
                # ! x y z:   ordered(x, z) & ~is_linked_with_2(y, z)  => ~ with(x, y).
                trans[4].append( implies(  ~ordered[x, z] & drink_food[y, z], ~drinks[x, y]))
                # ! x y z:   ~ordered(x, z) & is_linked_with_2(y, z)  => ~with(x, y).
                trans[5].append( implies(  ordered[x, z] & ~drink_food[y, z], ~drinks[x, y]))
    for x in person :
        for y in dollar :
            for z in food :
                # ! x y z:  ordered(x, z) & is_linked_with_3(y, z)  =>  cost(x, y).
                trans[6].append( implies(  ordered[x, z] & dollar_food[y, z], pays[x, y]))
                # ! x y z:  ordered(x, z) & ~ is_linked_with_3(y, z)  => ~ cost(x, y).
                trans[7].append( implies( ~ordered[x, z] & dollar_food[y, z], ~pays[x, y]))
                # ! x y z:  ~  ordered(x, z) & is_linked_with_3(y, z)  => ~cost(x, y).
                trans[8].append( implies(  ordered[x, z] & ~dollar_food[y, z], ~pays[x, y]))
    for x in drink :
        for y in dollar :
            for z in food :
                # ! x y z:  is_linked_with_2(x, z) & is_linked_with_3(y, z)  =>  is_linked_with_1(x, y).
                trans[9].append( implies( drink_food[x, z] & dollar_food[y, z], drink_dollar[x, y]) )
                # ! x y z:  ~is_linked_with_2(x, z) & is_linked_with_3(y, z)   => ~ is_linked_with_1(x, y).
                trans[10].append( implies( ~drink_food[x, z] & dollar_food[y, z], ~drink_dollar[x, y]) )
                # ! x y z:  is_linked_with_2(x, z) & ~is_linked_with_3(y, z)   => ~is_linked_with_1(x, y).
                trans[11].append( implies( drink_food[x, z] & ~dollar_food[y, z], ~drink_dollar[x, y]) )

    # Clues
    clues = []
    bv_clues = [BoolVar() for i in range(n_clues)]

    # TODO: The order with the lemonade cost $1 more than the order with the water
    clues.append( )

    # Homer paid $7
    clues.append( pays('homer', '7'))

    # TODO:  Glen paid $3 less than whoever ordered the sloppy joe
    clues.append(  )

    # Wallace didn't have the iced tea
    clues.append( ~drinks('wallace', 'iced_tea'))

    # TODO:  Of the diner who paid $6 and Homer, one ordered the spaghetti and the other drank the water
    clues.append( )

    # Oliver ordered the hamburger
    clues.append( ordered('oliver', 'hamburger') )

    # TODO:  The five diners were whoever ordered the turkey plate, Oliver, Glen, the person who got the iced tea and the person who paid $5
    clues.append(  )

    # Glen didn't have the orange soda
    clues.append( ~drinks('glen', 'orange_soda') )

    # bv for tracking clues during explanation generation
    trans_bv = [implies(bv, tr) for bv, tr  in zip(bv_trans, trans) ]
    bij_bv = [implies(bv, bi) for bv, bi  in zip(bv_bij, bij) ]
    clues_bv = [implies(bv, clue) for bv, clue  in zip(bv_clues, clues) ]

    model = Model([bij_bv, trans_bv, clues_bv])
    return model


def p5():
    person = ['Mattie', 'Ernesto', 'Roxanne', 'Zachary', 'John']
    age = ['109', '110', '111', '112', '113']
    city = ['Brussels', 'Tehama', 'Zearing', 'Plymouth', 'Shaver Lake']
    birthplace = ['Mexico', 'Oregon', 'Kansas', 'Washington', 'Alaska']

    types = [person, age, city, birthplace]
    n_types = len(types)
    n_dom = len(types[0])
    assert all(len(types[i]) == n_dom for i in range(n_types)), "all types should have equal length"
    n_bij = 24
    n_trans = 12
    n_clues = 10

    is_old = Relation(person, age)
    lives_in = Relation(person, city)
    native = Relation(person, birthplace)
    age_city = Relation(age, city)
    age_birth = Relation(age, birthplace)
    city_birth = Relation(city, birthplace)

    relations = [is_old, lives_in, native, age_city, age_birth, city_birth]

    # Bijectivity
    bij = []
    bv_bij = [BoolVar() for i in range(n_bij)]
    for rel in [is_old, lives_in, native, age_city, age_birth, city_birth]:
        # for each relation
        for col_ids in rel.df:
            # one per column
            bij += exactly_one(rel[:,col_ids])
        for (_,row) in rel.df.iterrows():
            # one per row
            bij += exactly_one(row)

    # Transitivity
    trans = [ ]
    bv_trans = [BoolVar() for i in range(n_trans)]

    for x in person:
        for z in birthplace:
            for y in age:
                # ! x y z:  from(x, z) & is_linked_with_1(y, z) => is_old(x, y).
                trans.append(implies( bv_trans[0], implies( native[x, z] & age_birth[y, z], is_old[x, y])) )
    #             # ! x y z:  ~from(x, z) & is_linked_with_1(y, z) => ~is_old[x, y].
                trans.append(implies( bv_trans[1], implies( ~native[x, z] & age_birth[y, z], ~is_old[x, y]) ))
    #             # ! x y z:  from(x, z) & ~is_linked_with_1(y, z) => ~is_old[x, y].
                trans.append(implies( bv_trans[2], implies( native[x, z] & ~age_birth[y, z], ~is_old[x, y]) ))


    for x in person :
        for y in age :
            for z in city :
                # ! x y z:  lives_in(x, z) & is_linked_with_2(y, z) => is_old[x, y].
                trans.append(implies( bv_trans[3],  implies( lives_in[x, z] & age_city[y, z], is_old[x, y])))
                # ! x y z:  ~lives_in(x, z) & is_linked_with_2(y, z) => ~is_old(x, y).
                trans.append(implies( bv_trans[4],  implies( ~lives_in[x, z] & age_city[y, z], ~is_old[x, y])))
                # ! x y z:  lives_in(x, z) & ~is_linked_with_2(y, z) => ~is_old(x, y).
                trans.append(implies( bv_trans[5], implies( lives_in[x, z] & ~age_city[y, z], ~is_old[x, y])))

    for x in person :
        for y in birthplace :
            for z in city :
                #  ! x y z:  lives_in(x, z) & is_linked_with_3(y, z) => from(x, y).
                trans.append(implies( bv_trans[6], implies( lives_in[x, z] & city_birth[z, y] , native[x, y] )))
                # ! x y z:  ~lives_in(x, z) & is_linked_with_3(y, z) => ~from(x, y).
                trans.append(implies( bv_trans[7], implies( ~lives_in[x, z] & city_birth[z, y] , ~native[x, y]) ))
                # ! x y z:  lives_in(x, z) & ~is_linked_with_3(y, z) => ~from(x, y).
                trans.append(implies( bv_trans[8], implies( lives_in[x, z] & ~city_birth[z, y] , ~native[x, y] )))

    for x in age :
        for y in birthplace:
            for z in city :
                #  ! x y z:  is_linked_with_2(x, z) & is_linked_with_3(y, z) => is_linked_with_1(x, y).
                trans.append(implies( bv_trans[9], implies( age_city[x, z] & city_birth[z, y], age_birth[x, y])))

                # ! x y z:  ~is_linked_with_2(x, z) & is_linked_with_3(y, z) => ~is_linked_with_1(x, y).
                trans.append(implies( bv_trans[10], implies( ~age_city[x, z] & city_birth[z, y], ~age_birth[x, y])))

                # ! x y z:  is_linked_with_2(x, z) & ~is_linked_with_3(y, z) => ~is_linked_with_1(x, y).
                trans.append(implies( bv_trans[11], implies( age_city[x, z] & ~city_birth[z, y], ~age_birth[x, y])))

    # Clues
    clues = []
    clues_text = [
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
    # bv_clues = [BoolVar() for i in range(n_clues)]

    # # Mattie is 113 years old
    # clues.append( implies(bv_clues[0], is_old['Mattie', '113']) )

    # # The person who lives in Tehama is a native of either Kansas or Oregon
    # clues.append( [implies(bv_clues[1], implies(lives_in[p,'Tehama'],
    #                         native[p,'Kansas'] | native[p,'Oregon'])) for p in person] )

    # # The Washington native is 1 year older than Ernesto
    # clues.append( [implies(bv_clues[2], implies(age_birth[a,'Washington'],
    #                         is_old['Ernesto',str(int(a)-1)])) for a in age] )

    # # Roxanne is 2 years younger than the Kansas native
    # clues.append( [implies(bv_clues[3], implies(is_old['Roxanne',a], 
    #                         age_birth[str(int(a)+2), 'Kansas'])) for a in age] )

    # # The person who lives in Zearing isn't a native of Alaska
    # clues.append( [implies(bv_clues[4], implies(lives_in[p,'Zearing'],
    #                         ~native[p,'Alaska'])) for p in person] )

    # # The person who is 111 years old doesn't live in Plymouth
    # clues.append( [implies(bv_clues[5], implies(is_old[p,'111'],
    #                         ~lives_in[p,'Plymouth'])) for p in person] )

    # # The Oregon native is either Zachary or the person who lives in Tehama
    # clues.append( [implies(bv_clues[6], implies(native[p,'Oregon'],
    #                         (p == 'Zachary') | lives_in[p,'Tehama'])) for p in person] )

    # # The person who lives in Shaver Lake is 1 year younger than Roxanne
    # clues.append( [implies(bv_clues[7], implies(age_city[a,'Shaver Lake'],
    #                         is_old['Roxanne',str(int(a)+1)])) for a in age] )

    # # The centenarian who lives in Plymouth isn't a native of Alaska
    # clues.append( [implies(bv_clues[8], implies(lives_in[p,'Plymouth'],
    #                         ~native[p,'Alaska'])) for p in person] )

    # # Of the person who lives in Tehama and Mattie, one is a native of Alaska and the other is from Kansas
    # clues.append( [implies(bv_clues[9], implies(lives_in[p,'Tehama'],
    #                         (p != 'Mattie') &
    #                         ((native['Mattie','Alaska'] & native[p,'Kansas']) |
    #                         (native[p,'Alaska'] & native['Mattie','Kansas'])))) for p in person] )

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

    # bv for tracking clues during explanation generation
    # bij_bv = [implies(bv, bi) for bv, bi  in zip(bv_bij, bij)]

    # model = Model(clues + bij_bv + trans)
    # return (bv_trans, bv_bij, bv_clues), (trans, bij_bv, clues), clues_text
    return clues


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
            bij += exactly_one(rel[:,col_ids])
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

    model = Model(allwishes)
    # print(model)
    return model


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
    rels=[is_old, lives_in, native, age_city, age_birth, city_birth]
    return bij, trans, clues, rels

def test_MSSes():
    cppy_model = frietKotProblem()
    cnf = cnf_to_pysat(cppy_model.constraints)
    frozen_cnf = [frozenset(c) for c in cnf]
    seq = omusExplain(frozen_cnf, weights=[len(c) for c in cnf], parameters=parameters, incremental=True)


def explain_origin(parameters={'extension': 'greedy_no_param','output': 'log.json'}, 
                   incremental=True, 
                   reuse_mss=True):

    from datetime import date, datetime

    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    # model constraints
    bij, trans, clues, rels = originProblem()
    clues_cnf = cnf_to_pysat(to_cnf(clues))
    bij_cnf = cnf_to_pysat(to_cnf(bij))
    trans_cnf = cnf_to_pysat(to_cnf(trans))
    cnf = [frozenset(c) for c in clues_cnf + bij_cnf + trans_cnf]
    weights = [20 for clause in clues_cnf] + \
              [1 for clause in trans_cnf] + \
              [1 for clause in bij_cnf]

    o, expl_seq = omusExplain(cnf, weights=weights, rels=rels, parameters=parameters, incremental=True, reuse_mss=True)
    o.export_results('results/puzzles/origin/', today + "_" + now + ".json")

def explain_frietkot(parameters={'extension': 'greedy_no_param','output': 'log.json'}, 
                   incremental=True, 
                   reuse_mss=True):
    from datetime import date, datetime

    today = date.today().strftime("%Y_%m_%d")
    now = datetime.now().strftime("%H_%M_%S")

    # explain
    cppy_model = frietKotProblem()
    cnf = cnf_to_pysat(cppy_model.constraints)
    frozen_cnf = [frozenset(c) for c in cnf]
    o, expl_seq = omusExplain(frozen_cnf, weights=[len(c) for c in cnf], parameters=parameters, incremental=incremental, reuse_mss=reuse_mss)
    o.export_results('results/puzzles/frietkot/', today + "_" + now + ".json")

if __name__ == "__main__":
    explain_frietkot()