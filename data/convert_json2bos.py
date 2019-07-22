#!/usr/bin/env python3
# convert json file to BOS prolog input
#
# be sure to install 'python3-nltk'
# then run once: import nltk; nltk.download('punkt'); nltk.download('averaged_perceptron_tagger')

import sys
import json
import os.path
import nltk

def convert(fname):
    with open(fname, 'r') as ffile:
        data = json.load(ffile)

        name = data['title'].lower()
        nr_types = len(data['types'])
        nr_domsize = len( next(iter(data['types'].values())) ) # any element
        print("problem({}, problem({}, {}, {}, {}))".format(
                name,
                nr_types,
                nr_domsize,
                get_clues(data),
                get_grammar(data)))

def get_clues(data):
    # pretty printing stuff
    clues = ["        \"{}\"".format(clue) for clue in data['clues']]
    return "[\n"+",\n".join(clues)+"\n                     ]"

def get_grammar(data):
    # person names (no values)
    pns = []
    for (category, names) in data['types'].items():
        # TODO: add A/B/C/D... per type
        for n in names:
            if not isinstance(n, (int,float)):
                pns.append(n.lower())
    pns_str = ["    pn([{}])".format(pn) for pn in pns]

    # get all nouns from nltk
    #https://stackoverflow.com/questions/33587667/extracting-all-nouns-from-a-text-file-using-nltk
    # function to test if something is a noun
    # do the nlp stuff
    cluetext = " ".join(data['clues']).lower()
    tokenized = nltk.word_tokenize(cluetext)
    pos_tags = nltk.pos_tag(tokenized)
    # TODO: Fromt his, we can extract lots of things... like nouns
    print(pos_tags)
    def is_noun(pos): return pos[:2] == 'NN'
    nouns = [word for (word, pos) in pos_tags if is_noun(pos)]
    # remove the person names
    nouns = set(nouns) - frozenset(pns)
    nouns_str = ["    noun([{}])".format(noun) for noun in nouns]

    # collect what is needed:
    # prep()
    # ppn() # ?
    # tv() # ?
    # tvGap() # ?
    # tvPrep() # ?

    return "[\n"+\
           ",\n".join(pns_str)+"\n"+\
           ",\n".join(nouns_str)+\
           "\n                     ]"



if __name__ == "__main__":
    assert (len(sys.argv) == 2), "Expecting 1 argument: the json file"
    convert(sys.argv[1])
