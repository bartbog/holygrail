#!/usr/bin/env python3
# convert json file to BOS prolog input
#
# be sure to install 'python3-nltk'
# and run: 'pip3 install pattern'
# then run once: import nltk; nltk.download('punkt'); nltk.download('averaged_perceptron_tagger')

import sys
import json
import os.path
import nltk
from pattern.en import pluralize, singularize

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
    pns = set()
    for (category, names) in data['types'].items():
        for n in names:
            if not isinstance(n, (int,float)):
                pns.add(n.lower())
    # TODO, what with those that are 'ppn'?

    # do the nlp stuff
    # http://www.nltk.org/book/ch07.html
    clues_token = [nltk.word_tokenize(clue) for clue in data['clues']]
    clues_pos = [nltk.pos_tag(clue) for clue in clues_token]

    # check for double meanings
    poscounts = nltk.ConditionalFreqDist([tag for tags in clues_pos for tag in tags])
    poscounts_ambigu = [(x,poscounts[x]) for x in poscounts if len(poscounts[x]) > 1]
    print("Ambiguous:",poscounts_ambigu)

    # extra nouns that are not our proper nouns
    nouns_tuple = set()
    for clue_pos in clues_pos:
        for (word, pos) in clue_pos:
            if word in pns:
                continue # skip
            if pos.startswith('NNS'):
                # plural
                nouns_tuple.add( (singularize(word),word) )
            elif pos.startswith('NN'):
                # singular
                nouns_tuple.add( (word,pluralize(word)) )
        
    # collect what is needed:
    # prep()
    # ppn() # ?
    # tv() # ?
    # tvGap() # ?
    # tvPrep() # ?
    pns_str = ["    pn([{}])".format(pn) for pn in pns]
    nouns_str = ["    noun([{},{}])".format(s,p) for (s,p) in nouns_tuple]

    return "[\n"+\
           ",\n".join(pns_str)+"\n"+\
           ",\n".join(nouns_str)+\
           "\n                     ]"



if __name__ == "__main__":
    assert (len(sys.argv) == 2), "Expecting 1 argument: the json file"
    convert(sys.argv[1])
