#!/usr/bin/env python3
# convert json file to BOS prolog input
#
# be sure to install 'python3-nltk'
# and run: 'pip3 install pattern'
# then run once: import nltk; nltk.download('punkt'); nltk.download('averaged_perceptron_tagger'); nltk.download('wordnet')

import sys
import json
import os.path
import nltk
import string
import glob
from pattern.en import pluralize, singularize, lemma
from nltk.corpus import wordnet as wn

def convert(fname):
    with open(fname, 'r') as ffile:
        data = json.load(ffile)

        name = data['title'].lower()
        nr_types = len(data['types'])
        nr_domsize = len( next(iter(data['types'].values())) ) # any element

        (clues, lexicon) = get_lexicon(data)
        return "problem({}, problem({}, {}, {}, {})).".format(
                name,
                nr_types,
                nr_domsize,
                pp_clues(clues),
                lexicon)

def pp_clues(clues):
    # pretty printing stuff
    clues = ["        \"{}\"".format(clue) for clue in clues]
    return "[\n"+",\n".join(clues)+"\n                     ]"

def get_lexicon(data):
    # proper nouns (no numbers)
    pns = set()
    nns = set() # numeric ones
    for (category, names) in data['types'].items():
        for n in names:
            if isinstance(n, (int,float)):
                nns.add(n)
            else:
                pns.add(n.lower())
    # ppns are discoved below

    # do the nlp stuff
    # http://www.nltk.org/book/ch07.html
    clues_token = [nltk.word_tokenize(clue) for clue in data['clues']]
    
    # remove symbols (why?)
    punctuations = frozenset(string.punctuation)
    clues_token_clean = []
    for clue in clues_token:
        clues_token_clean.append([i for i in clue if i not in punctuations])
    clues_pos = [nltk.pos_tag(clue) for clue in clues_token_clean]

    # cleaning: make numbers integer
    for clue_pos in clues_pos:
        for (i,(word, pos)) in enumerate(clue_pos):
            # CD (cardinal number) -- remove comma or dot
            if pos == 'CD':
                # this may not be sufficiently robust with fractional numbers (e.g, 0.9 vs 0.90)
                word = word.replace(".","")
                word = word.replace(",","")
                if word in nns:
                    # tag it a NNN if in the names list (numeric)
                    clue_pos[i] = (word, 'NNN')
                else:
                    clue_pos[i] = (word, pos)

    # check for ppn's
    # extract [DT pn NN] triples
    pn_triples = dict((pn,[]) for pn in pns)
    for clue_pos in clues_pos:
        for (i,(word, pos)) in enumerate(clue_pos):
            word = word.lower()
            if word in pns:
                if not pos.startswith('NN'):
                    # make sure it is correctly tagged
                    clue_pos[i] = (word, 'NN')
                # check for triple
                if i > 0 and clue_pos[i-1][1] == 'DT' \
                and i+1 < len(clue_pos) and clue_pos[i+1][1] == 'NN':
                    pn_triples[word].append( (clue_pos[i-1][0],clue_pos[i+1][0]) )
    # check for each type, use most common triple
    ppns = set() # XXX deprecated, remove later
    ppns_dict = dict() # pn -> triple
    for (category, names) in data['types'].items():
        triples = []
        for name in names:
            if not isinstance(name, (int,float)):
                name = name.lower()
                if name in pn_triples:
                    triples += pn_triples[name]
        if len(triples) > 0:
            firstdist = nltk.FreqDist([phrase[0] for phrase in triples])
            lastdist = nltk.FreqDist([phrase[-1] for phrase in triples])
            for name in names:
                ppns.add( (firstdist.max(),name.lower(),lastdist.max()) ) # XXX depr
                ppns_dict[name.lower()] = (firstdist.max(),name.lower(),lastdist.max())
    # fix the less common triple ppn usages in the clues...
    j = 0 # old style because we will restart for j
    while j < len(clues_pos):
        clue_pos = clues_pos[j]
        for (i,(word, pos)) in enumerate(clue_pos):
            if word in ppns_dict:
                triple = ppns_dict[word]
                start = i-1 # standard case
                stop = i+1 # standard case
                if clue_pos[start][0] == triple[0] and clue_pos[stop][0] == triple[2]:
                    continue # all good
                # special case: -1 is not a DT, but -2 is
                if start-1 >= 0 and clue_pos[start][1] != 'DT' and clue_pos[start-1][1] == 'DT':
                    start = i-2
                # special case: +1 is not the 3-NN, but +2 is
                if stop+1 < len(clue_pos) and clue_pos[stop][0] != triple[2] and clue_pos[stop+1][0] == triple[2]:
                    stop = i+2
                triple_pos = [ (triple[0], 'DT'), (triple[1], 'NN'), (triple[2], 'NN') ]
                clues_pos[j] = clue_pos[:start] + triple_pos + clue_pos[stop+1:]
                j = j - 1 # restart j
        j = j + 1

    # check for double meanings
    #poscounts = nltk.ConditionalFreqDist([tag for tags in clues_pos for tag in tags])
    #poscounts_ambigu = [(x,poscounts[x]) for x in poscounts if len(poscounts[x]) > 1]
    #print("Ambiguous:",poscounts_ambigu)

    # extra nouns that are not our proper nouns
    nouns_tuple = set()
    for clue_pos in clues_pos:
        for (word, pos) in clue_pos:
            word = word.lower()
            if word in pns:
                continue # skip
            if pos.startswith('NNS'):
                # plural
                nouns_tuple.add( (singularize(word),word) )
            elif pos.startswith('NN'):
                # singular
                nouns_tuple.add( (word,pluralize(word)) )

    # verbs WORK IN PROGRESS
    #tv_set = set()
    #tvprep_set = set()
    #for clue_pos in clues_pos:
    #    for (i,(word, pos)) in enumerate(clue_pos):
    #        if pos.startswith('VB'):
    #            # tvprep: verb with preposition
    #            if i+1 < len(clue_pos) and clue_pos[i+1][1] == 'IN':
    #                tvprep_set.add( (word, clue_pos[i+1][0], lemma(word)) )
    #            # tv: transitive verb
    #            if i+1 < len(clue_pos) and clue_pos[i+1][1] == 'VBN':
    #                # tv-2-sized, e.g. 'was prescribed'
    #                word2 = clue_pos[i+1][0]
    #                tv_set.add( ((word,word2), lemma(word2)) )
    #            if pos == 'VBN' and i > 0 and clue_pos[i-1][1].startswith('VB'):
    #                # previous was also a verb, so this one already used as tv-2-sized
    #                continue
    #            tv_set.add( (word, lemma(word)) )
    #print("tv",tv_set)
    #print("tvprep",tvprep_set)


    # https://stackoverflow.com/questions/28033882/determining-whether-a-word-is-a-noun-or-not
    # this is really slow and due to an insufficient POS tagger...
    verbs = frozenset(x.name().split('.', 1)[0] for x in wn.all_synsets('v'))
    
    verbs_with_prep = set()
    tr_verbs = set()
    two_word_tr_verbs = set()
    for clue_pos in clues_pos:
        for (i,(word, pos)) in enumerate(clue_pos):
            word = word.lower()
            # verbs with preposition
            if lemma(word) in verbs and i < len(clue_pos)-1 \
            and clue_pos[i+1][1] == 'IN': # lemma() converts verb to base form
                verbs_with_prep.add( (clue_pos[i][0], clue_pos[i+1][0], lemma(clue_pos[i][0])) )
            # tr verbs
            if lemma(word) in verbs \
               and lemma(clue_pos[i-1][0]) not in verbs \
               and i < len(clue_pos)-2 \
               and ( clue_pos[i+1][1] == "CD" or clue_pos[i+1][0] in pns or clue_pos[i+2][0] in pns ):
                if clue_pos[i+1][1] != 'VBN':
                    tr_verbs.add( (word, lemma(word)) )
                else:
                    two_word_tr_verbs.add( (word, clue_pos[i+1][0], lemma(clue_pos[i+1][0])) )
                    
    clues_revised = []
    for clues in clues_pos:
        target = []
        for i,item in enumerate(clues):# enumerate(nltk.pos_tag(clues_token_clean[6])):
            word = item[0].lower()

            # noun
            if word in pns:
                target.append( (word, 'pn') )
            elif word in flatten(nouns_tuple) and word not in flatten(ppns):
                target.append( (word, 'noun') )
            elif word in flatten(nouns_tuple) and word in flatten(ppns):
                if target[-2][1] == 'DT':
                    for ppn in ppns:
                        if target[-1][0] in ppn:
                            del target[-2:]
                            target.append( (ppn, 'ppn') )
                            break
                elif target[-3][1] == 'DT':
                    for ppn in ppns:
                        if target[-1][0] in ppn or target[-2][0] in ppn:
                            del target[-3:]
                            target.append( (ppn, 'ppn') )
                            break
            # verb
            elif lemma(word) in verbs or item[1].startswith('VB'):
                if target[-1][1].startswith('VB'):
                    target.append( ((target[-1][0], word), 'tv') )
                    del target[-2]
                elif word in tr_verbs:
                    target.append( (word, 'tv') )
                else:
                    target.append(item)

            # prep
            elif item[1] == 'IN' and i > 1:
                if target[-1][1].startswith('VB') or lemma(target[-1][0]) in verbs:
                    target.append( ((target[-1][0], word), 'tvPrep') )
                    del target[-2]
                else:
                    target.append(item)

            else:
                target.append(item)    
                
        clues_revised.append(target)
    #print("\n".join(map(str,clues_revised)))

    # reconstruct sentences from revised clues
    clues_new = []
    for clue in clues_revised:
        clue_str = ""
        for (word, tag) in clue:
            if isinstance(word, (list,tuple)):
                # multiple words
                clue_str += " ".join(word)
            else:
                clue_str += word
            clue_str += " "
        clues_new.append(clue_str)
    #print(clues_new)
    
    # finding tvGap
    tvgap_phrases = []
    for clues in clues_revised:
        for i,item in enumerate(clues):
            if item[-1].startswith('tv') and (clues[i+1][-1] == 'pn' or clues[i+1][-1] == 'ppn'):
                if clues[i+2:]: # rest of the phrase is not empty, add it
                    # TODO: check for punctuation or conjunction or other end of subsentence?
                    tvgap_phrases.append( [item] + clues[i+2:] )
    
    # dictionary to find phrase frequency
    cnt = {}
    for tvgap in tvgap_phrases:
        t = tuple(tvgap) # for dict
        if t in cnt:
            cnt[t] +=1
        else:
            cnt[t] = 1 
            
    tvGap_list = []
    for tvgap,val in cnt.items():
        # tvgap = [ (words, "TV"), (rest, tag), (of, tag), ([multi,part,sentence],tag) ]
        if val>1:
            tv = tvgap[0][0]
            gapwords = []
            for item in tvgap[1:]:
                for word in item[:-1]:
                    gapwords.append(word)
            # find current tv and its lemma, remove from tv
            thelemma = "noooone"
            for (v,v2) in list(tr_verbs):
                if v == tv:
                    thelemma = v2
                    tr_verbs.remove( (v,v2) )
            for (v,v2,v3) in list(two_word_tr_verbs):
                if (v,v2) == tv:
                    thelemma = v3
                    two_word_tr_verbs.remove( (v,v2,v3) )
            tvGap_list.append( (tv,gapwords,thelemma) )
    
    # for printing, remove ppns from pns
    for (pre,pn,post) in ppns:
        pns.remove(pn)
    pns_str = ["    pn([{}])".format(pn) for pn in pns]
    nouns_str = ["    noun([{}], [{}])".format(s,p) for (s,p) in nouns_tuple]
    ppns_str = ["    ppn([{}, {}, {}])".format(a,b,c) for (a,b,c) in ppns]
    tv_str = ["    tv([{}], [{}])".format(v,v2) for (v,v2) in tr_verbs]
    tv_str_two = ["    tv([{}, {}], [{}])".format(v1,v2,v3) for (v1,v2,v3) in two_word_tr_verbs]
    tvprep_str = ["    tvPrep([{}], [{}], [{}], [todooo])".format(v,p,v2) for (v,p,v2) in verbs_with_prep]
    tvgap_str = []
    for (v,gap,v2) in tvGap_list:
        one = "[{}]".format(", ".join(v))
        two = "[{}]".format(", ".join(gap))
        mystr = "    tvGap({}, {}, [{}])".format(one, two, v2)
        tvgap_str.append(mystr)
            
    return (clues_new,
           "[\n"+\
           ",\n".join(pns_str + ppns_str + nouns_str + tv_str + tv_str_two + tvprep_str + tvgap_str)+\
           "\n                     ]")

# https://stackoverflow.com/questions/47432632/flatten-multi-dimensional-array-in-python-3
def flatten(something):
    if isinstance(something, (list, tuple, set, range)):
        for sub in something:
            yield from flatten(sub)
    else:
        yield something

if __name__ == "__main__":
    assert (len(sys.argv) == 2), "Expecting 1 argument: the json file"
    convert(sys.argv[1])
