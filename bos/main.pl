/*************************************************************************

     File: lambdaDRT.pl
     Copyright (C) 2004, 2006 Patrick Blackburn & Johan Bos

     This file is part of BB2, version 2.0 (November 2006).

     BB2 is free software; you can redistribute it and/or modify
     it under the terms of the GNU General Public License as published by
     the Free Software Foundation; either version 2 of the License, or
     (at your option) any later version.

     BB2 is distributed in the hope that it will be useful,
     but WITHOUT ANY WARRANTY; without even the implied warranty of
     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
     GNU General Public License for more details.

     You should have received a copy of the GNU General Public License
     along with BB2; if not, write to the Free Software Foundation, Inc.,
     59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

*************************************************************************/

:- module(main, [test/0,
                 testAll/1,
                 test/1,
                 test/3,
                 lambdaDRT/4,
                 infix/0,
                 prefix/0,
                 useLexicon/1,
                 solvep/1,
                 solveAll/0
                ]).

:- use_module(readLine, [readLine/1,
                        readFromString/2]).

:- use_module(comsemPredicates, [prefix/0,
                                 infix/0,
                                 printRepresentations/2]).

:- use_module(betaConversionDRT, [betaConvert/2]).
:- use_module(mergeDRT, [mergeDrs/2]).
simplify(X, Y) :-
    betaConvert(X, X1),
    mergeDrs(X1, Y).

:- use_module(types, [combineTypes/2, nameTypes/1, getRealBaseTypeCandidates/2]).
:- use_module(typesLexicon, [lexicalTypes/1]).

:- use_module(myGrammar, [s/3]).

:- use_module(problems, [problem/2]).
:- use_module(problemLexiconRules, [useLexicon/1]).

:- use_module(drs2fol, [drs2fol/2]).
:- use_module(printFol, [printFol/1]).

:- use_module(solution2idp, [solution2idp/3]).
:- use_module(typeExtraction, [getBaseTypeAtoms/2]).

/*========================================================================
    Driver Predicates
========================================================================*/

test :-
    testAll([
                   tias, p1,
                   p2
             ]).

% Test the list of problems
% fails if any one of the problems fails
testAll(Problems) :-
    maplist(testp, Problems, Resultss, _),
    format('~n~n~nResults (number of meanings per sentence and for the whole puzzle):~n###################################################################~n'),
    maplist(printResults, Resultss, _),
    \+ (
        member([_, _, X], Resultss),
        X \= 1
    ).

printResults(Results, _Types) :-
    format('Problem ~p: ~p --> ~p~n', Results).
    %% typesToSetOfVariables(Types, FixedTypes, TypesPerVariable),
    %% writeln(FixedTypes),
    %% maplist(writeln, TypesPerVariable),
    %% nl.

typesToSetOfVariables(Types, FixedTypes, TypesPerVariable) :-
    combineTypes(Types, CombinedTypes),
    findall(Bag, (
                group_by(Var, X, (
                             maplist(term_variables, CombinedTypes, Vars),
                             pairs_keys_values(Pairs, CombinedTypes, Vars),
                             numbervars(CombinedTypes, 0, End),
                             between(0, End, VarNb),
                             Var =.. ['$VAR', VarNb],
                             member(X-XVars, Pairs),
                             member(Var, XVars)
                         ), Bag)
            ), TypesPerVariable),
    findall(X, (
                member(X, CombinedTypes),
                term_variables(X, [])
            ), FixedTypes).

solveAll :-
    maplist(solvep, [tias, p1, p1b, p2, p3, p4, p5, p6, p7b, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20]).
solvep(ProblemName) :-
    testp(ProblemName, _, Sols),
    Sols = [Solution],
    nl,
    problem(ProblemName, Problem),
    solution2idp(Solution, ProblemName, Problem).

testp(ProblemName, [ProblemName, NbDRSes, NbResults], Solutions) :-
    problem(ProblemName, Problem),
    Problem = problem(_, _, Sentences, Lexicon),
    useLexicon(Lexicon),
    format('~n###############################~n###   ~p~n###############################~n', [ProblemName]),
    maplist(testSentence, Sentences, NbDRSes, Results),
    nl,
    filterResults(Problem, Results, NewResults),
    length(NewResults, NbResults),
    maplist(pairs_keys_values, NewResults, NewDRSss, Types),
    maplist(toSolution(Problem), NewDRSss, Types, Solutions),
    nl, print(NbDRSes),
    format('~nNumber of possible meanings in total: ~p~n', [NbResults]),
    %% maplist(toFol(Sentences), Types, NewDRSss),
    true.

filterResults(problem(_NbBaseTypes, _, _, _), Results, NewResults) :-
    findall(PossibleResult, (
                maplist(memberIfMultiple, PossibleResult, Results),
                pairs_keys_values(PossibleResult, _DRSs, Types),
                flatten(Types, FlattenTypes),
                combineTypes(FlattenTypes, CombinedTypes),
                \+ (
                    member(attr(TypeX, countable), CombinedTypes),
                    member(attr(TypeY, qualified), CombinedTypes),
                    TypeX == TypeY
                )
                %% pairs_keys_values(PossibleResult, _DRSs, Types),
                %% flatten(Types, FlattenTypes),
                %% combineTypes(FlattenTypes, NewTypes)
                %% \+ endoPredicateType(NewTypes),
                %% \+ \+ (
                %%     nameTypes(NewTypes),
                %%     getBaseTypeAtoms(NewTypes, BaseTypes),
                %%     \+ (
                %%         member(attr(TypeX, countable), Types),
                %%         member(attr(TypeX, qualified), Types)
                %%     ),
                %%     nl,
                %%     writeln(NewTypes),
                %%     writeln(BaseTypes),
                %%     length(BaseTypes, NbBaseTypes)
                %% )
            ), NewResults).

endoPredicateType([type(_, pred(X, Y)) | _]) :-
    X == Y.
endoPredicateType([_ | Types]) :-
    endoPredicateType(Types).

toSolution(problem(_NbBaseTypes, _NbConceptsPerType, Sentences, _), DRSs, Types, solution(Sentences, DRSs, CombinedTypes)) :-
    flatten(Types, FlatTypes),
    combineTypes(FlatTypes, CombinedTypes),
    !.

toFol(Sentences, Types, DRSs) :-
    maplist(drs2fol, DRSs, FOLs),
    pairs_keys_values(Pairs, Sentences, FOLs),
    nl,
    flatten(Types, FlattenedTypes),
    \+ \+ (nameTypes(FlattenedTypes), numbervars(FlattenedTypes, 0, End), numbervars(FOLs, End, _), printTypes(FlattenedTypes), maplist(printSentence, Pairs)).

printTypes(Types) :-
    include(=(type(_, _)), Types, Types1),
    maplist(getType, Types1, RealTypes),
    list_to_set(RealTypes, AllTypes),
    maplist(getRepresentativeForType(Types), AllTypes, Representatives),
    pairs_keys_values(Pairs, AllTypes, Representatives),
    write('Types: '),
    print(Pairs),
    nl.
getType(type(_, Type), Type).
getRepresentativeForType([type(_-Var, Type) | _], Type, Var) :-
    !.
getRepresentativeForType([_ | Types], Type, Var) :-
    getRepresentativeForType(Types, Type, Var).
printSentence(Sentence-FOL) :-
    write('// '),
    writeln(Sentence),
    printFol(FOL).

memberIfMultiple(fail-[], []).
memberIfMultiple(H, [H|_]).
memberIfMultiple(X, [_|T]) :-
    member(X, T).

testSentence(Sentence, NbDRS, Results) :-
    format('~nSentence: ~p', [Sentence]),
    test(Sentence, DRSs, Types),
    pairs_keys_values(Results, DRSs, Types),
    length(DRSs, NbDRS).

test(String) :-
    test(String, _, _).
test(String, DRSs, Types) :-
    readFromString(String, Discourse),
    lambdaDRT(Discourse, drs([], []), DRSs, Types),
    printRepresentations(DRSs, Types).

lambdaDRT(Discourse, Old, Sems, Types) :-
     lexicalTypes(LexicalTypes),
     b_setval(types, LexicalTypes),
     findall(Sem-Types, (
                     s([coord:no, sem:Drs], Discourse, []),
                     (
                         simplify(merge(Old, Drs), Sem)
                     ->
                         b_getval(types, Types1),
                         combineTypes(Types1, Types)
                     ;
                         nl, write('failed conversion: '),
                         numbervars(Drs, 0, _),
                         print(Drs),
                         fail
                     )
                  ), Sols),
     pairs_keys_values(Sols, Sems, Types).
