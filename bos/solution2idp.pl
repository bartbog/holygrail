:- module(solution2idp, [
              solution2idp/3
          ]).

:- use_module(drs2fol, [drs2fol/2]).
:- use_module(printFol, [printFol/2]).
:- use_module(types, [
                  nameTypes/1,
                  resolveMissingTypes/2,
                  combineTypesToMatrix/4
              ]).
:- use_module(typeExtraction, [
                  getPredicates/2,
                  getBaseTypes/4,
                  getDerivedTypes/3
              ]).
:- use_module(questions, [
                  setQuestionTopic/1,
                  clearQuestionTopic/0
              ]).
:- use_module(printTable, [printTable/1]).

solution2idp(solution(Sentences, DRSs, TypesIn), ProblemName, Problem) :-
    setQuestionTopic(ProblemName),
    Problem = problem(NbBaseTypes, NbConceptsPerType, _, _),
    writeln(TypesIn),
    combineTypesToMatrix(TypesIn, NbBaseTypes, NbConceptsPerType, TypesMatrix),
    nameTypes(TypesMatrix),
    resolveMissingTypes(TypesMatrix, Types),
    maplist(drs2fol, DRSs, FOLs),
    pairs_keys_values(SentencePairs, Sentences, FOLs),
    nameTypes(Types),
    nameVariables(FOLs),
    getPredicates(Types, Predicates),
    getBaseTypes(Types, BaseTypes, NbBaseTypes, NbConceptsPerType),
    getDerivedTypes(Types, BaseTypes, DerivedTypes),
    \+ \+ printFile(ProblemName, SentencePairs, voc(BaseTypes, DerivedTypes, Predicates)),
    clearQuestionTopic,
    problemToFileName(ProblemName, FileName),
    format(string(Command), "cat ~p | docker run -i --rm --name idp -v $(pwd)/output:/root/idp krrkul/idp3:latest idp", [FileName]),
    process_create(path(sh), ["-c", Command], []).

handleIDPOutput(models(0, [])) :-
    format("Couldn't find any models. Something went wrong~n", []),
    fail.
handleIDPOutput(models(1, [Model])) :-
    !,
    format("Succes! Solution: ~n", []),
    printModel(Model).
handleIDPOutput(models(N, Models)) :-
    N > 1,
    format("Found too many models. Something went wrong~n", []),
    maplist(printModel, Models),
    fail.
printModel(model(_, Groups)) :-
    sortGroups(Groups, Sorted),
    printTable(Sorted).

sortGroups([Row | Rows], Sorted) :-
    nth1(I, Row, X),
    number(X),
    !,
    predsort(sortByColumn(I), [Row | Rows], Sorted).
sortByColumn(I, Delta, R1, R2) :-
    nth1(I, R1, X1),
    nth1(I, R2, X2),
    compare(Delta, X1, X2).

printFile(ProblemName, SentencePairs, Vocabularium) :-
    problemToFileName(ProblemName, FileName),
    tell(FileName),
    write('// Problem '),
    writeln(ProblemName),
    nl,
    printVocabulary(Vocabularium),
    nl,
    printExtraVocabulary(Vocabularium),
    nl,
    printStructure(),
    nl,
    printTheory(SentencePairs, Vocabularium),
    nl,
    printForceSomethingWrongValueTheory(Vocabularium),
    nl,
    printProcedureDiff(Vocabularium),
    nl,
    printProcedureGetPredList(Vocabularium),
    nl,
    printMain(SentencePairs),
    nl,
    told.
problemToFileName(ProblemName, FileName) :-
    atom_concat('output/', ProblemName, Temp1),
    atom_concat(Temp1, '.idp', FileName).

printVocabulary(voc(BaseTypes, DerivedTypes, Predicates)) :-
    writeln('vocabulary V {'),
    maplist(printType, BaseTypes),
    maplist(printType, DerivedTypes),
    nl,
    maplist(printPredicate, Predicates),
    writeln('}').
printType(baseType(Type, constructed:List)) :-
    !,
    atomic_list_concat(List, ', ', ListString),
    format('    type ~p constructed from {~w}~n', [Type, ListString]).
printType(baseType(Type, fakeConstructed:List)) :-
    !,
    printType(baseType(Type, constructed:List)).
printType(baseType(Type, int)) :-
    !,
    format('    type ~p isa int~n', [Type]).
printType(baseType(Type, int:Range)) :-
    !,
    atomic_list_concat(Range, '; ', RangeString),
    format('    type ~p = {~w} isa int~n', [Type, RangeString]).
printType(baseType(Type, X)) :-
    !,
    format('    type ~p //~p~n', [Type, X]).
printType(derivedType(Type, BaseType, int:Range)) :-
    !,
    atomic_list_concat(Range, '; ', RangeString),
    format('    type ~p = {~w} isa int // differences between values of type ~p~n', [Type, RangeString, BaseType]).
printPredicate(predicate(Name, Type1, Type2)) :-
    format('    ~p(~p, ~p)~n', [Name, Type1, Type2]).

printExtraVocabulary(voc(_BaseTypes, _DerivedTypes, Predicates)) :-
    writeln('vocabulary VExtra {'),
    writeln('    extern vocabulary V'),
    maplist(printExtraPredicate, Predicates),
    writeln('}').
printExtraPredicate(predicate(Name, Type1, Type2)) :-
    format('    ct_~p(~p, ~p)~n', [Name, Type1, Type2]),
    format('    cf_~p(~p, ~p)~n', [Name, Type1, Type2]).

printStructure() :-
    writeln('structure S : V {'),
    writeln('}').

printTheory(SentencePairs, voc(BaseTypes, _, Predicates)) :-
    maplist(printSentenceTheory(SentencePairs), SentencePairs),
    writeln('theory bijections : V {'),
    format('    // Logigram bijection axioms:~n'),
    maplist(printLogigramAxiomsForPredicate, Predicates),
    format('    // Logigram synonym axioms:~n'),
    printSynonymAxioms(Predicates),
    nl,
    format('    // Logigram transitive relation axioms:~n'),
    printTransitiveRelationAxioms(Predicates),
    nl,
    format('    // Logigram reflexive relation axioms:~n'),
    printReflexiveRelationAxioms(Predicates),
    nl,
    format('    // Logigram symmetry breaking axioms:~n'),
    include(=(baseType(_, fakeConstructed:_)), BaseTypes, FakeConstructedTypes),
    maplist(printSymmetryBreakersFakeConstructedTypes(Predicates, BaseTypes), FakeConstructedTypes),
    writeln('}').
printSentenceTheory(SentencePairs, Sentence-FOL) :-
    nth1(Index, SentencePairs, Sentence-FOL),
    format('theory T~d: V {~n    // ~w~n    ~@}~n~n',[Index, Sentence, printFol(idp, FOL)]).
printLogigramAxiomsForPredicate(predicate(Name, Type1, Type2)) :-
    format('    ! x [~p]: ?=1 y [~p]: ~p(x, y).~n', [Type1, Type2, Name]),
    format('    ! x [~p]: ?=1 y [~p]: ~p(y, x).~n~n', [Type2, Type1, Name]).
printSynonymAxioms([]).
printSynonymAxioms([predicate(Name, Type1, Type2) | Preds]) :-
    include(=(predicate(_, Type1, Type2)), Preds, Synonyms),
    maplist(printSynonymAxioms(predicate(Name, Type1, Type2)), Synonyms),
    printSynonymAxioms(Preds).
printSynonymAxioms(predicate(Name1, Type1, Type2), predicate(Name2, Type1, Type2)) :-
    format('    ! x [~p] y [~p]: ~p(x, y) <=> ~p(x, y).~n', [Type1, Type2, Name1, Name2]).
printTransitiveRelationAxioms([]).
printTransitiveRelationAxioms([Predicate | Preds]) :-
    printTransitiveRelationAxioms(Predicate, Preds),
    printTransitiveRelationAxioms(Preds).
printTransitiveRelationAxioms(predicate(Name1, Type1, Type2), Preds) :-
    member(predicate(Name2, Type1, Type3), Preds),
    member(predicate(Name3, Type2, Type3), Preds),
    format('    ! x [~p] y [~p]: ~p(x, y) <=> ? z [~p]: ~p(x, z) & ~p(y, z).~n', [Type1, Type2, Name1, Type3, Name2, Name3]),
    fail.
printTransitiveRelationAxioms(predicate(Name1, Type1, Type2), Preds) :-
    member(predicate(Name2, Type3, Type1), Preds),
    member(predicate(Name3, Type3, Type2), Preds),
    format('    ! x [~p] y [~p]: ~p(x, y) <=> ? z [~p]: ~p(z, x) & ~p(z, y).~n', [Type1, Type2, Name1, Type3, Name2, Name3]),
    fail.
printTransitiveRelationAxioms(_, _).
printReflexiveRelationAxioms([]).
printReflexiveRelationAxioms([Predicate | Preds]) :-
    printReflexiveRelationAxioms(Predicate, Preds),
    printReflexiveRelationAxioms(Preds).
printReflexiveRelationAxioms(predicate(Name1, Type1, Type2), Preds) :-
    member(predicate(Name2, Type2, Type1), Preds),
    format('    ! x [~p] y [~p]: ~p(x, y) <=> ~p(y, x).~n', [Type1, Type2, Name1, Name2]),
    fail.
printReflexiveRelationAxioms(_, _).
printSymmetryBreakersFakeConstructedTypes(Predicates, BaseTypes, baseType(FakeConstructedType, fakeConstructed:DomainFake)) :-
    member(predicate(Name, FakeConstructedType, Type1), Predicates),
    member(baseType(Type1, _:DomainReal), BaseTypes),
    maplist(printPredicateFact(Name), DomainFake, DomainReal).
printPredicateFact(Name, Arg1, Arg2) :-
    format('    ~p(~p, ~p).~n', [Name, Arg1, Arg2]).

printForceSomethingWrongValueTheory(voc(_BaseTypes, _DerivedTypes, Predicates)) :-
    writeln('theory forceSomethingWrongValue : VExtra {'),
    writeln('    ~('),
    maplist(printForceSomethingWrongPredicate, Predicates),
    writeln('        true'),
    writeln('    ).'),
    writeln('}').
printForceSomethingWrongPredicate(predicate(Name, Type1, Type2)) :-
  format('        (! x [~p] y [~p]: ct_~p(x,y) => ~p(x,y)) &~n', [Type1, Type2, Name, Name]),
  format('        (! x [~p] y [~p]: cf_~p(x,y) => ~~~p(x,y)) &~n', [Type1, Type2, Name, Name]).

printProcedureDiff(voc(_BaseTypes, _DerivedTypes, Predicates)) :-
    writeln('procedure diff(S1, S2) {'),
    writeln('    S3 = clone(S1)'),
    maplist(printProcedureDiffPredicate, Predicates),
    writeln('    return S3'),
    writeln('}').
printProcedureDiffPredicate(predicate(Name, _Type1, _Type2)) :-
    format('    removeFrom(S3[V::~p], S2[V::~p].ct)~n', [Name, Name]),
    format('    removeFrom(S3[V::~p], S2[V::~p].cf)~n', [Name, Name]).

printProcedureGetPredList(voc(_BaseTypes, _DerivedTypes, Predicates)) :-
    writeln('procedure getpredlist() {'),
    writeln('    return {'),
    maplist(printProcedureGetPredListPredicate, Predicates),
    writeln('    }'),
    writeln('}').
printProcedureGetPredListPredicate(predicate(Name, _Type1, _Type2)) :-
    format('        {V::~p, VExtra::ct_~p, VExtra::cf_~p},~n', [Name, Name, Name]).

printMain(SentencePairs) :-
    writeln('include "./generic_procedures.idp"'),
    nl,
    writeln('procedure main() {'),
    writeln('    stdoptions.cpsupport = false'),
    nl,
    writeln('    theories = {'),
    maplist(printMainTheoriesDict(SentencePairs), SentencePairs),
    writeln('    }'),
    nl,
    writeln('    test(theories,S)'),
    writeln('    S = explanationLoop(theories,S,true,theories)'),
    nl,
    writeln('    print("The final result is:")'),
    writeln('    print(S)'),
    writeln('    exit(0)'),
    writeln('}').
printMainTheoriesDict(SentencePairs, Sentence-FOL) :-
    nth1(Index, SentencePairs, Sentence-FOL),
    % format('theory T~d: V {~n    // ~w~n    ~@}~n~n',[Index, Sentence, printFol(idp, FOL)]).
    format('        {T~d, "~w"},~n', [Index, Sentence]).


nameVariables(FOL) :-
    term_variables(FOL, Vars),
    nameVariables(Vars, 0).
nameVariables([], _).
nameVariables([Var | Vars], Code) :-
    Code1 is Code + 1,
    codeToAtom(Code, Var),
    nameVariables(Vars, Code1).

codeToAtom(Code, Atom) :-
    Code < 26,
    !,
    C is Code + 97,
    atom_codes(Atom, [C]).
codeToAtom(Code, Atom) :-
    Code < 26*26,
    !,
    C1 is Code // 26 + 96,
    C2 is (Code mod 26) + 97,
    atom_codes(Atom, [C1, C2]).


