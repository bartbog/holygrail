:- module(problemLexiconRules, [
              lexEntry/2,
              useLexicon/1
          ]).

:- use_module(myLexicon, [lexEntry/2 as defaultLexicon]).
:- use_module(types, [addType/2, addTypeAttribute/2]).
:- use_module(typesLexicon, [addLexicalType/2]).

:- dynamic pLexEntry/2.

useLexicon(Rules) :-
    retractall(pLexEntry(_, _)),
    maplist(addRule, Rules).

lexEntry(X, Y) :-
    defaultLexicon(X, Y).
lexEntry(X, Y) :-
    pLexEntry(X, Y).

syntax_symbol(Syntax, Symbol) :-
    atomic_list_concat(Syntax, '_', Symbol).
symbol_syntax(Symbol, Syntax) :-
    split_string(Symbol, '_', '', L),
    maplist(atom_chars, Syntax, L).

/*========================================================================
    Rules
========================================================================*/
addRule(pn(Syntax)) :-
    syntax_symbol(Syntax, Symbol),
    assertz((pLexEntry(pn, [symbol:Symbol, syntax:Syntax, num:sg, vType:Type]) :- addType(pn-Symbol, Type), addTypeAttribute(Type, qualified))).
addRule(pn(Syntax, Type)) :-
    syntax_symbol(Syntax, Symbol),
    addLexicalType(pn-Symbol, Type),
    addRule(pn(Syntax)).
addRule(ppn(Syntax)) :-
    syntax_symbol(Syntax, Symbol),
    assertz((pLexEntry(pn, [symbol:Symbol, syntax:Syntax, num:_, vType:Type]) :- addType(pn-Symbol, Type), addTypeAttribute(Type, qualified))).
addRule(ppn(Syntax, Type)) :-
    syntax_symbol(Syntax, Symbol),
    addLexicalType(pn-Symbol, Type),
    addRule(ppn(Syntax)).
addRule(pnn(Syntax, Number)) :-
    syntax_symbol(Syntax, Symbol),
    assertz((pLexEntry(pn, [symbol:Number, syntax:Syntax, num:sg, vType:Type]) :- addType(pn-Symbol, Type), addTypeAttribute(Type, countable))).
addRule(noun(SyntaxSg, SyntaxPl)) :-
    syntax_symbol(SyntaxSg, Symbol),
    assertz(pLexEntry(noun, [symbol:Symbol, num:sg, syntax:SyntaxSg, vType:Type]) :- addType(noun-Symbol, Type)),
    assertz(pLexEntry(noun, [symbol:Symbol, num:pl, syntax:SyntaxPl, vType:Type]) :- addType(noun-Symbol, Type)).
addRule(tv(SyntaxSg, SyntaxInf)) :-
    syntax_symbol(SyntaxSg, Symbol),
    assertz(pLexEntry(tv, [symbol:Symbol, syntax:SyntaxSg, inf:fin, num:sg, vType:Type]) :- addType(tv-Symbol, Type)),
    assertz(pLexEntry(tv, [symbol:Symbol, syntax:SyntaxInf, inf:inf, num:sg, vType:Type]) :- addType(tv-Symbol, Type)).
addRule(tvPrep(SyntaxSg, PP, SyntaxInf, SyntaxPart)) :-
    %% Type = pred(SubjType, ObjType),
    append(SyntaxSg, PP, WordForm),
    syntax_symbol(WordForm, Symbol),
    assertz(pLexEntry(ivpp, [symbol:Symbol, syntax:SyntaxSg, pp:PP, inf:fin, num:sg, vType:Type]) :- addType(ivpp-Symbol, Type)),
    assertz(pLexEntry(ivpp, [symbol:Symbol, syntax:SyntaxInf, pp:PP, inf:inf, num:sg, vType:Type]) :- addType(ivpp-Symbol, Type)),
    assertz(pLexEntry(ivpp, [symbol:Symbol, syntax:SyntaxPart, pp:PP, inf:part, num:sg, vType:Type]) :- addType(ivpp-Symbol, Type)).
    %% assertz(pLexEntry(prep, [symbol:Symbol, syntax:PP, type:v, vType:pred(SubjType, ObjType)])).
addRule(tvGap(SyntaxSg, Gap, SyntaxInf)) :-
    append(SyntaxSg, Gap, WordForm),
    syntax_symbol(WordForm, Symbol),
    assertz(pLexEntry(tvgap, [symbol:Symbol, syntax:SyntaxSg, gap:Gap, inf:fin, num:sg, vType:Type]) :- addType(tvgap-Symbol, Type)),
    assertz(pLexEntry(tvgap, [symbol:Symbol, syntax:SyntaxInf, gap:Gap, inf:inf, num:sg, vType:Type]) :- addType(tvgap-Symbol, Type)).
addRule(copGap(Syntax, Gap)) :-
    append([is], Syntax, SyntaxSg),
    append(SyntaxSg, Gap, WordForm),
    syntax_symbol(WordForm, Symbol),
    assertz(pLexEntry(copgap, [symbol:Symbol, syntax:Syntax, gap:Gap, vType:Type]) :- addType(copgap-Symbol, Type)).
addRule(prep(Syntax)) :-
    syntax_symbol(Syntax, Symbol),
    assertz(pLexEntry(prep, [symbol:Symbol, syntax:Syntax, type:n, vType:Type]) :- addType(prep-Symbol, Type)).
addRule(comp(Type, Syntax)) :-
    assertz(pLexEntry(comp, [type:Type, syntax:Syntax])).
