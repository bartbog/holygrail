/*************************************************************************

   File: englishGrammar.pl
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

:- module(myGrammar, [s/3]).

:- use_module(comsemPredicates, [memberList/2]).
:- use_module(problemLexiconRules, [lexEntry/2]).
:- use_module(myLexiconSemantics, [semLex/2]).
:- use_module(myGrammarSemantics, [combine/2]).

:- use_module(types, [addType/2, addTypeAttribute/2]).

/*========================================================================
  Sentences
========================================================================*/

s([coord:no, sem:Sem]) -->
  np([coord:_, num:Num, gap:[], sem:NP, vType:SubjType]),
  vp([coord:_, inf:fin, num:Num, gap:[], sem:VP, vType:SubjType]),
  { combine(s:Sem, [np:NP, vp:VP]) }.

%% s([coord:no, sem:Sem]) -->
%%   [there, is],
%%   det([mood:decl, type:indef, num:sg, sem:Det, vType:Type]),
%%   n([coord:_, num:sg, sem:N, vType:Type]),
%%   { combine(s:Sem, [det:Det, n:N]) }.

%% s([coord:yes, sem:Sem]) -->
%%   s([coord:ant, sem:S1]),
%%   s([coord:con, sem:S2]),
%%   { combine(s:Sem, [s:S1, s:S2]) }.

%% s([coord:yes, sem:Sem]) -->
%%   s([coord:either, sem:S1]),
%%   s([coord:or, sem:S2]),
%%   { combine(s:Sem, [s:S1, s:S2]) }.

%% s([coord:ant, sem:Sem]) -->
%%   [if],
%%   s([coord:no, sem:S]),
%%   { combine(s:Sem, [if:S]) }.

%% s([coord:either, sem:Sem]) -->
%%   [either],
%%   s([coord:no, sem:S]),
%%   { combine(s:Sem, [either:S]) }.

%% s([coord:con, sem:Sem]) -->
%%   [then],
%%   s([coord:no, sem:S]),
%%   { combine(s:Sem, [then:S]) }.

%% s([coord:con, sem:Sem]) -->
%%   s([coord:no, sem:S]),
%%   { combine(s:Sem, [then:S]) }.

%% s([coord:or, sem:Sem]) -->
%%   [or],
%%   s([coord:no, sem:S]),
%%   { combine(s:Sem, [or:S]) }.

%% s([coord:question, sem:Sem]) -->
%%   q([sem:Q]),
%%   { combine(s:Sem, [question:Q]) }.

%s([coord:C, sem:Sem]) -->
%  [it, is, not, the, case, that],
%  s([coord:C, sem:S]),
%  { combine(s:Sem, [not:S]) }.

s([coord:no, sem:Sem]) -->
  [of],
  np([coord:_, num:sg, gap:[], sem:NP1, vType:SubjType]),
  [and],
  np([coord:_, num:sg, gap:[], sem:NP2, vType:SubjType]),
  [one],
  vp([coord:no, inf:fin, num:sg, gap:[], sem:VP1, vType:SubjType]),
  [and, the, other],
  vp([coord:no, inf:fin, num:sg, gap:[], sem:VP2, vType:SubjType]),
  { combine(s:Sem, [np1:NP1, np2:NP2, vp1:VP1, vp2:VP2])}.

s([coord:no, sem:Sem]) -->
  [the],
  number([sem:_, vType:_]),
  n([coord:_, num:pl, sem:_, vType:Type]),
  cop([type:np, inf:fin, num:pl, sem:Cop]),
  np([coord:conj, num:_, gap:[], sem:NP, vType:Type]),
  { combine(s:Sem, [cop:Cop, np:NP, alldifferent])}.

%% sinv([gap:G, sem:S]) -->
%%   av([inf:fin, num:Num, sem:Sem]),
%%   np([coord:_, num:Num, gap:[], sem:NP, vType:SubjType]),
%%   vp([coord:_, inf:inf, num:Num, gap:G, sem:VP, vType:SubjType]),
%%   { combine(sinv:S, [av:Sem, np:NP, vp:VP]) }.

/*========================================================================
  Questions
========================================================================*/

%% q([sem:Sem]) -->
%%   whnp([num:Num, sem:NP, vType:Type]),
%%   vp([coord:_, inf:fin, num:Num, gap:[], sem:VP, vType:Type]),
%%   { combine(q:Sem, [whnp:NP, vp:VP]) }.

%% q([sem:Sem]) -->
%%   whnp([num:_, sem:NP, vType:Type]),
%%   sinv([gap:[np:NP-Type], sem:S]),
%%   { combine(q:Sem, [sinv:S]) }.


/*========================================================================
  Noun Phrases
========================================================================*/

npCoordNum(conj, pl).
npCoordNum(disj, sg).
npCoordNum(neg, sg).

%% np([coord:no, num:sg, gap:[np:NP-Type], sem:NP, vType:Type]) --> [].

np([coord:CoordType, num:CoordNum, gap:G, sem:NP, vType:Type]) -->
  { npCoordNum(CoordType, CoordNum) },
  coordPrefix([type:CoordType]),
  { Coord1 = no ; Coord1 = np },
  np([coord:Coord1, num:sg, gap:G, sem:NP1, vType:Type]),
  noCoord([type:CoordType, sem:C]),
  np([coord:CoordType, num:_, gap:G, sem:NP2, vType:Type]),
  { combine(np:NP, [np:NP1, coord:C, np:NP2]) }.
np([coord:CoordType, num:CoordNum, gap:G, sem:NP, vType:Type]) -->
  { npCoordNum(CoordType, CoordNum) },
  coordPrefix([type:CoordType]),
  { Coord1 = no ; Coord1 = np ; Coord1 = comp },
  np([coord:Coord1, num:sg, gap:G, sem:NP1, vType:Type]),
  coord([type:CoordType, sem:C]),
  { member(Coord, [CoordType, no, np, comp]) },
  np([coord:Coord, num:_, gap:G, sem:NP2, vType:Type]),
  { combine(np:NP, [np:NP1, coord:C, np:NP2]) }.

%% np([coord:conj, num:pl, gap:G, sem:NP, vType:Type]) -->
%%   np([coord:no, num:sg, gap:G, sem:NP1, vType:Type]),
%%   noCoord([type:conj, sem:C]),
%%   np([coord:conj, num:_, gap:G, sem:NP2, vType:Type]),
%%   { combine(np:NP, [np:NP1, coord:C, np:NP2]) }.
%% np([coord:conj, num:pl, gap:G, sem:NP, vType:Type]) -->
%%   np([coord:no, num:sg, gap:G, sem:NP1, vType:Type]),
%%   coord([type:conj, sem:C]),
%%   { member(Coord, [conj, no]) },
%%   np([coord:Coord, num:_, gap:G, sem:NP2, vType:Type]),
%%   { combine(np:NP, [np:NP1, coord:C, np:NP2]) }.

%% np([coord:disj, num:sg, gap:G, sem:NP, vType:Type]) -->
%%   coordPrefix([type:disj]),
%%   np([coord:no, num:sg, gap:G, sem:NP1, vType:Type]),
%%   noCoord([type:disj, sem:C]),
%%   np([coord:disj, num:sg, gap:G, sem:NP2, vType:Type]),
%%   { combine(np:NP, [np:NP1, coord:C, np:NP2]) }.
%% np([coord:disj, num:sg, gap:G, sem:NP, vType:Type]) -->
%%   coordPrefix([type:disj]),
%%   np([coord:no, num:sg, gap:G, sem:NP1, vType:Type]),
%%   coord([type:disj, sem:C]),
%%   { member(Coord, [disj, no]) },
%%   np([coord:Coord, num:sg, gap:G, sem:NP2, vType:Type]),
%%   { combine(np:NP, [np:NP1, coord:C, np:NP2]) }.

%% np([coord:yes, num:sg, gap:G, sem:NP, vType:Type]) -->
%%   coordPrefix([type:neg]),
%%   np([coord:no, num:sg, gap:G, sem:NP1, vType:Type]),
%%   coord([type:neg, sem:C]),
%%   np([coord:no, num:sg, gap:G, sem:NP2, vType:Type]),
%%   { combine(np:NP, [np:NP1, coord:C, np:NP2]) }.

np([coord:no, num:Num, gap:[], sem:NP, vType:dollar]) -->
  ['$'],
  np([coord:no, num:Num, gap:[], sem:NP, vType:dollar]).


np([coord:no, num:Num, gap:[], sem:NP, vType:Type]) -->
  det([mood:decl, type:_, num:Num, sem:Det, vType:Type]),
  n([coord:_, num:Num, sem:N, vType:Type]),
  { combine(np:NP, [det:Det, n:N]) }.


np([coord:no, num:Num, gap:[], sem:NP, vType:Type]) -->
  number([sem:Number, vType:Type]),
  n([coord:_, num:Num, sem:N, vType:Type]),
  { addTypeAttribute(Type, countable) },
  { combine(np:NP, [number:Number, n:N]) }.

np([coord:no, num:Num, gap:[], sem:NP, vType:Type]) -->
  { semLex(det, [type:indef, num:Num, sem:Det, vType:Type]) },
  [whoever],
  { semLex(relpro, [sem:RP]) },
  vp([coord:no, inf:fin, num:Num, gap:[], sem:VP, vType:Type]),
  { combine(np:NP, [det:Det, whoever:RP, vp:VP]) }.

np([coord:no, num:_Num, gap:[], sem:NP, vType:Type]) -->
  number([sem:Number, vType:Type]),
  { addTypeAttribute(Type, countable) },
  { combine(np:NP, [number:Number]) }.

%% np([coord:no, num:Num, gap:[tv:_TV-pred(_TypeSubj, TypeObj) | G], sem:NP, vType:TypeObj]) -->
%%     np([coord:no, num:Num, gap:G, sem:NP, vType:TypeObj]).
np([coord:no, num:Num, gap:[tv:TV-pred(TypeSubj, TypeObj) | G], sem:NP, vType:TypeObj]) -->
    np([coord:_, num:Num, gap:G, sem:NP1, vType:TypeSubj]),
    { combine(np:NP, [np:NP1, tv:TV, vType:TypeObj])}.

np([coord:comp, num:Num, gap:[tv:TV | G], sem:NP, vType:Type]) -->
  sp([num:Num, gap:[], sem:NP1, vType:Type]),
  comp([sem:Comp, vType:Type]),
  { Coord = no; Coord = np },
  np([coord:Coord, num:_, gap:[tv:TV | G], sem:NP2, vType:Type]),
  { addTypeAttribute(Type, countable) },
  { combine(np:NP, [np:NP1, comp:Comp, np:NP2]) }.

np([coord:no, num:Num, gap:[], sem:NP, vType:Type]) -->
  pn([num:Num, sem:PN, vType:Type]),
  { combine(np:NP, [pn:PN]) }.

np([coord:np, num:Num, gap:[], sem:NP, vType:Type]) -->
  det([mood:decl, type:_, num:Num, sem:Det, vType:Type]),
  np([coord:no, num:_, gap:[], sem:NP2, vType:Type2]),
  n([coord:_, num:Num, sem:N, vType:Type]),
  { combine(np:NP, [det:Det, np:NP2, n:N, vType1:Type, vType2:Type2]) }.

np([coord:np, num:Num, gap:[], sem:NP, vType:Type]) -->
  np([coord:no, num:_, gap:[], sem:NP2, vType:Type2]),
  [s],
  n([coord:_, num:Num, sem:N, vType:Type]),
  { combine(np:NP, [np:NP2, s:s, n:N, vType1:Type, vType2:Type2]) }.

sp([num:_Num, gap:[], sem:NP, vType:Type]) -->
    some([sem:SP, vType:Type]),
    { combine(np:NP, [some:SP]) }.
sp([num:Num, gap:[], sem:NP, vType:Type]) -->
    np([coord:no, num:Num, gap:[], sem:NP, vType:Type]).

%np([coord:no, num:sg, gap:[], sem:NP]) -->
%  pro([sem:PN]),
%  { combine(np:NP, [pn:PN]) }.

%np([coord:no, num:sg, gap:[], sem:NP]) -->
%  qnp([mood:decl, sem:QNP]),
%  { combine(np:NP, [qnp:QNP]) }.


/*========================================================================
  WH Noun Phrases
========================================================================*/

%% whnp([num:sg, sem:NP, vType:Type]) -->
%%  qnp([mood:int, sem:QNP, vType:Type]),
%%  { combine(whnp:NP, [qnp:QNP]) }.

%whnp([num:sg, sem:NP]) -->
%  det([mood:int, type:_, num:_, sem:Det]),
%  n([coord:_, num:_, sem:N]),
%  { combine(whnp:NP, [det:Det, n:N]) }.


/*========================================================================
  Nouns
========================================================================*/

n([coord:no, num:Num, sem:Sem, vType:Type]) -->
  noun([num:Num, sem:N, vType:Type]),
  nmod([num:Num, sem:PP, vType:Type]),
  { combine(n:Sem, [noun:N, nmod:PP]) }.

%% n([coord:yes, num:Num, sem:N, vType:Type]) -->
%%   n([coord:no, num:Num, sem:N1, vType:Type]),
%%   coord([type:_, sem:C]),
%%   n([coord:_, num:Num, sem:N2, vType:Type]),
%%   { combine(n:N, [n:N1, coord:C, n:N2]) }.

%% n([coord:C, num:Num, sem:Sem, vType:Type]) -->
%%   adj([sem:A, vType:adj(Type)]),
%%   n([coord:C, num:Num, sem:N, vType:Type]),
%%   { combine(n:Sem, [adj:A, n:N]) }.

n([coord:no, num:Num, sem:N, vType:Type]) -->
  noun([num:Num, sem:Noun, vType:Type]),
  { combine(n:N, [noun:Noun]) }.

nmod([num:_, sem:N, vType:Type]) -->
  pp([sem:PP, vType:Type]),
  { combine(nmod:N, [pp:PP]) }.

nmod([num:Num, sem:N, vType:Type]) -->
  rc([num:Num, sem:RC, vType:Type]),
  { combine(nmod:N, [rc:RC]) }.

%% nmod([num:Num, sem:Sem, vType:Type]) -->
%%   pp([type:n, sem:PP, vType:Type]),
%%   nmod([num:Num, sem:NMod, vType:Type]),
%%   { combine(nmod:Sem, [pp:PP, nmod:NMod]) }.

/*========================================================================
  Prepositional Phrases
========================================================================*/

pp([sem:PP, vType:SubjType]) -->
  prep([sem:Prep, vType:pred(SubjType, ObjType)]),
  np([coord:_, num:_, gap:[], sem:NP, vType:ObjType]),
  { combine(pp:PP, [prep:Prep, np:NP]) }.


/*========================================================================
  Relative Clauses
========================================================================*/

rc([num:Num, sem:RC, vType:Type]) -->
  relpro([sem:RP]),
  vp([coord:no, inf:fin, num:Num, gap:[], sem:VP, vType:Type]),
  { combine(rc:RC, [relpro:RP, vp:VP]) }.

%% rc([num:Num, sem:RC, vType:Type]) -->
%%   prep([type:v, syntax:PP, sem:_, vType:_]),
%%   relpro([sem:RP]),
%%   vp([coord:no, inf:fin, num:Num, gap:[pp:PP], sem:VP, vType:Type]),
%%   { combine(rc:RC, [relpro:RP, vp:VP]) }.

% For performance reasons only (could add [] as relpro as well)
rc([num:Num, sem:RC, vType:TypeSubj]) -->
  { semLex(relpro, [sem:RP]) },
  tv([inf:part, num:Num, gap:GapBefore-GapAfter, sem:TV, vType:pred(TypeSubj, TypeObj)]),
  GapBefore,
  np([coord:no, num:_, gap:[], sem:NP, vType:TypeObj]),
  GapAfter,
  { combine(rc:RC, [relpro:RP, vp:app(TV, NP)]) }.

rc([num:Num, sem:RC, vType:TypeObj]) -->
    { semLex(relpro, [sem:RP]) },
    np([coord:_, num:_, gap:[], sem:NP, vType:TypeSubj]),
    tv([inf:fin, num:Num, gap:_-[], sem:TV, vType:pred(TypeSubj, TypeObj)]),
    { combine(vp:VP, [np:NP, tv:TV]) },
    { combine(rc:RC, [relpro:RP, vp:VP]) }.

/*========================================================================
  Verb Phrases
========================================================================*/

vp([coord:yes, inf:Inf, num:Num, gap:[], sem:VP, vType:Type]) -->
  vp([coord:no, inf:Inf, num:Num, gap:[], sem:VP1, vType:Type]),
  coord([type:_, sem:C]),
  vp([coord:_, inf:Inf, num:Num, gap:[], sem:VP2, vType:Type]),
  { combine(vp:VP, [vp:VP1, coord:C, vp:VP2]) }.

vp([coord:no, inf:Inf, num:Num, gap:[], sem:VP, vType:Type]) -->
  av([inf:Inf, num:Num, sem:Mod]),
  { member(Inf2, [inf, part]) },
  vp([coord:_, inf:Inf2, num:_, gap:[], sem:V2, vType:Type]),
  { combine(vp:VP, [av:Mod, vp:V2]) }.

vp([coord:no, inf:Inf, num:Num, gap:[], sem:VP, vType:Type]) -->
  cop([type:np, inf:Inf, num:Num, sem:Cop]),
  np([coord:_, num:_, gap:[], sem:NP, vType:Type]),
  { combine(vp:VP, [cop:Cop, np:NP]) }.

%% vp([coord:no, inf:Inf, num:Num, gap:[], sem:VP, vType:Type]) -->
%%   cop([type:adj, inf:Inf, num:Num, sem:Cop]),
%%   adj([sem:Adj, vType:adj(Type)]),
%%   { combine(vp:VP, [cop:Cop, adj:Adj]) }.

vp([coord:no, inf:Inf, num:Num, gap:[], sem:VP, vType:Type]) -->
  cop([type:adj, inf:Inf, num:Num, sem:Cop]),
  pp([sem:PP, vType:Type]),
  { combine(vp:VP, [cop:Cop, adj:PP]) }.

vp([coord:no, inf:Inf, num:Num, gap:[], sem:VP, vType:Type]) -->
  cop([type:np, inf:Inf, num:Num, sem:Cop]),
  (number([sem:_, vType:_]) ; [all]),
  [different],
  n([coord:_, num:Num, sem:_N, vType:Type]),
  { combine(vp:VP, [cop:Cop, alldifferent]) }.

%% vp([coord:no, inf:Inf, num:Num, gap:[], sem:VP, vType:Type]) -->
%%   iv([inf:Inf, num:Num, sem:IV, vType:Type]),
%%   { combine(vp:VP, [iv:IV]) }.

%vp([coord:no, inf:Inf, num:Num, gap:[], sem:VP]) -->
%  iv([inf:Inf, num:Num, sem:IV]),
%  adv([sem:ADV]),
%  { combine(vp:VP, [iv:IV, adv:ADV]) }.

%vp([coord:no, inf:Inf, num:Num, gap:[], sem:VP]) -->
%  iv([inf:Inf, num:Num, sem:IV]),
%  pp([type:vp, sem:Adv]),
%  { combine(vp:VP, [iv:IV, adv:Adv]) }.

vp([coord:no, inf:I, num:Num, gap:[], sem:VP, vType:TypeObj]) -->
  np([coord:_, num:_, gap:[], sem:NP, vType:TypeSubj]),
  tv([inf:I, num:Num, gap:_-[], sem:TV, vType:pred(TypeSubj, TypeObj)]),
  { combine(vp:VP, [np:NP, tv:TV]) }.

vp([coord:no, inf:I, num:Num, gap:G, sem:VP, vType:TypeSubj]) -->
  tv([inf:I, num:Num, gap:Pre-Post, sem:TV, vType:pred(TypeSubj, TypeObj)]),
  optional(Pre),
  { Coord = conj ; Coord = comp },
  np([coord:Coord, num:_, gap:[tv:TV-pred(TypeSubj, TypeObj) | G], sem:NP, vType:TypeObj]),
  optional(Post),
  { combine(vp:VP, [tv:TV, np:NP]) }.

vp([coord:no, inf:I, num:Num, gap:G, sem:VP, vType:TypeSubj]) -->
  tv([inf:I, num:Num, gap:GapBefore-GapAfter, sem:TV, vType:pred(TypeSubj, TypeObj)]),
  GapBefore,
  np([coord:_, num:_, gap:G, sem:NP, vType:TypeObj]),
  optional(GapAfter),
  { combine(vp:VP, [tv:TV, np:NP]) }.

%% vp([coord:no, inf:I, num:Num, gap:G, sem:VP, vType:TypeSubj]) -->
%%   ivpp([inf:I, num:Num, pp:PP, sem:IVPP, vType:pred(TypeSubj, TypeObj)]),
%%   optional(PP),
%%   np([coord:_, num:_, gap:[tv:IVPP-pred(TypeSubj, TypeObj) | G], sem:NP, vType:TypeObj]),
%%   { combine(vp:VP, [tv:IVPP, np:NP]) }.

%% vp([coord:no, inf:I, num:Num, gap:[pp:PP], sem:VP, vType:TypeObj]) -->
%%   np([coord:_, num:_, gap:_, sem:NP, vType:TypeSubj]),
%%   ivpp([inf:I, num:Num, pp:PP, sem:IVPP, vType:pred(TypeSubj, TypeObj)]),
%%   { combine(vp:VP, [tv:IVPP, npSubj:NP]) }.

optional(X) -->
  optional(X, _).
optional([], _) -->
  [].
optional(X, true) -->
  { X \= [] },
  X.
optional(X, fail) -->
  { X \= [] },
  [].


numberOrAll-->
  [all].
numberOrAll-->
  number([sem:_, vType:_]).
debug(X, X) :-
  writeln(X).

/*========================================================================
  Lexical Rules
========================================================================*/

%% iv([inf:Inf, num:Num, sem:Sem, vType:Type]) -->
%%   { lexEntry(iv, [symbol:Sym, syntax:Word, inf:Inf, num:Num, vType:Type]) },
%%   Word,
%%   { semLex(iv, [symbol:Sym, sem:Sem]) }.

%% ivpp([inf:Inf, num:Num, pp:PP, sem:Sem, vType:Type]) -->
%%   { lexEntry(ivpp, [symbol:Sym, syntax:Word, pp:PP, inf:Inf, num:Num, vType:Type]) },
%%   Word,
%%   { semLex(ivpp, [symbol:Sym, sem:Sem]) }.

tv([inf:Inf, num:Num, gap:[]-[], sem:Sem, vType:Type]) -->
  { lexEntry(tv, [symbol:Sym, syntax:Word, inf:Inf, num:Num, vType:Type]) },
  Word,
  { semLex(tv, [symbol:Sym, sem:Sem]) }.

tv([inf:Inf, num:Num, gap:PP-[], sem:Sem, vType:Type]) -->
  { lexEntry(ivpp, [symbol:Sym, syntax:Word, pp:PP, inf:Inf, num:Num, vType:Type]) },
  Word,
  { semLex(tv, [symbol:Sym, sem:Sem]) }.

tv([inf:Inf, num:Num, gap:[]-Gap, sem:Sem, vType:Type]) -->
  { lexEntry(tvgap, [symbol:Sym, syntax:Word, gap:Gap, inf:Inf, num:Num, vType:Type]) },
  Word,
  { semLex(tv, [symbol:Sym, sem:Sem]) }.

tv([inf:Inf, num:Num, gap:[]-Gap, sem:Sem, vType:Type]) -->
  cop([type:tv, inf:Inf, num:Num, sem:Sem, symbol:Sym]),
  { lexEntry(copgap, [symbol:Sym, syntax:Word, gap:Gap, vType:Type]) },
  Word.

cop([type:Type, inf:Inf, num:Num, sem:Sem]) -->
  cop([type:Type, inf:Inf, num:Num, sem:Sem, symbol:_]).
cop([type:Type, inf:Inf, num:Num, sem:Sem, symbol:Sym]) -->
  { lexEntry(cop, [pol:Pol, syntax:Word, inf:Inf, num:Num]) },
  Word,
  { semLex(cop, [pol:Pol, type:Type, sem:Sem, symbol:Sym]) }.

det([mood:M, type:Type, num:Num, sem:Det, vType:VType]) -->
  { lexEntry(det, [syntax:Word, mood:M, num:Num, type:Type]) },
  Word,
  { semLex(det, [type:Type, num:Num, sem:Det, vType:VType]) }.

number([sem:Sem, vType:Type]) -->
  [Number],
  { integer(Number) },
  { semLex(number, [number:Number, sem:Sem, vType:Type]) },
  { addType(number-Number, Type) }.
number([sem:Sem, vType:Type]) -->
  { lexEntry(number, [syntax:Word, number:Number]) },
  Word,
  { semLex(number, [number:Number, sem:Sem, vType:Type]) },
  { addType(number-Number, Type) }.

pn([num:Num, sem:Sem, vType:Type]) -->
  { lexEntry(pn, [symbol:Sym, syntax:Word, num:Num, vType:Type]) },
  optional([the]),
  Word,
  { semLex(pn, [symbol:Sym, sem:Sem]) }.

%pro([sem:Sem]) -->
%  { lexEntry(pro, [symbol:Sym, syntax:Word]) },
%  Word,
%  { semLex(pro, [symbol:Sym, sem:Sem]) }.

relpro([sem:Sem]) -->
  { lexEntry(relpro, [syntax:Word]) },
  Word,
  { semLex(relpro, [sem:Sem]) }.

prep([sem:Sem, vType:VType]) -->
  { lexEntry(prep, [symbol:Sym, syntax:Word, type:_, vType:VType]) },
  Word,
  { semLex(prep, [symbol:Sym, type:n, sem:Sem]) }.

%% adj([sem:Sem, vType:Type]) -->
%%   { lexEntry(adj, [symbol:Sym, syntax:Word, vType:Type]) },
%%   Word,
%%   { semLex(adj, [symbol:Sym, sem:Sem]) }.

%adv([sem:Sem]) -->
%  { lexEntry(adv, [symbol:Sym, syntax:Word]) },
%  Word,
%  { semLex(adv, [symbol:Sym, sem:Sem]) }.

av([inf:Inf, num:Num, sem:Sem]) -->
  { lexEntry(av, [syntax:Word, inf:Inf, num:Num, pol:Pol]) },
  Word,
  { semLex(av, [pol:Pol, sem:Sem]) }.

coordPrefix([type:_]) --> [].
coordPrefix([type:Type]) -->
  { lexEntry(coordPrefix, [syntax:Word, type:Type]) },
  Word.

coord([type:Type, sem:Sem]) -->
  { lexEntry(coord, [syntax:Word, type:Type]) },
  Word,
  { semLex(coord, [type:Type, sem:Sem]) }.
noCoord([type:Type, sem:Sem]) -->
  { semLex(coord, [type:Type, sem:Sem]) }.

%% qnp([mood:M, sem:NP, vType:_VType]) -->
%%   { lexEntry(qnp, [symbol:Symbol, syntax:Word, mood:M, type:Type]) },
%%   Word,
%%   { semLex(qnp, [type:Type, symbol:Symbol, sem:NP]) }.

noun([num:Num, sem:Sem, vType:Type]) -->
  { lexEntry(noun, [symbol:Sym, num:Num, syntax:Word, vType:Type]) },
  Word,
  { semLex(noun, [symbol:Sym, sem:Sem]) }.

comp([sem:Sem, vType:VType]) -->
  { lexEntry(comp, [type:Type, syntax:Word]) },
  Word,
  { semLex(comp, [type:Type, sem:Sem, vType:VType]) }.

some([sem:Sem, vType:Type]) -->
  { lexEntry(some, [syntax:Word]) },
  Word,
  { semLex(some, [sem:Sem, vType:Type]) }.
some([sem:Sem, vType:Type]) -->
  { semLex(some, [sem:Sem, vType:Type]) }.
