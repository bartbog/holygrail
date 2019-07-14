:- module(typesLexicon, [
              lexicalTypes/1,
              addLexicalType/2
            ]).

lexicalTypes(Types) :-
  nb_current(lexical_types, Types),
  !.
lexicalTypes([]).

addLexicalType(Symbol, Type) :-
  lexicalTypes(Types),
  b_setval(lexical_types, [type(Symbol, Type) | Types]).
