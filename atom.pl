:- module(atom, [arithmetic/1,
		 atom_list_concat/2,built_in/1, comparison/1, fresh_all/2,
		 identical/2, is_atom/1, match/2, substitute_atom/4,
		 term_comparison/1]).
:- use_module(library(lists), [append/3, is_list/1]).
	      
atom_list_concat([],'').
atom_list_concat([H|T],C):-
	atom_list_concat(T,CT),
	aon_concat(H,CT,C).

% aon = atom or number
aon_concat(N1,N2,N3):-
	aon_chars(N1,LN1),
	aon_chars(N2,LN2),
	append(LN1,LN2,LN3),
	atom_chars(N3,LN3).

% aon = atom or number
aon_chars(X,L):-
	number(X), number_chars(X,L).
aon_chars(X,L):-
	atom(X), atom_chars(X,L).

arithmetic(-_).
arithmetic(_+_).
arithmetic(_-_).
arithmetic(_*_).
arithmetic(_/_).

comparison(_X = _Y).
comparison(_X < _Y).
comparison(_X =< _Y).
comparison(_X > _Y).
comparison(_X >= _Y).
comparison(_X =\= _Y).
comparison(_X == _Y).

term_comparison(arg(_,_,_)).
term_comparison('=..'(_,_)).

is_atom(_X is _Y).

built_in(X):- is_atom(X).
built_in(X):- comparison(X).
built_in(X):- term_comparison(X).
built_in('!').
built_in(number(_)).
built_in(integer(_)).
built_in(write(_)).
built_in(nl).
built_in(fail).
built_in(var(_)).
built_in(nonvar(_)).
built_in(functor(_,_,_)).
built_in(atom(_)).

substitute_atom(Atom, Positions, Values, NewAtom):-
	Atom =.. [Name|Arguments],
	substitute_args(Arguments, Positions, Values, 1, NewArguments),
	NewAtom =.. [Name|NewArguments].

substitute_args(Arguments, [], _, _I, Arguments) :- !.
substitute_args([Argument|Arguments], [I|Positions],
		Values, K, [Argument|NewArguments]) :-
	K < I, K1 is K+1,
	substitute_args(Arguments, [I|Positions], Values, K1, NewArguments).
substitute_args([_Argument|Arguments], [I|Positions],
		[Value|Values], I, [Value|NewArguments]) :-
	I1 is I+1,
	substitute_args(Arguments, Positions, Values, I1, NewArguments).

% fresh_all returns atom of the same functor but with all args - fresh vars
fresh_all(Atom, NewAtom):-
	functor(Atom, Name, Arity),
	functor(NewAtom, Name, Arity).

identical(X,Y):- var(X), var(Y).
identical(X,Y):- atomic(X), atomic(Y), !, X=Y.
identical(X,Y):- is_list(X), is_list(Y), !,
	X = [XH|XT], Y = [YH|YT], % unifications always succeed,
	                          % since [] is atomic, i.e. excluded
	                          % by the previous clause
	identical(XH,YH), identical(XT,YT).
identical(X,Y):- compound(X), compound(Y), !,
	X =.. [N|XArgs], Y=.. [N|YArgs],
	identical(XArgs, YArgs).

% Y matches X, i.e., after the unification Y is unchanged
match(X,Y):- var(X), !, X=Y.
match(X,Y):- atomic(X), atomic(Y), !, X=Y.
match(X,Y):- is_list(X), is_list(Y), !,
	X = [XH|XT], Y = [YH|YT], % unifications always succeed,
	                          % since [] is atomic, i.e. excluded
	                          % by the previous clause
	match(XH,YH), match(XT,YT).
match(X,Y):- compound(X), compound(Y), !,
	X =.. [N|XArgs], Y=.. [N|YArgs],
	match(XArgs, YArgs).









