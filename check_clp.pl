:- module(check_clp, [check_clp/1,check_clp_/1]).
:- use_module(library(clpq)).

check_clp(X):-
	copy_term(X,Y), check_clp_(Y).

check_clp_(true) :- !.
check_clp_(false) :- fail.
check_clp_((_X,-inf,inf)):-!.
check_clp_((X,Min,inf)):- !, {X >= Min}.
check_clp_((X,-inf,Max)):- !, {X =< Max}.
check_clp_((X,Min,Max)):- {X >= Min, X =< Max}.

check_clp_(X is Y)       :- var(X), var(Y), !, {X = Y}.
check_clp_(X is Y mod Z) :- var(X), !, {X < Y, X < Z, X >= 0}.
check_clp_(X is Y)       :- var(X), !, {X = Y}.
check_clp_(X mod Y is Z) :- !, check_clp_(Z is X mod Y).
check_clp_(X is Y mod Z) :- !, {X < Y, X < Z, X >= 0}.
check_clp_(X is Y)       :- {X = Y}.

check_clp_(X = Y)  :- {X = Y}.
check_clp_(X > Y)  :- var(X), !, {X > Y, X >= Y+1}.
				         % the second constraint may be added
                                         % since X and Y are integers
check_clp_(X mod Z > Y) :- !, check_clp_(and(T is X mod Z, T > Y)).
check_clp_(X > Y)  :- {X > Y, X >= Y+1}.
				         % the second constraint may be added
                                         % since X and Y are integers
check_clp_(X >= Y) :- var(X), !, {X >= Y}.
check_clp_(X mod Z >= Y) :- !, check_clp_(and(T is X mod Z, T >= Y)).
check_clp_(X >= Y) :- {X >= Y}.

check_clp_(X < Y)  :- var(X), !, {X < Y, X =< Y-1}.
				         % the second constraint may be added
                                         % since X and Y are integers
check_clp_(X mod Z < Y) :- !, check_clp_(and(T is X mod Z, T < Y)).
check_clp_(X < Y)  :- !, {X < Y, X =< Y-1}.
				         % the second constraint may be added
                                         % since X and Y are integers
check_clp_(X =< Y) :- var(X), !, {X =< Y}.
check_clp_(X mod Z =< Y) :- !, check_clp_(and(T is X mod Z, T =< Y)).
check_clp_(X =< Y) :- {X =< Y}.

check_clp_(and(X1,X2)):-
	check_clp_(X1), check_clp_(X2).
check_clp_(or(X1,_X2)):-
	check_clp_(X1), !.
check_clp_(or(_X1,X2)):-
	check_clp_(X2), !.
check_clp_(not(X1)):-
	\+ check_clp_(X1).

