:- module(apply, [apply/3]).
:- use_module(adorn, [original_free_atom/3]).
:- use_module(library(lists), [nth0/3]).
:- use_module(library(clpfd)).

apply(X, _Atom, X):-
	var(X), !.
apply(or(LA1,LA2), Atom, or(A1,A2)):- !,
	apply(LA1,  Atom, A1),
	apply(LA2,  Atom, A2).
apply(and(LA1,LA2), Atom, and(A1,A2)):-!,
	apply(LA1,  Atom, A1),
	apply(LA2,   Atom, A2).
apply(not(LA1), Atom, not(A1)):-!,
	apply(LA1,  Atom, A1).
apply(LA1 = LA2,  Atom, A1 = A2):- !,
	apply(LA1,  Atom, A1),
	apply(LA2,  Atom, A2).
apply(LA1 >= LA2, Atom, A1 >= A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply(LA1 =< LA2,  Atom, A1 =< A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply(LA1 > LA2, Atom, A1 > A2):- !,
	apply(LA1,  Atom, A1),
	apply(LA2,  Atom, A2).
apply(LA1 < LA2, Atom, A1 < A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply(LA1 #= LA2,  Atom, A1 #= A2):- !,
	apply(LA1,  Atom, A1),
	apply(LA2,  Atom, A2).
apply(LA1 #>= LA2, Atom, A1 #>= A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply(LA1 #=< LA2,  Atom, A1 #=< A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply(LA1 #> LA2, Atom, A1 #> A2):- !,
	apply(LA1,  Atom, A1),
	apply(LA2,  Atom, A2).
apply(LA1 #< LA2, Atom, A1 #< A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply(LA1 is LA2, Atom, A1 is A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply(-LA1, Atom, -A1):-!,
	apply(LA1,  Atom, A1).
apply(LA1 + LA2, Atom, A1 + A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply(LA1 - LA2, Atom, A1 - A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply(LA1 * LA2, Atom, A1 * A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply(LA1 / LA2, Atom, A1 / A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply(LA1 mod LA2, Atom, A1 mod A2):- !,
	apply(LA1,   Atom, A1),
	apply(LA2,   Atom, A2).
apply((LA1, A2, A3),  Atom, (A1, A2,A3)):- !,
	apply(LA1,   Atom, A1).
apply('#VAR'(K),  Atom, V):-
	!, original_free_atom(Atom, OAtom, _),
	user:iap(OAtom-IntArgPos),!,
	nth0(K, IntArgPos, ArgNo),
	arg(ArgNo, Atom, V).
apply(G, _, G):-
	ground(G).
