:- module(simplify_symb, [combine/2,simplify_symb/2]).
:- use_module(numvars, [varname/1]).
:- use_module(comma, [remove_trues/2]).
:- use_module(library(lists), [append/3, is_list/1, member/2]).
:- use_module(library(ordsets), [is_ordset/1, list_to_ord_set/2,ord_union/3]).


eq(and(I,I),I).
eq(and(A, true), A).
eq(and(true, A), A).
eq(X+0,X).
eq(0+X,X).
eq(_X*0,0).
eq(0*_X,0).
eq(X*1,X).
eq(1*X,X).
eq(X+X*(-1),0).
eq(X+(-1)*X,0).
eq(X*(-1)+X,0).
eq((-1)*X+X,0).
eq((-1)*(X*(-1)), X).
eq((B*C), D):- number(B), number(C), D is B*C.
eq((B+C), D):- number(B), number(C), D is B+C.			
eq((A*B)*C,A*(B*C)).
eq(A*(B+C),A*B+A*C). %%%% :- \+ varname(A).
%%%%%%% eq(A*B+A*C,A*(B+C)) :- varname(A).
eq((A+B)*C,A*C+B*C).
eq(A-B, A+B*(-1)).
eq(X1+X2,Y1+Y2):- remove_pairs(X1+X2,Y1+Y2), \+ X1+X2=Y1+Y2.

simplify_symb(X, X) :- var(X), !.
simplify_symb(X, X) :- number(X).
simplify_symb(Exp,SExp):-
	eq(Exp,NExp),!,
	simplify_symb(NExp,SExp).
simplify_symb(implies(Body,BuiltIns,Head),
	      implies(Body1,BuiltIns1,Head1)) :-
	!, simplify_symb(Body,Body1),
	remove_trues(BuiltIns, BuiltIns1),
	simplify_symb(Head,Head1).
simplify_symb(-S, SExp):-
	simplify_symb(S*(-1),SExp).
simplify_symb(S,SExp):-
	S =.. [Op,X,Y],
	simplify_symb(X,SX),
	simplify_symb(Y,SY),
	\+ ((X,Y) = (SX,SY)), !,
	S1 =.. [Op, SX, SY],
	simplify_symb(S1,SExp).
simplify_symb(Exp,Exp).

% X and -X form a pair
remove_pairs(X,Y):-
	to_list(X,LX),
	remove_pairs_(LX,LY),
	to_sum(LY, Y).

to_list(X+Y, L):-
	!, to_list(X, L1), to_list(Y,L2), append(L1,L2,L).
to_list((X+Y)*Z, L):- !, to_list(X*Z+Y*Z,L).
to_list(X*(Y+Z), L):- !, to_list(X*Y+X*Z,L).
to_list(X, [X]).

to_sum([], 0).
to_sum([X], X) :- !.
to_sum([X|Xs], X+S):-to_sum(Xs,S).

remove_pairs_([], []).
remove_pairs_([X|Xs], Ys) :-
	neg(X,NX),
	member(NX, Xs), !,
	remove_once(Xs, NX, Zs),
	remove_pairs_(Zs, Ys).
remove_pairs_([X|Xs], [X|Ys]) :-
	remove_pairs_(Xs, Ys).


neg(X, Y):- neg_(X,Y).
neg((-1)*X, X) :- !.
neg(X, (-1)*X).

neg_(X*(-1), X):- !.
neg_(X*Y, X*Y1):-
	!, neg_(Y, Y1).
neg_(X, X*(-1)).

remove_once([X|T], X, T) :- !.
remove_once([Y|T], X, [Y|Z]) :- remove_once(T, X, Z).

combine(Pos, Positions):-
	keysort(Pos, Pos1),
	combine_(Pos1,Positions).
combine_([],[]).
combine_([Pred-Pos1, Pred-Pos2|Pos], Positions):-
	is_list(Pos1), !,
	to_ordset(Pos1, Pos11),
	to_ordset(Pos2, Pos21),
	ord_union(Pos11,Pos21,Pos3),
	combine_([Pred-Pos3|Pos], Positions).
combine_([Pred-Pos1, Pred-Pos2|Pos], Positions):-
	simplify_symb(Pos1+Pos2,Pos3),
	combine_([Pred-Pos3|Pos], Positions).
combine_([Pred-Pos1|Pos], [Pred-Pos1|Positions]):-
	combine_(Pos, Positions).
to_ordset(OrdSet, OrdSet):-
	is_ordset(OrdSet), !.
to_ordset(List, OrdSet):-
	list_to_ord_set(List, OrdSet).