%%%%% last changed on 17 may 1997
%
%                  transform1.pl
% TRANSFORMATION OF CONTROL PREDICATES : -> ; and ASSOCIATIVITY
%                   CORRECTION

:- module(transform1,[transform/2, normal_form/2]).
:- use_module(library(lists)).
%%% ;
rewrite_or(X,(Y,Z)) :- functor(X,',',2),!,
			arg(1,X,X1),arg(2,X,X2),
			rewrite_or(X1,Y),rewrite_or(X2,Z).
rewrite_or(X,Y) :- functor(X,';',2),arg(1,X,X1),
			rewrite_or(X1,Y).
			change_transformed(';').
rewrite_or(X,Y) :- functor(X,';',2),arg(2,X,X1),
			rewrite_or(X1,Y),
			change_transformed(';').
rewrite_or(X,X) :- \+ functor(X,';',2).

rorall((A:-B),L,M) :- findall((A:-E),(rewrite_or(B,E),\+ B=E),L),
                    (L=[] -> M=[] ; M=[(A:-B)]).

%%% ->
rewrite_imply(X,(Y,Z)) :- functor(X,',',2),!,
			arg(1,X,X1),arg(2,X,X2),
			rewrite_imply(X1,Y),rewrite_imply(X2,Z).
rewrite_imply(X,(Y1,Y2)) :- 
	functor(X,'->',2),arg(1,X,X1),
	rewrite_imply(X1,Y1),arg(2,X,X2),
	rewrite_imply(X2,Y2),change_transformed('->').
rewrite_imply(X,X) :- \+ functor(X,'->',2).

rimall((A:-B),L,M) :- findall((A:-E),(rewrite_imply(B,E),\+ B=E),L),
                    (L=[] -> M=[] ; M=[(A:-B)]).

%%% associativity correction
rewrite_assoc(','(','(A,B),C),','(A,','(B,C))) :- !.
rewrite_assoc(','(A,','(B,C)),','(A,L)) :- rewrite_assoc(','(B,C),L).
normal_form(F,N) :- rewrite_assoc(F,F1),!, normal_form(F1,N).
normal_form(F,F).
rasall((H:-B),L,M) :-
	findall((H:-B1),(normal_form(B,B1),\+ B=B1),L),
	(L=[] -> M=[] ; M=[(H:-B)]).

rall([],[],[],_):- !.
rall([(A:-B)|Clauses],LAdd,LDelete,Flag):-
	!, rall((A:-B),LAdd1,LDelete1,Flag),
	rall(Clauses,LAdd2,LDelete2,Flag),
	append(LAdd1,LAdd2,LAdd),
	append(LDelete1,LDelete2,LDelete).
rall([_|Clauses],LAdd,LDelete,Flag):-
	!, rall(Clauses,LAdd,LDelete,Flag).
rall(Rule,L,M,or) :- rorall(Rule,L,M).
rall(Rule,L,M,imp) :- rimall(Rule,L,M).
rall(Rule,L,M,assoc) :- rasall(Rule,L,M).

rall(Clauses,Clauses1,Flag):-
	rall(Clauses,LAdd,LDelete,Flag),
	
	
transform0(Clauses,Clauses3):-	
	rall(Clauses,Clauses0,or),
	rall(Clauses0,Clauses1,imp),
	rall(Clauses1,Clauses2,assoc),
	remove_variants(Clauses2,Clauses3).

remove_variants([],[]).
remove_variants([X|L1],[X|L2]) :-
	\+ member(X,L1),!,remove_variants(L1,L2).
remove_variants([_|L1],L2) :-
	remove_variants(L1,L2).

transform(Clauses,Clauses2):-
	transform0(Clauses,Clauses1),
	(Clauses = Clauses1 -> Clauses2 = Clauses1
	; transform(Clauses1,Clauses2)).
	
%%% used in TermiLog to report what kind of control predicates were
%%% discovered.
change_transformed(_).














