%%%%% last changed on 17 may 1997
%
%                  transform.pl
% TRANSFORMATION OF CONTROL PREDICATES : -> ; and ASSOCIATIVITY
%                   CORRECTION

:- module(transform,[transform/2, normal_form/2]).
:- use_module(library(lists)).
:- use_module(aux).
:- use_module(numvars).

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

rorall((A:-B),L) :- findall((A:-E),rewrite_or(B,E),L).

%%% ->
rewrite_imply(X,(Y,Z)) :- functor(X,',',2),!,
			arg(1,X,X1),arg(2,X,X2),
			rewrite_imply(X1,Y),rewrite_imply(X2,Z).
rewrite_imply(X,(Y1,Y2)) :- 
	functor(X,'->',2),arg(1,X,X1),
	rewrite_imply(X1,Y1),arg(2,X,X2),
	rewrite_imply(X2,Y2),change_transformed('->').
rewrite_imply(X,X) :- \+ functor(X,'->',2).

rimall((A:-B),L) :- findall((A:-E),rewrite_imply(B,E),L).

%%% associativity correction
rewrite_assoc(','(','(A,B),C),','(A,','(B,C))) :- !.
rewrite_assoc(','(A,','(B,C)),','(A,L)) :- rewrite_assoc(','(B,C),L).
normal_form(F,N) :- rewrite_assoc(F,F1),!, normal_form(F1,N).
normal_form(F,F).
rasall((H:-B),L) :-
	findall((H:-B1),normal_form(B,B1),L).

rall([],[],_):- !.
rall([(A:-B)|Clauses],L,Flag):-
	!, rall((A:-B),L1,Flag),
	rall(Clauses,L2,Flag),
	append(L1,L2,L).
rall([Fact|Clauses],[Fact|L],Flag):-
	!, rall(Clauses,L,Flag).

rall(Rule,LTR,or) :- rorall(Rule,LTR).
rall(Rule,LTR,imp) :- rimall(Rule,LTR).
rall(Rule,LTR,assoc) :- rasall(Rule,LTR).

transform0(Clauses,Clauses3):-
	%timer('After Reading'),
	rall(Clauses,Clauses0,or),%timer('After OR'),
	rall(Clauses0,Clauses1,imp),%timer('After IMP'),
	rall(Clauses1,Clauses2,assoc),%timer('After ASSOC')
	remove_variants(Clauses2,Clauses3).

remove_variants([],[]).
remove_variants([X|L1],[X|L2]) :-
	\+ member(X,L1),!,remove_variants(L1,L2).
remove_variants([_|L1],L2) :-
	remove_variants(L1,L2).
frzl-f([],[],[]).
frzl-f([(H:-B)|Clauses],[F|FClauses],Facts) :- !,
        frz((H:-B),F),
	frzl-f(Clauses,FClauses,Facts).
frzl-f([Fact|Clauses],FClauses,[Fact|Facts]) :- 
	frzl-f(Clauses,FClauses,Facts).

melt_newl-f([],[]).
melt_newl-f([F|FClauses],[Clause|Clauses]):-
	melt_new(F,Clause),
	melt_newl-f(FClauses,Clauses).
	    
transform(Clauses,Clauses1):-
	frzl-f(Clauses,Clauses_,Facts),
	transform_(Clauses_,Clauses1_),
	melt_newl-f(Clauses1_,Clauses1__),
	append(Facts,Clauses1__,Clauses1).
		
transform_(Clauses,Clauses2):-	
	transform0(Clauses,Clauses1),%timer('After Transform0 '),
	(Clauses = Clauses1 -> Clauses2 = Clauses1
	; ( diff(Clauses1, Clauses, ClausesDiff,ClausesCommon),
	    transform_(ClausesDiff,ClausesDiff2),
	    append(ClausesDiff2,ClausesCommon,Clauses2))).

/*
transform(Clauses,Clauses2):-	
	transform0(Clauses,Clauses1),%timer('After Transform0 '),
	diff(Clauses1, Clauses, ClausesDiff,ClausesCommon),
	%timer('After Diff '),
	(ClausesDiff = [] -> Clauses2 = Clauses1
	      ;
	    (transform(ClausesDiff,ClausesDiff2),
	      %timer('After Transform_#2 '),
	    append(ClausesDiff2,ClausesCommon,Clauses2))).

*/

diff([],_,[],[]).
diff([X|L1],L2,L3,[X|L4]):-
	member(X,L2),!, diff(L1,L2,L3,L4).
diff([X|L1],L2,[X|L3],L4):-
	diff(L1,L2,L3,L4).

%%% used in TermiLog to report what kind of control predicates were
%%% discovered.
change_transformed(_).





/*
time(_),read_program('../examples/maria/boyer.pl',Clauses),
     rec_comps(Clauses,Comps), timer('Time measured is:').
*/







