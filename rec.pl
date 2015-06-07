:- module(rec, [rec/6]).
:- use_module(library(ordsets), [list_to_ord_set/2, ord_union/3]).
:- use_module(atom, [built_in/1, fresh_all/2]).
:- use_module(aux, [eliminate_duplicates/2, flatten/2,
		    my_ord_subtract/3, my_ord_del_element/4,
		    my_remove_duplicates/2]).
:- use_module(library(lists),[append/3, member/2]).
% rec(Clauses, Rec, DirectRecursive, MutuallyRecursive, Nonrec)
% divides predicates determined
% by Clauses to recursive ones and non-recursive ones

rec(Clauses, Rec, DR, MR, Nonrec, Unfoldable):-
	pairs(Clauses, Pairs),
	dir_rec(Pairs, DirRec),
	my_ord_subtract(Pairs, DirRec,Others),
	drop_23(DirRec, DR),
	mut_rec(Others, DR, MutRec,Nonrec,  Unfoldable),
	distinguish(MutRec, MR),
	ord_union(DirRec,MutRec,Rec_),
	drop_23(Rec_, Rec__), my_remove_duplicates(Rec__, Rec),!.

pairs(Clauses, Pairs):-
	pairs_(Clauses, Pairs0),
	flatten(Pairs0, Pairs1),
	list_to_ord_set(Pairs1,Pairs).
pairs_([],[]).
pairs_([Clause|Clauses], [Pairs0|Pairs]):-
	pairs_(Clause, Pairs0),
	pairs_(Clauses,Pairs).
pairs_(clause(_Head,true),[]).
pairs_(clause(Head,(B1,B2)),[(H,B,clause)|L]):-
	\+ built_in(B1), !,
	fresh_all(Head,H),
	fresh_all(B1,B),
	pairs_(clause(Head,B2),L).
pairs_(clause(Head,(_B1,B2)),L):-
	pairs_(clause(Head,B2),L).

% finds directly recursive predicates
dir_rec(Pairs, DirRec) :-
	dir_rec_(Pairs, DR),
	list_to_ord_set(DR,DirRec).
dir_rec_([],[]).
dir_rec_([(X,X,R)|Pairs], [(X,X,R)|Recs]):-
	!, my_ord_del_element(Pairs, (X,_,_), Rest, _),
	dir_rec_(Rest, Recs).
dir_rec_([_|Pairs], Recs):-
	dir_rec_(Pairs, Recs).

% add_pred_no_clause(Elements, Elements, Pairs1, Pairs2).
add_pred_no_clause([], P, P).
add_pred_no_clause([El|Elements], Pairs1, Pairs2):-
	\+ member((El,_,_), Pairs1), !,
	add_pred_no_clause(Elements, [(El,true,clause)|Pairs1], Pairs2).
add_pred_no_clause([_El|Elements], Pairs1, Pairs2):-
	add_pred_no_clause(Elements,Pairs1, Pairs2).

% mut_rec(Pairs,  DR, MutRec,NonRec,  Unfoldable)

mut_rec(Pairs, DR,Rec,NonRec,  Unfoldable):-
	drop_reason(Pairs, Pairs_),
	elements(Pairs, Elements_),
	my_ord_subtract(Elements_, DR, Elements),
	closure(Pairs,Pairs, [], Elements, Rec, NonRec, Pairs_),
	find_unfoldables(NonRec, Pairs,  Unfoldable).

find_unfoldables(A1, Pairs, A3):-
	find_candidates(A1, Pairs, A2),
	(A1 = A2 -> A3 = A1 ;
	    find_unfoldables(A2, Pairs, A3)).

not_unfoldable_candidate1(P, As, Pairs):-
	member((P,Q,_), Pairs),
	\+ member(Q, As).
find_candidates(Preds, Pairs, Candidates) :-
	find_candidates(Preds, Preds, Pairs, Candidates).
find_candidates([], _, _, []).
find_candidates([P|Preds], As, Pairs, [P|Candidates]) :-
	\+ not_unfoldable_candidate1(P, As, Pairs), !,
	find_candidates(Preds, As, Pairs, Candidates).
find_candidates([_P|Preds], As, Pairs, Candidates) :-
	find_candidates(Preds, As, Pairs, Candidates).

elements(Pairs, Elements) :-
	drop_reason2(Pairs,Elements_),
	list_to_ord_set(Elements_, Elements__),
	eliminate_duplicates(Elements__, Elements).
	  
closure(_,[],R,N,R,N,_).
closure(Pairs, Closure, R1, N1,  R3, N3, All):-
	closure(Pairs,Closure,NextClosure, R1, N1, 
		R2, N2, All, NewAll),
	closure(Pairs,NextClosure,R2,N2,R3,N3,NewAll).

closure(Pairs,Closure,NextClosure,R1,N1,R2,N2,All,NewAll):-
	multiply(Pairs,Closure,Res,Pairs),
	list_to_ord_set(Res,ResOrdSet),
	my_ord_subtract(ResOrdSet, All, Diff),
	dir_rec(Diff, DR),
	list_to_ord_set(DR,ADR),
	ord_union(R1,ADR,R2),
	drop_23(DR, DR_23),
	my_ord_subtract(N1, DR_23, N2),
	my_ord_subtract(Diff,DR,NextClosure),
	drop_reason(NextClosure, NextClosure_),
	ord_union(All, NextClosure_, NewAll).

multiply([],[],[],_).
multiply([],[_|L],Pairs3, P):-
	multiply(P,L,Pairs3,P).
multiply([(X,Y,R1)|Pairs1],[(Y,Z,R2)|Pairs2],
	 [(X,Z,((X,Y,R1),(Y,Z,R2)))|Pairs3], P):-
	!, multiply(Pairs1,[(Y,Z,R2)|Pairs2],Pairs3, P).
multiply([_|Pairs1],Pairs2,Pairs3, P):-
	!, multiply(Pairs1,Pairs2,Pairs3, P).



distinguish(L1,L2):-
	distinguish_(L1,L),
	eliminate_duplicates(L,L2).
distinguish_([],[]).
distinguish_([(X,X,Reason)|L], [L1|MR]):-
	distinguish_((X,X,Reason), L1),
	my_ord_subtract(L,L1,L2),
	distinguish_(L2,MR).
distinguish_((_X,Y,clause),[Y]).
distinguish_((X,_Y,(R1,R2)), L):-
	distinguish_(R1,L1),
	distinguish_(R2,L2),
	append(L1,L2,L_),
	sort([X|L_],L).

drop_23([],[]).
drop_23([(E,_,_)|L],[E|L1]):-
	drop_23(L,L1).

drop_reason([],[]).
drop_reason([(E1,E2,_)|L],[(E1,E2,_Var)|L1]):-
	drop_reason(L,L1).

drop_reason2([],[]).
drop_reason2([(E1,E2,_)|L],[E1,E2|L1]):-
	drop_reason2(L,L1).


g(Rec, DR, MR, NonRec, Unfoldable):- rec([clause('p_in(#VAR(1),2,inf)'(_20412,_20377),(_20377>1,_20412 is _20377*_20377,'p_in(#VAR(0),2,inf)'(_20377),true)),clause('p_in(#VAR(0),2,inf)'(_20984),(_20932 is _20984-1,'p_in(#VAR(1),2,inf)'(_20932,_20919),true)),clause('p_in(#VAR(0),2,inf)'(_20856),(_20804 is _20856-1,'p_in(#VAR(1),-inf,1)'(_20804,_20791),true)),clause('p_in(#VAR(0),-inf,1)'(_20728),(_20676 is _20728-1,'p_in(#VAR(1),2,inf)'(_20676,_20663),true)),clause('p_in(#VAR(0),-inf,1)'(_20600),(_20548 is _20600-1,'p_in(#VAR(1),-inf,1)'(_20548,_20535),true))], Rec, DR, MR, NonRec, Unfoldable).
/*
rec:rec([clause('q_#VAR(0)_>_#VAR(1)'(_3376,_3190),
     (_3376>_3190,_3226 is _3376-_3190,_3306 is _3190+1,'q_#VAR(0)_>_#VAR(1)'(_3226,_3306),true)),
     clause('q_#VAR(0)_>_#VAR(1)'(_3074,_2888),
     (_3074>_2888,_2924 is _3074-_2888,_3004 is _2888+1,'q_#VAR(0)_=<_#VAR(1)'(_2924,_3004),true))],
     A,B,C,D,E).
*/
