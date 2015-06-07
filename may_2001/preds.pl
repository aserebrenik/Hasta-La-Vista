:- module(preds,[built_in/1,rec_comps/2,rec_comps/3,preds/2]).
:- use_module(library(lists)).
:- use_module(library(ordsets)).

built_ins([!/0,< /2,= /2,=.. /2,=:= /2,=< /2,== /2,=\= /2,> /2,>= /2,@< /2,
@=< /2,@> /2,@>= /2,'C'/3,\== /2,arg/3,atom/1,atomic/1,close/1,compare/3,
copy_term/2,current_op/3,display/1,erase/1,fail/0,functor/3,ground/1,
integer/1,is/2,keysort/2,length/2,name/2,nl/0,nonvar/1,number/1,numbervars/3,
open/3,read/1,recorda/3,recorded/3,recordz/3,sort/2,statistics/2,true/0,
ttynl/0,ttyput/1,var/1,write/1]).

built_in(P/N):-built_ins(B),ord_member(P/N,B).

rec_comps(Clauses,Comps):-
	rec_comps(Clauses,_,Comps).
preds(Clauses,Preds):-
	rec_comps(Clauses,Preds,_).
rec_comps(Clauses,Preds,Comps):-
			process_clauses(Clauses,Arcs),
			preds_(Arcs,Preds),
			strong_comps(Preds,Arcs,Comps).

mut_rec(Pred1,Pred2,Arcs) :- conn(Pred1,Pred2,Arcs),conn(Pred2,Pred1,Arcs).
comp(Pred,Comp,Arcs) :- findall(Q, mut_rec(Pred,Q,Arcs),Comp1), 
			sort(Comp1,Comp).

strong_comps([],_,[]).
strong_comps([P|Preds],Arcs,Comps) :-
       comp(P,C,Arcs), 
       ((C=[], !, Comps=Comps1, Preds=P1) ; 
	     (Comps=[C|Comps1],ord_subtract(Preds,C,P1)) ),
       strong_comps(P1,Arcs,Comps1).

preds_(Arcs,Preds) :- findall(P,
	(member(dep(P,_),Arcs) ; member(dep(_,P),Arcs)),
		Preds1), sort(Preds1,Preds).


process_clauses(Clauses,Arcs):-
	process_clauses(Clauses,[],Arcs0),
	sort(Arcs0,Arcs).

process_clauses([],Arcs,Arcs).
process_clauses([Clause|Clauses],OldArcs,NewArcs):-
	make_arcs(Clause,OldArcs,Arcs),
	process_clauses(Clauses,Arcs,NewArcs).

conn(Pred1,Pred2,Arcs) :- conn(Pred1,Pred2,Arcs,[],_).
conn(Pred1,Pred2,Arcs,P,[Pred2,Pred1|P]) :- 
		\+member(Pred1,P),
		member(dep(Pred1,Pred2),Arcs).
conn(Pred1,Pred2,Arcs,P1,P) :- member(dep(Pred1,N),Arcs), 
		\+member(Pred1,P1), N \== Pred2,
		conn(N,Pred2,Arcs,[Pred1|P1],P).

make_arcs(end_of_file,Arcs,Arcs) :- !.
make_arcs((:- op(_Priority,_Type,_Char)),Arcs,Arcs):- !.
make_arcs((:- dynamic(_Name/_Arity)),Arcs,Arcs):- !.
make_arcs((:- public(_Name/_Arity)),Arcs,Arcs):- !.
make_arcs((:- mode(_Mode_Specs)),Arcs,Arcs):- !.
make_arcs((Head :- Body),Oldarcs,Temparcs) :- 
       !, nonvar(Body),!,ma((Head:-Body),Oldarcs,Temparcs).
make_arcs(Fact,Arcs,Arcs):- nonvar(Fact).

ma((Head :- B1,B2),Oldarcs,Temparcs) :- !, 
	ma((Head :- B1),[],Tarcs1),
	ma((Head :- B2),[],Tarcs2),
	append(Tarcs1,Tarcs2,Tarcs),
	append(Oldarcs,Tarcs,Temparcs).
ma((Head :- Body),Oldarcs,[dep(H/HArity,B/BArity)|Oldarcs]) :-
	functor(Body,B,BArity),\+ built_in(B/BArity),!,
	functor(Head,H,HArity).
ma(_,Oldarcs,Oldarcs).

%*********************************************************************
