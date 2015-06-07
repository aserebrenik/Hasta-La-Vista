:- module(bottom_up,[types/2,divide_into_levels/2]).
:- use_module(library(clpfd)).
:- use_module(library(lists)).
:- use_module(preds).
:- use_module(aux).

types(Clauses,Types):-
	divide_into_levels(Clauses,Levels).

divide_into_levels(Clauses,Levels):-
	preds(Clauses,Preds),
	length(Preds,N),
	def_vars(Preds,N,Vars),
	add_constraints(Clauses,Preds,Vars),
	sum(Vars,#=,Sum),
	labeling([minimize(Sum)],Vars),
	construct_levels(Vars,Preds,N,Levels).

def_vars([],_,[]).
def_vars([_Pred|Preds],N,[V|Vars]):-
	V in 0..N,
	def_vars(Preds,N,Vars).
	
add_constraints([],_,_).
add_constraints([(H:-B)|Clauses],
		Preds,Vars):-!,
	functor(H,N,A),
	functors(B,L0),
	sort(L0,L),
	add_comparison(N/A,L,Preds,Vars),
	add_constraints(Clauses,Preds,Vars).
add_constraints([_Fact|Clauses],
		Preds,Vars):-
	add_constraints(Clauses,Preds,Vars).

add_comparison(N/A,L,Preds,Vars):-
	nth(Nth,Preds,N/A),
	nth(Nth,Vars,V),
	add_for_each(L,Preds,Vars,N/A,V).

functors((B1,B2),L):-!,
	functors(B1,L1),
	functors(B2,L2),
	append(L1,L2,L).
functors(B,[N/A]):-
	functor(B,N,A),
	\+ built_in(N/A),!.
functors(_B,[]).

add_for_each([],_,_,_,_).
add_for_each([F|L],Preds,Vars,F,V):-!,
	add_for_each(L,Preds,Vars,F,V).
add_for_each([F|L],Preds,Vars,N/A,V):-
	nth(Nth,Preds,F),
	nth(Nth,Vars,VF),
	V #> VF,
	add_for_each(L,Preds,Vars,N/A,V).

construct_levels(Vars,Preds,N,Levels):-
	construct_levels(Vars,Preds,0,N,Levels).

construct_levels(_Vars,_Preds,I,N,[]):- I > N,!.
construct_levels([],_,_I,_N,[]):- !.
construct_levels(Vars,Preds,I,N,[Level|Levels]):- I =< N,
	findall(Pred,
		(nth(Nth,Vars,I),
		 nth(Nth,Preds,Pred)),
		Level),
	delete(Vars,I,Vars1),
	delete_l(Level,Preds,NewPreds),
	I1 is I+1,
	construct_levels(Vars1,NewPreds,I1,N,Levels).

delete_l([],L,L).
delete_l([H|Hs],L1,L3):-
	delete(L1,H,L2),
	delete_l(Hs,L2,L3).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



