:- module(calls,[find_calls/3]).
:- use_module(library(ordsets)).
:- use_module(library(lists)).

find_calls(Query,Clauses,Calls):-
	find_calls([Query],Clauses,[],Calls).

find_calls([],_,Calls,Calls).
find_calls([Q|Qs],Clauses,OldCalls,NewCalls):-
	gen_calls(Q,Clauses,Calls),
	append(Calls,OldCalls,Calls0),
	find_calls(Qs,Clauses,Calls0,NewCalls).

gen_calls(Q,Clauses,Calls):-
	functor(Q,N,A),
	functor(Head,N,A),
	findall((Head:-Body),
		(member((Head:-Body),Clauses)),
		RelevantClauses),
	create_calls(Q,RelevantClauses,[],Calls).

create_calls(_,[],Calls,Calls).
create_calls(Q,[(Head:-Body)|RelevantClauses],
	     OldCalls,NewCalls) :-
	create_from_one_rule(Q,(Head:-Body),Calls0),
	append(Calls0,OldCalls,Calls),
	create_calls(Q,RelevantClauses,Calls,NewCalls).

create_from_one_rule(Q,(Head:-Body),
		     Calls):-
	unify(Q,Head),
	check_body(Body,Calls).


%%% unify
unify(Term1,Term2).


check_body((B1,B2),(B1,Calls)):-
	!, type(B1,T1), unify(B1,T1), check_body(B2,Calls).
check_body(B,B).


	

