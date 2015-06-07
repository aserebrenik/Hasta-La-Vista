:- module(filter,[filter_clauses/3,filter_undefined/3]).
:- use_module(library(lists), [append/3, member/2]).
:- use_module(atom, [built_in/1, fresh_all/2]).

% filtering is needed since there may be clauses in Clauses_
% that are not actually used, i.e., the corrresponding calls do
% not appear among the Calls

filter_clauses([], _, []).
filter_clauses([clause(Head,Body)|Clauses_], Calls,
	       [clause(Head,Body)|Clauses]):-
	copy_term(Head, H), 
	match(H, Calls), !,
	filter_clauses(Clauses_, Calls, Clauses).
filter_clauses([Clause|Clauses_], Calls, Clauses):-
	write('*** The following clause is unreachable ***'), nl,
	write(Clause), nl, 
	filter_clauses(Clauses_, Calls, Clauses).

match(Head, Calls):- member(Head, Calls), !.
match(Head, Calls):- fresh_all(Head, H), member(H, Calls),
	Head =.. [_|HArgs], H =.. [_|CArgs],
	match_args(HArgs, CArgs).
%%% PATCH for example log2b Type analysis does not infer calls to small
match(small(_),_).
%%% END PATCH

match_args([], []).
match_args([Arg1|Args1], [Arg2|Args2]):-
	match_type(Arg1, Arg2),
	match_args(Args1, Args2).

match_type(_, N) :- integer(N), !. % can we do better?
match_type(_, 'MAX') :- !.
match_type(A,A/0) :- atomic(A).
match_type(V, _)     :- var(V).
match_type(N, 'Int') :- integer(N).
%%% PATCH only to handle example valencia/log2b
%%% the problem is that the  type analysis infers
%%% log2('OR'([s([2]),'Int']),'Int',s(['Int']),'MAX')
%%% instead of
%%% log2('OR'([s([2]),'Int']),'OR'([s([2]),'Int']),s(['Int']),'MAX')
match_type(s(s(_)), 'Int').
%%% END PATCH
match_type(C, 'Atom'):- atom(C).
match_type([], 'List') :- !.
match_type([_|_], 'List') :- !.
match_type([_|_], 'ListOne') :- !.
match_type(C, 'OR'(Args)):-
	match_some(C, Args).
match_type(A, T)     :-
	atom(A), atom(T), !, 
	atom_chars(A, AC), atom_chars(T, TC),
	append(AC,[32,47,32,48],TC).
match_type(C, Type)  :- compound(C),
	C =.. [F|CArgs], Type =.. [F,TArgs],
	match_args(CArgs, TArgs).

match_some(C, [Arg|_]):- match_type(C, Arg).
match_some(C, [_|Args]):- match_some(C, Args).


% filter_undefined replaces H:-B1,r,B2 with H:-B1 if r is undefined

filter_undefined(true, _, true) :- !.
filter_undefined((B1,B2), Clauses0, (B1,B3)):-
	built_in(B1), !, filter_undefined(B2, Clauses0, B3).
% (fail, true) and not just true, since we assume that the body of a clause
% always ends with true
filter_undefined((B1,_B2), Clauses0, (fail, true)):-
	fresh_all(B1, B), \+ member(clause(B,_), Clauses0),!.
filter_undefined((B1,B2), Clauses0, (B1,B3)):-
	filter_undefined(B2, Clauses0, B3).

filter_undefined([], _, [])            :- !.
filter_undefined([clause(H,B)|Clauses], Clauses0,
		 [clause(H,B1)|Clauses1]):-
	filter_undefined(B,Clauses0,B1),
	(\+ (H,B) = (H,B1) ->
	    write('*** Clause '), write(clause(H,B)),
	    write(' was replaced by '), write(clause(H,B1)),
	    write(' ***'), nl
	    ;
	    true),
	filter_undefined(Clauses, Clauses0, Clauses1).

