:- module(functors, [functors/2]).

:- use_module(atom, [built_in/1,fresh_all/2]).
:- use_module(numvars, [varname/1]).
:- use_module(library(lists), [append/3, member/2]).


% functors(Clauses, Functors)
functors(Clauses, Functors):-
	functors_(Clauses, [], Fs),
	sort(Fs, Functors).

functors_([], F, F).
functors_([clause(Head,Body)|Clauses], F, Functors):-
	!, functors_((Head,Body), F, F1),
	functors_(Clauses, F1, Functors).
functors_(true, F, F).
functors_((B1,B2), F, F2):-
	!, functors_(B1, F, F1),
	functors_(B2, F1, F2).
functors_(A=B, F1, F2) :-
	!, functors_args([A,B],F1,F2).
functors_(S, F, F) :-
	built_in(S). % but  not =
functors_(S, F, F) :-
	atomic(S). % predicate with arity 0
functors_(S, F1, F2):-
	compound(S),!, %%% and also \+ built_in(S)
	S =.. [_|Args],
	functors_args(Args,F1,F2).

functors_args([],F,F).
functors_args([Arg|Args],F1,F2) :-
	var(Arg),!,
	functors_args(Args,F1,F2).
functors_args([Arg|Args],F1,F2) :-
	varname(Arg),!,
	functors_args(Args,F1,F2).
functors_args([Arg|Args],F1,F2) :-
	atomic(Arg),!,
	functors_args(Args,F1,F2).
functors_args([Arg|Args],F1,F2) :-
	compound(Arg),!,
	fresh_all(Arg,F),
	(member(F,F1) ->
	    F3 = F1
	;
	    F3 = [F|F1]),
	Arg =.. [_|AArgs],
	functors_args(AArgs,F3,F4),
	functors_args(Args, F4, F2).


