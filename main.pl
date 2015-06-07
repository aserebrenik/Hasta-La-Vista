:- module(main, [main/4,not_enough_memory/1,good1/1,good2/1]).
:- use_module(adornments,[ads_main/13]).
:- use_module(adorn, [original_free_atom/3]).
:- use_module(atom, [built_in/1, comparison/1, fresh_all/2]).
:- use_module(aux, [all_unifiables/4, writel/1, timer/1]).
:- use_module(comma,[add_true/2,comma_append1/3]).
:- use_module(numvars, [diff_vars/2, frz/2, melt/2]).
:- use_module(simplify_symb, [simplify_symb/2]).
:- use_module(intervals, [simplify/2]).
:- use_module(read_program, [read_program/2]).
:- use_module(termination, [prove_termination/9]).
:- use_module(type_inference, [type_inference/7]).
:- use_module(filter,[filter_clauses/3,filter_undefined/3]).
:- use_module(library(lists), [append/3, member/2]).
:- use_module(library(ordsets), [ord_subtract/3]).

:- dynamic norm/2.
:- dynamic lm/2.
:- dynamic size_exp/2.
:- dynamic io/1. % io((delete(X,Y,Z),[2],[1,3]))
:- dynamic bad_body/1.
:- dynamic bad_clause/1.

not_enough_memory(TerminationCondition) :-
	retractall(user:bad_clause(_)),
	retractall(user:bad_body(_)),
	NiceQuery = false_eqv('[T1 $= f $| t $| not(T1) $| and(T1,T1) $| or(T1,T1) $| imp(T1,T1) $| eqv(T1,T1)]'),
	to_internal_representation(NiceQuery, Query),
	File = '../examples/theorem_prover_1',
	read_program(File, Clauses_),
	NewClauses = Clauses_,
	PredsWithoutDefs = [],
	IO = [(false_f(_),[1],[]), (false_and(_),[1],[]),
	      (false_not(_),[1],[]), (false_or(_),[1],[]),
	      (false_imp(_),[1],[]), (false_equiv(_),[1],[])],
	Calls = [false_f('OR'([t/0, f/0, not([2]), and([2,2]), or([2,2]), imp([2,2]), eqv([2,2])])),false_and('OR'([t/0, f/0, not([2]), and([2,2]), or([2,2]), imp([2,2]), eqv([2,2])])),false_or('OR'([t/0, f/0, not([2]), and([2,2]), or([2,2]), imp([2,2]), eqv([2,2])])),false_not('OR'([t/0, f/0, not([2]), and([2,2]), or([2,2]), imp([2,2]), eqv([2,2])])),false_imp('OR'([t/0, f/0, not([2]), and([2,2]), or([2,2]), imp([2,2]), eqv([2,2])])),false_eqv('OR'([t/0, f/0, not([2]), and([2,2]), or([2,2]), imp([2,2]), eqv([2,2])]))],
	main(Query,NewClauses,Calls,PredsWithoutDefs,IO,TerminationCondition).

main(File, NiceQuery, Share, TerminationCondition):-
	retractall(user:bad_clause(_)),
	retractall(user:bad_body(_)),
	to_internal_representation(NiceQuery, Query),
	read_program(File, Clauses_),
	type_inference(Clauses_, Query, Share, NewClauses,
		       Calls, IO, PredsWithoutDefs),
	main(Query,NewClauses,Calls,PredsWithoutDefs,IO,TerminationCondition).


good1(TerminationCondition) :- 
        retractall(user:bad_clause(_)),
	retractall(user:bad_body(_)),
	NiceQuery = d_div('[T1 $= 1 $| (-1) $| x $| power(T1,T1) $| \'+\'(T1,T1) $| \'*\'(T1,T1) $| \'/\'(T1,T1) ]', '[T2 $= x]', var),
	to_internal_representation(NiceQuery, Query),
	read_program('../examples/der_cc2',Clauses_),
	NewClauses = Clauses_,
	PredsWithoutDefs = [],
	IO = [(d_div(_,_,_),[1,2],[3]), (d_nondiv(_,_,_),[1,2],[3])],
	Calls = [d_div('OR'([x/0, +([2,2]), *([2,2]), '/'([2,2]),
	power([2,2])]),x,MAX), d_nondiv('OR'([x/0, +([2,2]), *([2,2]),
					      '/'([2,2]),power([2,2])]),
					x,MAX)],
	main(Query,NewClauses,Calls,PredsWithoutDefs,IO,TerminationCondition).

confex(TerminationCondition) :- 
        retractall(user:bad_clause(_)),
	retractall(user:bad_body(_)),
	NiceQuery = conf(list_of_vars),
	main('../examples/conf',NiceQuery,[],TerminationCondition).

good2(TerminationCondition) :- 
        retractall(user:bad_clause(_)),
	retractall(user:bad_body(_)),
	NiceQuery = d_div(var, var, '[T1 $= 1 $| (-1) $| x $| power(T1,T1) $| \'+\'(T1,T1) $| \'*\'(T1,T1) $| \'/\'(T1,T1) ]'),
	to_internal_representation(NiceQuery, Query),
	read_program('../examples/der_cc2',Clauses_),
	NewClauses = Clauses_,
	PredsWithoutDefs = [],
	IO = [(d_div(_,_,_),[3],[1,2]), (d_nondiv(_,_,_),[3],[1,2])],
	Calls = [d_div(MAX, MAX, 'OR'([1/0, 0/0, x/0, +([2,2]), *([2,2]), '/'([2,2]), power([2,2])])), d_nondiv(MAX, MAX, 'OR'([1/0, 0/0, x/0, +([2,2]), *([2,2]), '/'([2,2]),power([2,2])]))],
	main(Query,NewClauses,Calls,PredsWithoutDefs,IO,TerminationCondition).

good3(TerminationCondition) :- 
        retractall(user:bad_clause(_)),
	retractall(user:bad_body(_)),
	NiceQuery = d('[T1 $= 1 $| (-1) $| x $| power(T1,T1) $| \'+\'(T1,T1) $| \'*\'(T1,T1) $| \'/\'(T1,T1) ]', '[T2 $= x]', var),
	to_internal_representation(NiceQuery, Query),
	read_program('../examples/der_cc1',Clauses_),
	NewClauses = Clauses_,
	PredsWithoutDefs = [],
	IO = [(d(_,_,_),[1,2],[3])],
	Calls = [d('OR'([x/0, +([2,2]), *([2,2]), '/'([2,2]),power([2,2])]),x,'MAX')],
	main(Query,NewClauses,Calls,PredsWithoutDefs,IO,TerminationCondition).

        %%%% UBRAT'3
	%NewClauses = Clauses_,
	%PredsWithoutDefs = [],
	%IO = [(d(_,_,_),[1,2],[3])],
	%Calls = [d('OR'([x/0, +([2,2]), *([2,2]), '/'([2,2]),power([2,2])]),x,MAX)],
	%%%% KONEC UBRAT'3,
	
	%%%% UBRAT'4
	%NewClauses = Clauses_,
	%PredsWithoutDefs = [],
	%IO = [(d(_,_,_),[3],[1,2])],
	%Calls = [d(MAX, MAX, 'OR'([1/0, 0/0, x/0, +([2,2]), *([2,2]), '/'([2,2]), power([2,2])]))],
	%%%% KONEC UBRAT'4

	%%%% UBRAT'5
	%NewClauses = Clauses_,
	%PredsWithoutDefs = [],
	%IO = [(false(_),[1],[])],
	%Calls = [false('OR'([t/0, f/0, not([2]), and([2,2]), or([2,2]), imp([2,2]), eqv([2,2])]))],
	%%%% KONEC UBRAT'5


main(Query,NewClauses,Calls,PredsWithoutDefs,IO,TerminationCondition):-
	filter_clauses(NewClauses, Calls, Clauses__),
	(Clauses__ = NewClauses, PredsWithoutDefs = [] ->
	    Clauses = Clauses__ ;
	    filter_undefined(Clauses__, Clauses__, Clauses)),
	
	loop(Query, Clauses, Calls, IO, [], TerminationCondition1),
	%%%%timer('Loop '),
	!, frz(TerminationCondition1,FTC),
	simplify_symb_l(FTC, Simplified),
	melt(Simplified, TerminationCondition2),
	adjust_to_calls(TerminationCondition2, Calls, TerminationCondition),
	output_the_results(TerminationCondition),
	clean_up,
	timer('Total: ').

%filter_clauses(X, _, X).
%filter_undefined(X, _, X).
		 
to_internal_representation_([], []) :- !.
to_internal_representation_([var|NQs], ['[T1 $=MAX]'|Qs]):-
	!, to_internal_representation_(NQs, Qs).
to_internal_representation_([int|NQs], ['[T1 $=Int]'|Qs]):-
	!, to_internal_representation_(NQs, Qs).
to_internal_representation_([list_of_ints|NQs],
			   ['[T1 $= [] $| \'.\'(Int, T1)]'|Qs]):-
	!, to_internal_representation_(NQs, Qs).
to_internal_representation_([list_of_vars|NQs],
			   ['[T1 $= [] $| \'.\'(MAX, T1)]'|Qs]):-
	!, to_internal_representation_(NQs, Qs).
to_internal_representation_([NQ|NQs], [Q|Qs]):-
	to_internal_representation(NQ,Q), !,
	to_internal_representation_(NQs, Qs).
to_internal_representation_([NQ|NQs], [NQ|Qs]):-
	to_internal_representation_(NQs, Qs).
to_internal_representation(NQ,Q):-
	NQ =.. [Name|NQs],
	to_internal_representation_(NQs, Qs),
	Q =.. [Name|Qs].

loop(Query, Clauses, Calls, IO, OldAssumptions,
     TerminationCondition):-
	ads_main(Query, Clauses, simple, Calls, IO,
		 AdornedClauses, AdornedCalls,
		 AdornedIO, Rec, MutRec, Preds, C1, C2),
%	timer('Loop ADS '),
%	aux:writel(AdornedClauses),
	prove_termination(Preds, AdornedIO,
			  AdornedCalls, AdornedClauses,
			  Rec, MutRec, _Dictionary,
			  Assumptions, Predicates), !,
	%%% timer('Loop Termination Proof '),
	(Assumptions = false -> % suspect non-termination
	    all_false(Preds, AllFalse),
	    construct_or(C1,AllFalse,TerminationCondition)
	;
	    (Assumptions = [] ->
		construct_true_termination_condition(C1,TerminationCondition)
	    ;

		construct_and(C2,Predicates,C),
		construct_or(C1,C,TerminationCondition)
		)).


output_the_results(TerminationCondition):-
	split_terminates_doesnt(TerminationCondition, Terminates, Doesnt),
	pretty_output(Terminates, PrettyTerminates),
	pretty_output(Doesnt, PrettyDoesnt),
	
	(\+ Terminates = [] -> 
	    write('Termination is established for the following calls: '),nl,
	    writel(PrettyTerminates), nl
	;
	    true),
	(\+ Doesnt = [] ->
	    write('The program may not terminate for the following calls:'),
	    nl, writel(PrettyDoesnt), nl
	;
	    true).

pretty_output([], []) :- !.
pretty_output([A-C|As], [B-C|Bs]):- !,
	pretty_output(A, B),
	pretty_output(As, Bs).

pretty_output(A, B) :-
	A =.. [Name|As], pretty_output_(As, Bs), B =.. [Name|Bs].

pretty_output_([], []).
pretty_output_(['OR'(['[] / 0','.'(['Int',2])])|As], [list_of_ints|Bs]):-
	!, pretty_output_(As, Bs).
pretty_output_(['OR'(['[] / 0','.'(['MAX',2])])|As], [list_of_vars|Bs]):-
	!, pretty_output_(As, Bs).
pretty_output_(['MAX'|As], [var|Bs]):-
	!, pretty_output_(As, Bs).
pretty_output_(['Int'|As], [int|Bs]):-
	!, pretty_output_(As, Bs).
pretty_output_([A|As], [B|Bs]):-
	pretty_output(A,B),!,
	pretty_output_(As, Bs).
pretty_output_([A|As], [A|Bs]):-
	pretty_output_(As, Bs).

split_terminates_doesnt([], [], []).
split_terminates_doesnt([Pred-false|Preds], Terminates, [Pred|Doesnt]):-
	!, split_terminates_doesnt(Preds, Terminates, Doesnt).
split_terminates_doesnt([Pred-true|Preds], [Pred-true|Terminates], Doesnt):-
	!, split_terminates_doesnt(Preds, Terminates, Doesnt).
split_terminates_doesnt([Pred-TC|Preds], [Pred-STC|Terminates], Doesnt1):-
	simplify(not(TC), NTC),
	(NTC = false ->
	    STC = true, Doesnt1 = Doesnt
	;
	    STC = TC, Doesnt1 = [Pred-NTC|Doesnt]),
	split_terminates_doesnt(Preds, Terminates, Doesnt).

adjust_to_calls([], _, []).
adjust_to_calls([Predicate-Condition|TC1],
		Calls, TC2):-
	all_unifiables(Predicate,Calls,PCalls,Rest),
	adjust_to_calls(TC1, Rest, TC),
	append_conditioned(PCalls,Condition,TC,TC2).

append_conditioned([], _, L, L).
append_conditioned([PCall|PCalls],Condition,TC,[PCall-Condition|TC2]):-
	append_conditioned(PCalls,Condition,TC,TC2).

all_false(Preds, AllFalse):-
	all_false_(Preds, AF),
	sort(AF, AllFalse).
all_false_([], []).
all_false_([Predicate|Predicates], [OPredicate-false|C]):-
	original_free_atom(Predicate, OPredicate, _),
	all_false_(Predicates, C).

construct_or([],_,[]) :- !.
construct_or([P-Cond1|C1],C2,[P-or(Cond1,Cond2)|C]) :-
	member(P-Cond2, C2),
	construct_or(C1,C2,C).

construct_and([],_,[]) :- !.
construct_and([P-Cond1|C1],C2,[P-and(Cond1,Cond2)|C]) :-
	member(P-Cond, C2),
	remove_dash(Cond,Cond2),
	construct_and(C1,C2,C).
	
construct_true_termination_condition([],[]).
construct_true_termination_condition([P-_Cond1|C1],[P-true|C]):-
	construct_true_termination_condition(C1,C).

% fresh_variables is true if Expr2 has some variables that
% do not appear in Expr1
fresh_variables(Expr1, Expr2):-
	diff_vars(Expr1, Vars1), diff_vars(Expr2, Vars2),
	ord_subtract(Vars2, Vars1, [_|_]).

get_cond(true,true).
get_cond((B1,B2),and(B1,B)):-
	comparison(B1),!,
	get_cond(B2,B).
get_cond((_B1,_B2),true).


update_clauses([], _, []).
update_clauses([clause(Head,Body)|Clauses], Pred,
	       NewClauses):-
	copy_term(Pred, Pred1),
	member((Head-Condition), Pred1), !,
	remove_dash(Condition, Condition1),
	frz((Head, Condition1, Body), (H, C, B)),
	get_cond(B,C0),
	C1 = and(C,C0),
	simplify_symb(C1, C2), %computes 1*0 to 0
	simplify(C2, C3),      %simplifies -1>0 to false
	(C3 = false ->
	    update_clauses(Clauses, Pred, NewClauses)
	    ;
	    and_to_comma(C3, C4),
	    comma_append1(C4,B,C4B),
	    add_true(C4B,C4Bt),
	    melt(clause(H, C4Bt), Clause),
	    write('Updated Clause: '),
	    write(Clause), nl,
	    update_clauses(Clauses, Pred, Clauses1),
	    NewClauses = [Clause|Clauses1]).
update_clauses([clause(Head,Body)|Clauses], Pred,
	       [clause(Head,Body)|Clauses1]):-
	copy_term(Pred, Pred1),
	\+ member((Head-_Condition), Pred1),
	update_clauses(Clauses, Pred, Clauses1).

and_to_comma(and(B1, B2), (B11, B12)):- !,
	and_to_comma(B1, B11),
	and_to_comma(B2, B12).
and_to_comma(B, B).

remove_dash(X #> Y, X>Y).
remove_dash(X #< Y, X<Y).
remove_dash(X #= Y, X=Y).
remove_dash(X #>= Y, X>=Y).
remove_dash(X #=< Y, X=<Y).

remove_dash(and(B1, B2), and(B11, B12)):-
	remove_dash(B1, B11), remove_dash(B2, B12).

simplify_symb_l([], []).
simplify_symb_l([P-Exp|Ps], [P-Exp2|P2s]):-
	simplify(Exp, Exp2),
	simplify_symb_l(Ps, P2s).


clean_up :-
	retractall(io(_)),
	retractall(norm(_,_)),
	retractall(lm(_,_)),
	retractall(size_exp(_,_)),
	retractall(bad_body(_)),
	retractall(bad_clause(_)).
/*

loop([clause(q(X,Y), (X>Y, Z is X-Y, Y1 is Y+1, q(Z,Y1), true))],
     [q(i1,i2)], [(q(_,_),[1,2],[])], TC).
loop([clause(p(X), (X>1,X<1000,X1 is -X*X,p(X1), true)),
      clause(p(X), (X< -1, X> -1000, X1 is X*X, p(X1), true))],
     [p(i)], [(p(_), [1], [])], TC).
loop([clause(p(X), (X<100, X1 is X+1, p(X1), true))],
     [p(i)], [(p(_), [1], [])], TC).
loop([clause(p(X), (X>1,Y is X*X,p(X,Y),true)),
      clause(p(X,Y), (X1 is X-1, p(X1), true))],
     [p(i), p(i1,i2)], [(p(_), [1], []), (p(_,_), [1,2], [])],
     TC).
loop([clause(p(X,Y), (Y>1, X is Y*Y, p(Y),true)),
      clause(p(X), (X1 is X-1, p(X1,Y), true))],
     [p(i), p(i1,i2)], [(p(_), [1], []), (p(_,_), [1,2], [])], TC).
loop([clause(p([X|Y],Z), (Z>0,Z1 is Z+1,p(Y,Z1),true))], 
     [p([_],i)], [(p(_,_), [1,2], [])], TC).
loop([clause(p(X), (X>0, X1 is X-1, p(X1), true))],
     [p(i)], [(p(_), [1], [])], TC).
loop([clause(delete(X,[X|T],T), true),
      clause(delete(X,[H|T],[H|T1]),
	     (delete(X,T,T1), true)),
      clause(permute([],[]), true),
      clause(permute(L, [El|T]),
	     (delete(El,L,L1), permute(L1,T), true))],
     [delete(_,[_],_), permute([_],_)],
     [(delete(_,_,_), [2], [1,3]),
	       (permute(_,_), [1], [2])], TC).
loop([clause(p, (p, true))], [p], [(p, [], [])], TC).

main('../examples/quicksort',
     quicksort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'),
     [], TC).
main('../examples/quicksort',quicksort(list_of_ints, var), [], TC).

main('../examples/app',
     app('[T1 $= [] $| \'.\'(Int, T1)]','[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'),
     [], TC).
% non-termination is established for the following examples
main('../examples/app',
     app('[T2 $=MAX]','[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
main('../examples/app',
     app('[T2 $=MAX]','[T2 $=MAX]','[T2 $=MAX]'), [], TC).

main('../examples/permute',
     permute('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'),
     [], TC).
main('../examples/perm_app',
     perm('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'),
     [], TC).
main('../examples/zebra',
     zebra('[T1 $= MAX]', '[T1 $= MAX]', '[T1 $= MAX]'),
     [], TC).

% occur check!
main('../examples/strange',
     g, [], TC).


main('../examples/bad_append',
     app('[T1 $= [] $| \'.\'(Int, T1)]','[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'),
     [], TC).

% termination cannot be proved over {0,1}
main('../examples/various/ack', ack('[T1 $= 0 $| s(T1)]', '[T1 $=  0 $| s(T1)]', '[T2 $= MAX]'),
     [], TC).
% PROBLEM fails during the labeling
main('../examples/various/associative', normal_form('[T1 $= op(Int $| T1, Int $| T1)]', '[T2 $= MAX]'), [], TC).
% termination is established
main('../examples/various/credit', credit('[T1 $= Int]',  '[T2 $= MAX]'), [],
     TC).
% termination is established
main('../examples/dds/dds1.1', append('[T1 $= [] $| \'.\'(Int, T1)]','[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.01
% termination is established
main('../examples/dds/dds1.2', permute('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.01
% termination is established
main('../examples/dds/dds3.13', duplicate('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.0
% termination is established
main('../examples/dds/dds3.14', sum('[T1 $= [] $| \'.\'(Int, T1)]','[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.01
% termination is established
main('../examples/dds/dds3.15', merge('[T1 $= [] $| \'.\'(Int, T1)]','[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.0
%%% PROBLEM DOES NOT WORK - TYPE ANALYSIS LOOPS
main('../examples/dds/dds3.17', dis('[T2 $= 0 $| 1 $| or(T2,T2) $| and(T2,T2)]'), [], TC).
% termination is established
main('../examples/dds/dds3.8', reverse('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]','[T2 $=MAX]'), [], TC). 0.01

%%%% TESTED
main('../examples/dds/dds1.1', append('[T1 $= [] $| \'.\'(MAX, T1)]','[T1 $= [] $| \'.\'(MAX, T1)]','[T2 $=MAX]'), [], TC).
main('../examples/dds/dds1.1', append('[T2 $=MAX]','[T2 $=MAX]','[T1 $= [] $| \'.\'(MAX, T1)]'), [], TC).
main('../examples/apt/list', list('[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).
main('../examples/apt/fold', fold('[T1 $= Int]',  '[T1 $= [] $| \'.\'(Int, T1)]', '[T2 $=MAX]'), [], TC).
main('../examples/apt/lte', goal, [], TC).
main('../examples/apt/map', map('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
main('../examples/apt/member', member('[T1 $= Int]',  '[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).
% possibility of non-termination
main('../examples/apt/mergesort', mergesort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
main('../examples/apt/mergesort_ap', mergesort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]', '[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).
main('../examples/apt/naive_rev', reverse('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
main('../examples/apt/ordered', ordered('[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).
main('../examples/apt/overlap', overlap('[T1 $= [] $| \'.\'(Int, T1)]','[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).
main('../examples/apt/permutation', perm('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
main('../examples/apt/quicksort', qs('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
main('../examples/apt/select', select('[T2 $=MAX]', '[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
main('../examples/apt/subset', subset('[T1 $= [] $| \'.\'(Int, T1)]', '[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).
% possibility of non-termination (true)
main('../examples/apt/subset', subset('[T2 $=MAX]', '[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).
main('../examples/apt/sum', sum('[T2 $=MAX]', '[T2 $=MAX]', '[T1 $= 0 $| s(T1)]'), [], TC).


%%%% PLUEMER
% may not terminate (similar to DDV, in fact terminates)
main('../examples/plumer/mergesort_t', mergesort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
% termination established
main('../examples/plumer/pl1.1', append('[T1 $= [] $| \'.\'(Int, T1)]','[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.0
% termination established
main('../examples/plumer/pl1.1', append('[T2 $=MAX]','[T2 $=MAX]','[T1 $= [] $| \'.\'(MAX, T1)]'), [], TC).0.01
% termination established
main('../examples/plumer/pl1.2',  perm('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.04
% termination established
main('../examples/plumer/pl2.3.1', p('[T1 $= Int]', '[T2 $=MAX]'), [], TC).0.0
% may not terminate - in fact terminates; we do not discover it,
% since we assume that norm(a) = norm(b)
main('../examples/plumer/pl2.3.1', p('[T1 $= Atom]', '[T2 $=MAX]'), [], TC).
% may not terminate - in fact terminates; we do not discover it,
% since we assume that norm(a) = norm(b)
main('../examples/plumer/pl2.3.1', p('[T1 $= MAX]', '[T2 $=MAX]'), [], TC).
% may not terminate - does not terminate
main('../examples/plumer/pl3.1.1', a, [], TC).0.01
% may not terminate - in fact does not terminate
main('../examples/plumer/pl3.5.6', p('[T2 $=MAX]'), [], TC).0.01
% termination established
main('../examples/plumer/pl3.5.6a', p('[T2 $=MAX]'), [], TC).0.02
% may not terminate, in fact does not terminate, DDV used another version
main('../examples/plumer/pl4.01', append3('[T2 $=MAX]','[T2 $=MAX]','[T2 $=MAX]','[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).0.0
% termination established
main('../examples/plumer/pl4.01a', append3('[T2 $=MAX]','[T2 $=MAX]','[T2 $=MAX]','[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).0.01
% termination established
main('../examples/plumer/pl4.4.3', merge('[T1 $= [] $| \'.\'(Int, T1)]','[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.0
% termination established
main('../examples/plumer/pl4.4.6a', perm('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.01
% may not terminate, in fact does not terminate
main('../examples/plumer/pl4.5.2', s('[T1 $= Int $| \'+\'(T1, T1)]','[T2 $=MAX]'), [], TC).0.04
% termination established
main('../examples/plumer/pl4.5.3a', p('[T1 $= b]'), [], TC).0.0
% may not terminate - indead does not
main('../examples/plumer/pl4.5.3a', p('[T1 $= a]'), [], TC).0.0
% may not terminate - indead does not
main('../examples/plumer/pl4.5.3b', goal, [], TC).0.01
% may not terminate - indead does not
main('../examples/plumer/pl4.5.3c', goal, [], TC).0.0
% may not terminate - indead does not
main('../examples/plumer/pl5.2.2', turing('[T1 $= t(T2, Int, T2), T2 $= [] $| \'.\'(Int, T2)]', '[T3 $= Int]', '[T1 $= [] $| \'.\'(p(Int, Int, Int, Int, Int), T1)]', '[T3 $= MAX]'), [], TC).0.09
% termination established
main('../examples/plumer/pl6.1.1', qsort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.05
% termination is established
main('../examples/plumer/pl7.2.9', mult('[T1 $= 0 $| s(T1)]', '[T1 $=  0 $| s(T1)]', '[T2 $= MAX]'), [], TC).0.01
% may not terminate - indead does not
main('../examples/plumer/pl7.6.2a', reach('[T1 $= Int]', '[T1 $= Int]', '[T1 $= [] $| \'.\'(\'.\'(Int, Int), T1)]'), [], TC).0.04
% may not terminate - indead does not
main('../examples/plumer/pl7.6.2b', reach('[T1 $= Int]', '[T1 $= Int]', '[T1 $= [] $| \'.\'(\'.\'(Int, Int), T1)]', '[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).
% termination is established0.05
main('../examples/plumer/pl7.6.2c', reach('[T1 $= Int]', '[T1 $= Int]', '[T1 $= [] $| \'.\'(\'.\'(Int, Int), T1)]', '[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).
% may not terminate (like DDV) - in fact terminates
main('../examples/plumer/pl8.2.1', mergesort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.1
% may not terminate - should terminate
% error in DDV they also cannot prove it
main('../examples/plumer/pl8.2.1a', mergesort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).0.09
% termination established0.03
main('../examples/plumer/pl8.3.1', minsort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
% termination established0.05
main('../examples/plumer/pl8.3.1a', minsort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
% termination established0.01
main('../examples/plumer/pl8.4.1', even('[T1 $= 0 $| s(T1)]'), [], TC).
% termination established0.01
main('../examples/plumer/pl8.4.1', odd('[T1 $= 0 $| s(T1)]'), [], TC).
% termination can be proved if Domain is set to 0..3
% to analyse this example we add extra coefficitent to level mappings
% that is lm(a(X)) = a_0 + a_1*norm(X)0.07
main('../examples/plumer/pl8.4.2', e('[T1 $= [] $| \'.\'(a $| b $| c $| \'+\' $| \'*\' $| \'(\' $| \')\', T1)]','[T2 $=MAX]'), [], TC).

main('../examples/various/game', win('[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).


% MARIA
% PROBLEM - empty %%% gebruikt sort
main('../examples/maria/aiakl.pl',
     init_vars('[T1 $= [] $| \'.\'(T2=T2, T1),
	         T2 $= [] $| \'.\'(Int, T2)]',
		 '[T1 $= [] $| \'.\'(T2=T2, T1),
	         T2 $= [] $| \'.\'(Int, T2)]',
	       '[T2 $=MAX]', '[T2 $=MAX]'), [], TC).
main('../examples/maria/bid.pl', goal, [], TC).
% T2 should be char Ambiguous combination of operators use parentheses
main('../examples/maria/deriv.pl', d('[T1 $= Int $| T1+T1 $| T1-T1 $| T1*T1 $| T1/T1 $| T1^T1 $| -T1 $| exp(T1) $| log(T1)]','[T2 $=Int]', '[T3 $=MAX]'), [], TC).
% termination proved
main('../examples/maria/fib_t', fib('[T1 $= 0 $| s(T1)]','[T2 $=MAX]'), [], TC).
% termination proved
main('../examples/maria/fib.pl', fib('[T1 $= Int]','[T2 $=MAX]'), [], TC).

% does not terminate - established
main('../examples/maria/fib.pl', fib('[T1 $= MAX]','[T2 $=MAX]'), [], TC).
% There is no recursion in this program.
main('../examples/maria/grammar.pl', goal,  [], TC).
% termination established
main('../examples/maria/hanoiapp.suc', shanoi('[T1 $= 0 $| s(T1)]','[T1 $= Int]','[T1 $= Int]','[T1 $= Int]','[T2 $=MAX]'), [], TC).
main('../examples/maria/mmatrix.pl', mmultiply('[T1 $= [] $| \'.\'(T2=T2, T1),
T2 $= [] $| \'.\'(Int, T2)]','[T2 $= [] $| \'.\'(Int, T2)]','[T2 $=MAX]'), [], TC).
% termination established
main('../examples/maria/money.pl', money('[T2 $=MAX]', '[T2 $=MAX]','[T2 $=MAX]','[T2 $=MAX]','[T2 $=MAX]','[T2 $=MAX]','[T2 $=MAX]','[T2 $=MAX]'), [], TC).
% termination proved
main('../examples/maria/occur.pl', occurall('[T2 $= [] $| \'.\'(Int, T2)]',
					    '[T1 $= [] $| \'.\'(T2, T1),
					      T2 $= [] $| \'.\'(Int, T2)]',
					    '[T2 $=MAX]'), [], TC).
				


% termination established
main('../examples/various/simple_num.pl', p('[T1 $= Int]'), [], TC).
% termination established
main('../examples/various/simple_num.pl', q('[T1 $= Int]'), [], TC).
% may not terminate indead does not terminate
main('../examples/various/simple_num2.pl', p('[T1 $= Int]'), [], TC).
% may not terminate indead does not terminate
main('../examples/various/simple_num2.pl', q('[T1 $= Int]'), [], TC).
% may not terminate indead does not terminate
main('../examples/various/simple_num2.pl', r('[T1 $= Int]'), [], TC).
% may not terminate indead does not terminate
main('../examples/various/simple_num2.pl', s('[T1 $= Int]'), [], TC).


main('../examples/various/osc.pl', p('[T1 $= Int]'), [], TC).
% fails
main('../examples/euclides', p('[T1 $= Int]', '[T1 $= Int]', '[T1 $= Int]'), [], TC).
% termination established
main('../examples/various/pseudo_num.pl', p('[T1 $= [] $| \'.\'(Int, T1)]',
					    '[T1 $= Int]'), [], TC).
% termination established for q(Int,Int)-or(_68272=<_68273,and(1+_68273>0,_68272>_68273)) - to weak, but this is what we have
main('../examples/various/paper_example1.pl', q('[T1 $= Int]','[T1 $= Int]'),
     [], TC).
% termination established for q(Int,Int)-or(_283636=<_283637,and((_283637,1,inf),_283636>_283637)) - precise
main('../examples/various/paper_example2.pl', q('[T1 $= Int]','[T1 $= Int]'),
     [], TC).
% termination is discovered only for X=7 (and not for X=<7 as one might expect)
main('../examples/various/paper_example3.pl', p('[T1 $= Int]'), [], TC).

% possibility of non-termination, in fact terminates due to instantiation error
main('../examples/various/num1.pl', p('[T1 $= Int]'),  [], TC).

main('../examples/various/num2.pl', p('[T1 $= Int]'),  [], TC).
main('../examples/various/num3.pl', p('[T1 $= Int]'),  [], TC).
main('../examples/various/num4.pl', p('[T1 $= Int]'),  [], TC).


main('../examples/bratko_gcd1', gcd('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
%TC = [gcd('Int','Int','MAX')-or(_A=_B,and(_A>_B,and(_B>=1,_B* -1+_A>=1)))] ? 
main('../examples/bratko_gcd', gcd('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
main('../examples/st', st('[T1 $= Int]'), [], TC).


% sterling-shapiro chapter 8
% termination is established
main('../examples/SS/ss8.1', greatest_common_divisor('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% termination is established
main('../examples/SS/ss8.2', factorial('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% termination is established
main('../examples/SS/ss8.3', factorial('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% termination is established
main('../examples/SS/ss8.4', factorial('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% termination is established
main('../examples/SS/ss8.5', between('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% termination is established
main('../examples/SS/ss8.6a', sumlist('[T2 $= [] $| \'.\'(Int, T2)]','[T2 $=MAX]'), [], TC).
% termination is established
main('../examples/SS/ss8.6b', sumlist('[T2 $= [] $| \'.\'(Int, T2)]','[T2 $=MAX]'), [], TC).
% termination is established
main('../examples/SS/ss8.7a', inner_product('[T2 $= [] $| \'.\'(Int, T2)]','[T2 $= [] $| \'.\'(Int, T2)]','[T2 $=MAX]'), [], TC).
% termination established
main('../examples/SS/ss8.7b', inner_product('[T2 $= [] $| \'.\'(Int, T2)]','[T2 $= [] $| \'.\'(Int, T2)]','[T2 $=MAX]'), [], TC).
% termination established
main('../examples/SS/ss8.8', area('[T2 $= [] $| \'.\'(\',\'(Int,Int), T2)]','[T2 $=MAX]'), [], TC).
% termination is established
main('../examples/SS/ss8.9', maxlist('[T2 $= [] $| \'.\'(Int, T2)]','[T2 $=MAX]'), [], TC).
% termination established
main('../examples/SS/ss8.10', length('[T2 $=MAX]', '[T1 $= Int]'), [], TC).
% termination established
main('../examples/SS/ss8.11', length('[T2 $= [] $| \'.\'(Int, T2)]','[T2 $=MAX]'), [], TC).
% termination established
main('../examples/SS/ss8.12', range('[T1 $= Int]','[T1 $= Int]', '[T2 $=MAX]'), [], TC).


% PROBLEM - integer overflow
main('../examples/SS/gcd', gcd('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% can be shown that it cannot be proved (established only for $1=$2)
main('../examples/SS/gcd1', gcd('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% can be shown that it cannot be proved (established only for $1=$2)
main('../examples/SS/gcd2', gcd('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
main('../examples/SS/gcd3', gcd('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).

% PROBLEM - type analysis empty
main('../examples/DLSS/6.10', gcd('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% PROBLEM - type analysis empty
main('../examples/DLSS/6.11', p('[T1 $= Int]', '[T1 $= Int]'), [], TC).
% termination established 0.01
main('../examples/DLSS/p141', p('[T1 $= Int]'), [], TC).

% PROBLEM - representation error - clpfd integer overflow (second loop iteration) ; problem - type inference for porgrams with negation
main('../examples/P/p31', is_prime('[T1 $= Int]'), [], TC).
% termination is established
main('../examples/P/p32', gcd('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% termination is established
main('../examples/P/p33', coprime('[T1 $= Int]', '[T1 $= Int]'), [], TC).
%  termination is established
main('../examples/P/p34', totient_phi('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% actual termination depends on cut; we suspect non-termination
% very-very slow
main('../examples/P/p35', prime_factors('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% PROBLEM depends on p35
main('../examples/P/p36', prime_factors_mult('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% PROBLEM depends on p36
main('../examples/P/p37', totient_phi_2('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% PROBLEM depends on p37
main('../examples/P/p38', totient_test('[T1 $= Int]'), [], TC).
% PROBLEM depends on p31
main('../examples/P/p39', prime_list('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% PROBLEM depends on p31
main('../examples/P/p40', goldbach('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% PROBLEM depends on p31
main('../examples/P/p41', goldbach_list('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).


% APT book chapter 9
% termination established
main('../examples/APT/between', between('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% termination established
main('../examples/APT/delete', delete('[T1 $= Int]', '[T2 $= void $| tree(Int, T2, T2)]', '[T3 $=MAX]'), [], TC).
% termination established
main('../examples/APT/factorial', fact('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% termination established
main('../examples/APT/in_tree', in_tree('[T1 $= Int]', '[T2 $= void $| tree(Int, T2, T2)]'), [], TC).
% termination established
main('../examples/APT/insert', insert( '[T1 $= Int]','[T2 $= void $| tree(Int, T2, T2)]', '[T3 $=MAX]'), [], TC).
% termination established
main('../examples/APT/length1', length('[T2 $= [] $| \'.\'(Int, T2)]','[T2 $=MAX]'), [], TC).
% termination established
main('../examples/APT/maximum', max('[T1 $= Int]', '[T1 $= Int]', '[T2 $=MAX]'), [], TC).
% termination established
main('../examples/APT/ordered', ordered('[T2 $= [] $| \'.\'(Int, T2)]'), [], TC).
%%% to look how should it be run. in any case - no recursion
%%% main('../examples/APT/queue', setup
% termination establishe
main('../examples/APT/quicksort', qs('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
% termination established
main('../examples/APT/quicksort_acc', qs_acc('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]','[T2 $=MAX]'), [], TC).
% termination established0.07
main('../examples/APT/quicksort_dl', qs('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).
% termination is established
main('../examples/APT/search_tree', is_search_tree('[T2 $= void $| tree(Int, T2, T2)]'), [], TC).
% termination is established
main('../examples/APT/tree_minimum', minimum('[T2 $= void $| tree(Int, T2, T2)]','[T2 $=MAX]'), [], TC).


% may not terminate; indead termination depends on cut (!)
% and for negative N does not terminate at all - termination condition
% is N >= 0
main('../examples/hanoi', hanoi('[T1 $= Int]'), [], TC).
% termination established
main('../examples/hanoi1', hanoi('[T1 $= Int]'), [], TC).
% may not terminate no reasonable condition is generated
main('../examples/hanoi2', hanoi('[T1 $= Int]'), [], TC).
main('../examples/hanoi2', move('[T1 $= Int]', '[T2 $= left]', '[T1 $= centre]', '[T1 $= right]'), [], TC).
main('../examples/hanoi2', move('[T1 $= Int]', '[T2 $= Int]', '[T1 $= Int]', '[T1 $= Int]'), [], TC).

% termination is established, unreachability of one of the cases of move is
% shown
main('../examples/hanoi3', hanoi('[T1 $= Int]'), [], TC).

% termination is established0.19 (jeruzalem)
main('../examples/hanoi_jrfisher', move('[T1 $= MAX]', '[T2 $= MAX]', '[T1 $= MAX]', '[T1 $= MAX]'), [], TC).

main('../examples/depth', depth('[T1 $= 0 $| s(T1)]','[T2 $=Int]'),[], TC).

main('../examples/test1', p('[T2 $=Int]'), [], TC).
% termination established
main('../examples/primes', primes('[T1 $= Int]','[T2 $=MAX]'), [], TC).
% may not terminate, indead does not terminate (produces infinitely many answers)
main('../examples/pythag', pythag('[T2 $=MAX]', '[T2 $=MAX]', '[T2 $=MAX]'), [], TC).
% termination established
main('../examples/pythag', minus('[T2 $=Int]', '[T2 $=Int]', '[T2 $=MAX]'), [], TC).
% may not terminate (indead) - no condition is possible 
main('../examples/triangle', triangle('[T1 $= Int]','[T2 $=MAX]'), [], TC).
% may not terminate (indead) termination condition is not inferred
% since the adrornments are or-adornments; infact no termination condition
% is possible, similarly to triangle
main('../examples/exp', exp('[T1 $= Int]','[T1 $= Int]','[T2 $=MAX]'), [], TC).

% termination is established
main('../examples/t1', p, [], TC).
% termination is established
main('../examples/t2', p('[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).
% termination is established
main('../examples/doesnotunify', p('[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).

% Termination is established
main('../examples/dldf', depthfirst2('[T1 $= Atom]', '[T2 $=MAX]', '[T1 $= Int]'), [], TC).
% Termination is established
main('../examples/dldf1', depthfirst2('[T1 $= Atom]', '[T2 $=MAX]', '[T1 $= Int]'), [], TC).
% Termination is established
main('../examples/forwardfib', fib3('[T1 $= Int]', '[T2 $=MAX]'), [], TC).

% termination is established
%%% *** The following case is unreachable clause(q_in(#VAR(0),-inf,-1)(_73228),(_73228<0,_73216 is _73228-1,q_in(#VAR(0),-inf,-1)(_73216),true))
main('../examples/up_down', p('[T1 $= Int]'), [], TC).

%%%%  while adorning, clauses with < in the head are not produced since
%%%% arg(X,_,_) assumes X>0
main('../examples/OKeefe/ground2', ground('[T1 $= MAX]'), [], TC).

% termination is established time 0.05
main('../examples/OKeefe/fib1', fib('[T1 $= Int]', '[T2 $=MAX]'), [], TC).

main('../examples/OKeefe/caa', count_atom_arguments('[T1 $= Int]', '[T1 $= MAX]', '[T1 $= Int]', '[T1 $= MAX]'), [], TC).

% Covington Nute Vellino termination is proved
main('../examples/fib_cnv.pl', fib('[T1 $= Int]','[T2 $=MAX]'), [], TC).

% DLSS 6.5 termination is established
main('../examples/mod', mod('[T1 $= Int]','[T1 $= Int]','[T2 $=MAX]'), [], TC).
% DLSS 6.3 termination is established
main('../examples/dlss6.3',r('[T1 $= Int]'), [], TC).


%Total:  0.03
%TC = [loop('Int','Int','Int','Int','Int')-or(_A>0,and(_A=<0,_A>=1))] 
main('../examples/loop',loop('[T1 $= Int]','[T1 $= Int]','[T1 $= Int]','[T1 $= Int]','[T1 $= Int]'), [], TC).
% termination established 0.02
main('../examples/interval',interval('[T1 $= Int]','[T1 $= Int]','[T1 $= MAX]'), [], TC).

main('../examples/rotateL',rotateL('[T1 $= Int]','[T2 $= [] $| \'.\'(Int, T2)]','[T1 $= MAX]'), [], TC).

main('../examples/mortgage', mortgage('[T1 $= Int]','[T1 $= Int]','[T1 $= Int]','[T1 $= Int]','[T1 $= MAX]'), [], TC).

main('../examples/dist/dist_s', dist('[T1 $= x $| \'+\'(T1,T1) $| \'*\'(T1,T1)]').


%%%%%%%%%%%%%% VALENCIA

main('../valencia/ackermann.pl', ackermann('[T1 $= 0 $| s(T1)]', '[T1 $= 0 $| s(T1)]','[T1 $= MAX]'), [], TC).

main('../valencia/average.pl', average('[T1 $= 0 $| s(T1)]', '[T1 $= 0 $| s(T1)]','[T1 $= MAX]'), [], TC).

main('../valencia/kay4.pl', kay4('[T1 $= Int]'), [], TC).

main('../valencia/log2a.pl', log2('[T1 $= 0 $| s(T1)]', '[T1 $= MAX]'), [], TC).

main('../valencia/log2b.pl', log2('[T1 $= 0 $| s(T1)]', '[T1 $= MAX]'), [], TC).

main('../valencia/mapcolor.pl', color_map('[T1 $= [] $| \'.\'(region(Int, MAX, T2), T1), T2 $= [] $| \'.\'(MAX, T2)]', '[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).
main('../valencia/mapcolor1.pl', color_map('[T1 $= emptylist $| cons(region(Int, MAX, T2), T1), T2 $= [] $| \'.\'(MAX, T2)]', '[T1 $= [] $| \'.\'(Int, T1)]'), [], TC).

main('../valencia/mergesort.pl', mergesort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'), [], TC).

main('../valencia/numbervars.pl', numvars('[T2 $=MAX]','[T1 $= Int]','[T2 $=MAX]'), [], TC).

main('../valencia/numbervars.pl', numvars2('[T2 $=MAX]','[T1 $= Int]','[T2 $=MAX]'), [], TC).

main('../valencia/shapes.pl', shapes('[T1 $= [] $| \'.\'(T2, T1), T2 $= [] $| \'.\'(Int, T2)]','[T2 $=MAX]'), [], TC).

main('../valencia/tautology.pl', tautology('[T1 $= \'+\'(T1,T1) $| \'*\'(T1,T1) $| \'-\'(T1) $| if(T1,T1) $| iff(T1,T1) $| sequent(T1,T1)]'), [], TC).

main('../valencia/tautology1.pl', tautology('[T1 $= \'+\'(T1,T1) $| \'*\'(T1,T1) $| \'-\'(T1) $| if(T1,T1) $| iff(T1,T1) $| sequent(T1,T1)]'), [], TC).

%%%%%%%%%%%%%% VALENCIA ADAPTED

main('../valencia/average_num.pl', average('[T1 $= 0 $| s(T1)]', '[T1 $= 0 $| s(T1)]','[T1 $= MAX]'), [], TC).

%%%%%%%%%%%%% VALENCIA AS

main('../valencia/as_collection/factorial', factorial1('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
main('../valencia/as_collection/factorial', factorial2('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
main('../valencia/as_collection/factorial', factorial3('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
main('../valencia/as_collection/fib', fib1('[T1 $= Int]', '[T2 $=MAX]'), [], TC).
main('../valencia/as_collection/fib', fib2('[T1 $= Int]','[T2 $=MAX]'), [], TC).
main('../valencia/as_collection/hanoi', move('[T1 $= MAX]', '[T2 $= MAX]', '[T1 $= MAX]', '[T1 $= MAX]'), [], TC).
main('../valencia/as_collection/primes', primes('[T1 $= Int]','[T2 $=MAX]'), [], TC).
main('../valencia/as_collection/totient', totient_phi(int, var), [], TC).

main('../valencia/as_collection/salvatore', p(int), [], TC).
main('../valencia/as_collection/salvatore1', p(int), [], TC).
main('../valencia/as_collection/salvatore2', p(int), [], TC).

main('../examples/loop1',loop('[T1 $= 0 $| s(T1)]','[T1 $= 0 $| s(T1)]','[T1 $= 0 $| s(T1)]'), [], TC). 
main('../examples/loop2',loop('[T1 $= 0 $| s(T1)]','[T2 $= f(T1,T1), T1 $= 0 $| s(T1)]'), [], TC).
main('../examples/loop1ab',loopa('[T1 $= 0 $| s(T1)]','[T1 $= 0 $| s(T1)]','[T1 $= 0 $| s(T1)]'), [], TC). 
main('../examples/loop2ab',loopa('[T1 $= 0 $| s(T1)]','[T2 $= f(T1,T1), T1 $= 0 $| s(T1)]'), [], TC).
% type inference *** OVERFLOW 755 *** Stack limits exceeded
% instead of type inference use UBRAT'1
*_2,1 *_1,1 *_0,1 d_div_1,2
/_0,2 /_2,1 /_1,1 d_div_0,1
d_nondiv_1,2 power_1,1 power_0,1
main('../examples/der_cc2',d_div('[T1 $= 1 $| (-1) $| x $| power(T1,T1) $| \'+\'(T1,T1) $| \'*\'(T1,T1) $| \'/\'(T1,T1) ]', '[T2 $= x]', var), [], TC).

% instead of type inference use UBRAT'2
*_2,1 *_1,1 *_0,1 +_1,1 +_2,1
d_div_3,1 d_div_0,1 d_nondiv_3,1
main('../examples/der_cc2',d_div(var, var, '[T1 $= 1 $| (-1) $| x $| power(T1,T1) $| \'+\'(T1,T1) $| \'*\'(T1,T1) $| \'/\'(T1,T1) ]'), [], TC).

% may not terminate UBRAT'3
main('../examples/der_cc1',d('[T1 $= 1 $| (-1) $| x $| power(T1,T1) $| \'+\'(T1,T1) $| \'*\'(T1,T1) $| \'/\'(T1,T1) ]', '[T2 $= x]', var), [], TC).

% may not terminate UBRAT' 4
main('../examples/der_cc1',d(var, var, '[T1 $= 1 $| (-1) $| x $| power(T1,T1) $| \'+\'(T1,T1) $| \'*\'(T1,T1) $| \'/\'(T1,T1) ]'), [], TC).

% may not terminate UBRAT' 5
main('../examples/theorem_prover', false('[T1 $= f $| t $| not(T1) $| and(T1,T1) $| or(T1,T1) $| imp(T1,T1) $| eqv(T1,T1)]'), [], TC).

% UBRAT' 6
main('../examples/theorem_prover_1', false_eqv('[T1 $= f $| t $| not(T1) $| and(T1,T1) $| or(T1,T1) $| imp(T1,T1) $| eqv(T1,T1)]'), [], TC).
*/









