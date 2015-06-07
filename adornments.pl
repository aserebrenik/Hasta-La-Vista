:- module(adornments,[get_maximal_prefix/3,ads_main/13]).
:- use_module(adorn, [code/3, decode/3, original_free_atom/3]).
:- use_module(atom, [comparison/1, built_in/1,
		     substitute_atom/4, fresh_all/2]).
:- use_module(apply, [apply/3]).
:- use_module(aux, [all_in/2, assert_list/2,my_ord_del_element/4,timer/1]).
:- use_module(check_clp,[check_clp/1]).
:- use_module(comma, [add_true/2, comma_eliminate_redundancy/2,
		      comma_member/2, drop_true/2]).
:- use_module(numvars, [diff_vars/2,frz/2, melt/2, varlist/2, varname/1]).
:- use_module(intervals, [interval_to_conjunct/2, extend/2, partition/3,
			  to_intervals/2, list_to_tree/3, simplify/2]).
:- use_module(find_int_pos, [find_int_pos/2]).
:- use_module(library(lists), [append/3,delete/3, member/2]).
:- use_module(library(ordsets), [list_to_ord_set/2, ord_subtract/3,
				 ord_union/3]).
:- use_module(rec, [rec/6]).
:- use_module(simplify_symb, [combine/2]).

partially_normalise_and_label(clause(Head,Body), 
		    clause(Head1,Body1)):-
	fresh_all(Head, Head_),
	user:iap(Head_-IntArgPos),
	length(IntArgPos, N), varlist(N,L),
	substitute_atom(Head, IntArgPos, L, Head1),
	Head =.. [_|Args], Head1 =.. [_|Args1],
	update_body(Args, Args1, Body, Body1).
partially_normalise_and_label([],[]).
partially_normalise_and_label([C|Cs],[C1|Cs1]):-
	copy_term(C,C_),
	partially_normalise_and_label(C_,C1),
	partially_normalise_and_label(Cs,Cs1).

:- meta_predicate update_body/4.
update_body([], [], B, B):- !.
update_body([Arg|Args], [Arg1|Args1], Body, Body1) :-
	(\+ varname(Arg1) ->
	    Body1 = Body0
	;
	    (var(Arg) ->
		Arg = Arg1, Body1 = Body0
	    ;
		Body1 = (Arg1 = Arg, Body0)
	    )
	),
	update_body(Args, Args1, Body, Body0).

get_maximal_prefix_candidate((Atom,Atoms), Algorithm, (Atom,Prefix)):-
	comparison(Atom), !,
	get_maximal_prefix_candidate(Atoms, Algorithm, Prefix).
get_maximal_prefix_candidate((Atom,Atoms), built_in, (Atom,Prefix)):-
	built_in(Atom), !,
	get_maximal_prefix_candidate(Atoms, built_in, Prefix).
get_maximal_prefix_candidate((Atom,Atoms), terminates, (Atom,Prefix)):-
	terminates(Atom), !,
	get_maximal_prefix_candidate(Atoms, terminates, Prefix).
get_maximal_prefix_candidate(_, _Algorithm, true).

get_maximal_prefix(clause(Head,Body), IO,
		   Algorithm, GAlgorithm, (Head1,Prefix)):-
	get_maximal_prefix(clause(Head,Body), Algorithm,
			   GAlgorithm, (Head1,Prefix1)),
	fresh_all(Head1, Head2),
	member((Head2, Ins, _), IO),
	Head =.. [_|Args],
	get_in_args(Args, Ins, 1, Args1),
	filter_prefix(Args1, Prefix1, Prefix).

get_in_args([], _, _, []).
get_in_args([Arg|Args], [I|Is], I, [Arg|InArgs]):- !,
	I1 is I+1, get_in_args(Args, Is, I1, InArgs).
get_in_args([_Arg|Args], Is, N, InArgs):- !,
	N1 is N+1, get_in_args(Args, Is, N1, InArgs).

filter_prefix_(_Args, true, true).
filter_prefix_(Args, (Cond, Prefix1), (Cond, Prefix2)):-
	diff_vars(Cond, Vars),
	all_in(Vars, Args), !,
	filter_prefix_(Args, Prefix1, Prefix2).
filter_prefix_(Args, (_Cond, Prefix1), Prefix2):-
	filter_prefix_(Args, Prefix1, Prefix2).	
filter_prefix(Args, Prefix1, Prefix2):-
	add_true(Prefix1, Prefix11),
	filter_prefix_(Args, Prefix11, Prefix2).

%%% intargpos - 
get_maximal_prefix(clause(Head,Body), Algorithm, GAlgorithm, (Head1,Prefix)):-
	fresh_all(Head,Head1),
	get_maximal_prefix_candidate(Body, Algorithm, Candidate),
	check_groundedness(Candidate, GAlgorithm, Prefix_),
	comma_eliminate_redundancy(Prefix_, Prefix).

check_groundedness(true, _, true).
check_groundedness((C,Cs), ground, (C,Ps)):-
	ground(C),!, check_groundedness(Cs, ground, Ps).
check_groundedness(_, ground, true).
check_groundedness(X, nonground, X).

get_maximal_prefixes_([], _Algo, _GAlgo, true).
get_maximal_prefixes_([Clause|Clauses], Algo, GAlgo, (Prefix, Prefixes)) :-
	get_maximal_prefix(Clause, Algo, GAlgo, Prefix),
	get_maximal_prefixes_(Clauses,Algo,GAlgo, Prefixes).
get_maximal_prefixes(Clauses, Algo, GAlgo, Prefixes):-
	get_maximal_prefixes_(Clauses, Algo, GAlgo, Prefixes_),!,
	comma_eliminate_redundancy(Prefixes_, Prefixes).

get_maximal_prefixes_([], _, _Algo, _GAlgo, true).
get_maximal_prefixes_([Clause|Clauses], IO, Algo, GAlgo, (Prefix, Prefixes)) :-
	get_maximal_prefix(Clause, IO,Algo, GAlgo, Prefix),
	get_maximal_prefixes_(Clauses,IO,Algo,GAlgo, Prefixes).
get_maximal_prefixes(Clauses, IO,Algo, GAlgo, Prefixes):-
	get_maximal_prefixes_(Clauses, IO,Algo, GAlgo, Prefixes_),!,
	comma_eliminate_redundancy(Prefixes_, Prefixes).

% section 4.2
find_adornments(Clauses, IO, simple, Adornments):-
	get_maximal_prefixes(Clauses, IO, comp, ground, Prefixes),!,
	partition(Clauses, Prefixes, Adornments).
find_adornments(_, _, _, []).

check_body_int((B1,_), IntArgPos):-
	fresh_all(B1, B), member((B-[_|_]), IntArgPos), !.
check_body_int((_,B2), IntArgPos):-
	check_body_int(B2, IntArgPos).
split_int_nonint([], _, [], []).
split_int_nonint([clause(Head,Body)|Clauses], IntArgPos,
		 [clause(Head,Body)|IntClauses], NonintClauses):-
	(fresh_all(Head, Head1), member((Head1-[_|_]), IntArgPos)
	; check_body_int(Body, IntArgPos))
	, !,
	split_int_nonint(Clauses, IntArgPos,IntClauses, NonintClauses).
split_int_nonint([(Head,I,O)|IOs], IntArgPos, [(Head,I,O)|IntIOs], NonintIOs):-
	fresh_all(Head, Head1),
	member((Head1-[_|_]), IntArgPos), !,
	split_int_nonint(IOs, IntArgPos,IntIOs, NonintIOs).
split_int_nonint([Head|Calls], IntArgPos, [Head|IntCalls], NonintCalls):-
	fresh_all(Head, Head1),
	member((Head1-[_|_]), IntArgPos), !,
	split_int_nonint(Calls, IntArgPos,IntCalls, NonintCalls).
split_int_nonint([X|Xs], IntArgPos, IntXs, [X|NonintXs]):-
	split_int_nonint(Xs, IntArgPos,IntXs, NonintXs).

% test_adornments verifies that at least one adornment is different
% from true; otherwise adroning is useless
% more precisely, test_adornments returns the non-true adornments

test_adornments([], []).
test_adornments([_Call-[true]|T], S):- !, test_adornments(T,S).
test_adornments([X|T], [X|S]):- !, test_adornments(T,S).

% filter_out_adornments removes adornments that cannot be used since
% they will contradict conditions in the calling clauses (all of them)




ads_main(Query, Clauses, Algorithm, Calls, IO,
	 AllAdornedClauses, AllAdornedCalls, AllAdornedIO,
	 Rec, MutRec, Preds, C1, C2):-

	find_int_pos(Clauses, IntArgPos),
	retractall(user:iap(_)),
	assert_list(iap,IntArgPos),

	split_int_nonint(Clauses, IntArgPos, 
			 IntegerClauses, NonintClauses),
	
	(IntegerClauses = [] ->
	    
	    AllAdornedClauses_ = Clauses,
	    AllAdornedCalls_ = Calls,
	    AllAdornedIO_ = IO,
	    Adornments = []
	;
	    split_int_nonint(IO, IntArgPos, IntIO, NonintIO),
	    split_int_nonint(Calls, IntArgPos,  IntCalls, NonintCalls),

	    partially_normalise_and_label(IntegerClauses, LClauses),
	    melt(LClauses, NewClauses),
	    find_adornments(LClauses, IO, Algorithm, Adornments2), 
	    test_adornments(Adornments2, Adornments1),

%%%%%  aux:writel(Adornments1),
	
	    (Adornments1 = [] ->
		%%%% retractall(user:iap(_)),
		AllAdornedClauses_ = Clauses,
		AllAdornedCalls_ = Calls,
		AllAdornedIO_ = IO,
		Adornments = []
	    ;
		Adornments = Adornments1,
		
		get_maximal_prefixes(LClauses, built_in, nonground, Prefixes),
		
%		write('Before Adorning'), nl,
%		aux:writel(NewClauses),

%		write('LClauses'), nl,
%		aux:writel(LClauses),

%		write('Prefixes'), nl,
%		aux:write(Prefixes),
		
		adorn_clauses(Adornments, NewClauses,
			      Prefixes, AdornedClauses),
	%	write('After Adorning'), nl,
	%	aux:writel(AdornedClauses),
		append(NonintClauses, AdornedClauses, AllAdornedClauses1),
	%	aux:writel(AllAdornedClauses1),
		adorn_up(AllAdornedClauses1, Adornments,
			 AllAdornedClauses2),
		remove_unreachable_clauses(Query, AllAdornedClauses2, 
					   AllAdornedClauses2,
					   AllAdornedClauses_))),
	
	

	rec(AllAdornedClauses_, Rec, _DirRec, MutRec, NonRec, Unfoldable),
	
	ord_union(Rec,NonRec,Preds),
	
	
	no_preds(Preds,Adornments,UsedAdornments, NoPredsAdornments),

	(var(AllAdornedIO_) ->
	    adorn_IO(IntIO, UsedAdornments, AdornedIO),
	    append(NonintIO, AdornedIO, AllAdornedIO_)
	; true),

	(var(AllAdornedCalls_) ->
	    adorn_calls(IntCalls, UsedAdornments, AdornedCalls),
	    append(NonintCalls, AdornedCalls, AllAdornedCalls_)
	; true),

	AllAdornedClauses = AllAdornedClauses_,
	
	adjust_adorned(Preds, AllAdornedCalls_, AllAdornedIO_,
		       AllAdornedCalls, AllAdornedIO),
	


	compute_c_1(Preds,NoPredsAdornments,Unfoldable,C1),
	compute_c_2(Preds,C1,C2).
%%%%%	aux:writel(AllAdornedClauses).

adorn_up([], _, []).
adorn_up([clause(H, B)|Clauses], Adornments, NewClauses) :-
	original_free_atom(H, FH, _),
	\+ member(FH-_, Adornments), !,
	get_maximal_prefix(clause(H, B), built_in, nonground, Prefix),
	findall(C,
		adorn_clause(clause(H, B), Adornments, Prefix, C),
		Cs),
	adorn_up(Clauses, Adornments, NewClauses1),
	append(Cs, NewClauses1, NewClauses).
adorn_up([clause(H, B)|Clauses], Adornments, [clause(H, B)|NewClauses]) :-
	adorn_up(Clauses, Adornments, NewClauses).

remove_unreachable_clauses(_, [], _, []).
remove_unreachable_clauses(Query, [clause(H,B)|Cs],
			   Clauses, [clause(H,B)|NCs]):-
	fresh_all(H,Q), Q = Query, !,
	remove_unreachable_clauses(Query, Cs, Clauses, NCs).
remove_unreachable_clauses(Query, [clause(H,B)|Cs],
			   Clauses, [clause(H,B)|NCs]):-
	original_free_atom(H, OA, Ad),
	\+ Ad = undefined, OA = Query, !,
	remove_unreachable_clauses(Query, Cs, Clauses, NCs).
remove_unreachable_clauses(Query, [clause(H,B)|Cs],
			   Clauses, [clause(H,B)|NCs]):-
	fresh_all(H, FH),
	member(clause(H1,B1), Clauses),
	\+ H1 = FH, 
	comma_member(FH, B1), !,
	remove_unreachable_clauses(Query, Cs, Clauses, NCs).
remove_unreachable_clauses(Query, [C|Cs], Clauses, NCs):-
	write('*** The following case is unreachable '),
	write(C), nl, 
	remove_unreachable_clauses(Query, Cs, Clauses, NCs).


adjust_adorned(Preds, AllAdornedCalls_, AllAdornedIO_,
	       AllAdornedCalls, AllAdornedIO) :-
	adjust_adorned(Preds, AllAdornedCalls_,AllAdornedCalls),
	adjust_adorned(Preds, AllAdornedIO_, AllAdornedIO).

adjust_adorned(_Preds, [], []).
adjust_adorned(Preds, [(P,I,O)|IOs_], [(P,I,O)|IOs]) :-
	member(P, Preds), !, 
	adjust_adorned(Preds, IOs_, IOs).
adjust_adorned(Preds, [(_P,_I,_O)|IOs_], IOs):- !,
	adjust_adorned(Preds, IOs_, IOs).
adjust_adorned(Preds, [Call|AllAdornedCalls_], [Call|AllAdornedCalls]) :-
	fresh_all(Call, C), member(C, Preds), !, 
	adjust_adorned(Preds, AllAdornedCalls_, AllAdornedCalls).
adjust_adorned(Preds, [_Call|AllAdornedCalls_], AllAdornedCalls):-
	adjust_adorned(Preds, AllAdornedCalls_, AllAdornedCalls).
	
/*
     ads_main([clause(p([X|Y],Z), (Z>0,Z1 is Z+1,p(Y,Z1),true))], simple,
          [p([_],a)], [(p(_,_), [1,2], [])],
	  AdornedClauses, ACalls, AIO, MutRec, Preds,C1, C2).
     ads_main([clause(p(X), (X>1,X<1000,X1 is -X*X,p(X1), true)),
           clause(p(X), (X< -1, X> -1000, X1 is X*X, p(X1), true))],
	   simple, [p(a)], [(p(_), [1], [])], 
	   AdornedClauses, ACalls, AIO, MutRec, Preds,C1, C2).
     ads_main([clause(q(X,Y), (X>Y, Z is X-Y, Y1 is Y+1, q(Z,Y1), true))],
          simple, [q(a,a)], [(q(_,_), [1,2], [])],
	  AdornedClauses, ACalls, AIO, MutRec, Preds,C1, C2).
     ads_main([clause(q(X,Y), (1+Y>0, X>Y, Z is X-Y, Y1 is Y+1, q(Z,Y1), true))],
          simple, [q(a,a)], [(q(_,_), [1,2], [])],
	  AdornedClauses, ACalls, AIO, MutRec, Preds,C1, C2).
     ads_main([clause(p(X), (X>0, X1 is X-1, p(X1), true))],
          simple,  [p(a)], [(p(_), [1], [])],
	  AdornedClauses, ACalls, AIO, MutRec, Preds,C1, C2).
     ads_main([clause(p(X), (X<100, X1 is X+1, p(X1), true))],
          simple,  [p(a)], [(p(_), [1], [])],
	  AdornedClauses, ACalls, AIO, MutRec, Preds,C1, C2).
     ads_main([clause(p(X), (X>1,Y is X*X,p(X,Y),true)),
           clause(p(X,Y), (X1 is X-1, p(X1), true))],
	  simple, [p(a), p(a,a)], [(p(_), [1], []), (p(_,_), [1,2], [])],
	  AdornedClauses, ACalls, AIO, MutRec, Preds,C1, C2).
     ads_main([clause(p(X,Y), (Y>1, X is Y*Y, p(Y),true)),
           clause(p(X), (X1 is X-1, p(X1,Y), true))],
	  simple, [p(a), p(a,a)], [(p(_), [1], []), (p(_,_), [1,2], [])],
	  AdornedClauses, ACalls, AIO, MutRec, Preds,C1, C2).
*/

adorn_calls([], _, []).
adorn_calls([Atom|Calls], Adornments,AdornedCalls):-
	findall(AdornedAtom,
		adorn_body((Atom, true), Adornments, (AdornedAtom, true)),
	       AdornedAtoms),
	adorn_calls(Calls, Adornments,AdornedCalls_),
	append(AdornedAtoms, AdornedCalls_, AdornedCalls).

adorn_IO([], _, []).
adorn_IO([(Atom,Inputs,Outputs)|IOs], Adornments, AdornedIOs):-
	findall((AdornedAtom,Inputs,Outputs),
		adorn_body((Atom, true), Adornments, (AdornedAtom, true)),
	       AdornedAtoms),
	adorn_IO(IOs, Adornments,AdornedIOs_),
	append(AdornedAtoms, AdornedIOs_, AdornedIOs).
	 
%% adorn_body(Body, Predicate, Adornments, NewBody) adorns the body
%% in all possible ways

adorn_body(true, _, true).
adorn_body((B1,B2), AllAdornments, (NB1,NB2)):-
	member(Predicate-Adornments, AllAdornments),
	fresh_all(B1,Predicate), 
	member(Adornment, Adornments),
	B1 =.. [P|Arguments],
	code(P,Adornment,NewPredicate),
	NB1 =.. [NewPredicate|Arguments],
	adorn_body(B2, AllAdornments, NB2).
adorn_body((B1,B2), AllAdornments, (B1,NB2)):-
	\+ (member(Predicate-_Adornments, AllAdornments),
	       fresh_all(B1,Predicate)),
	adorn_body(B2, AllAdornments, NB2).

adorn_clause(clause(Head, Body), Adornments, Pref, clause(Head1, Body1)):-
	adorn_body((Head, true), Adornments, (Head1, true)),
	check_consistency1(Head1, Pref, Conjunction),
	adorn_body(Body, Adornments, Body1),
	check_consistency(Body1, Conjunction).

adorn_clauses(_, [], _, []).
adorn_clauses(Adornments, [Clause|Clauses], (Pref,Prefs), AdornedClauses):-
	findall(AClause, adorn_clause(Clause, Adornments, Pref, AClause),
		AClauses),
	adorn_clauses(Adornments, Clauses, Prefs, AdornedClauses0),
	append(AClauses, AdornedClauses0, AdornedClauses).

check_consistency1(Head, Prefix, Constr):-
	Head =.. [HeadPred|_],

	to_intervals((Prefix, true), [_-[PrefixConj_]]),
	extend(PrefixConj_, PrefixConj),
	    
	(decode(HeadPred, _, Adornment) ->    
	    simplify(and(PrefixConj, Adornment), Constr_)
	    ;
	    simplify(PrefixConj,Constr_)),
	apply(Constr_, Head, Constr),
	check_clp(Constr).

check_consistency(Body, HPConj):-
	get_constraints(Body, Constraints),
	interval_to_conjunct(Constraints, Conj),
%%%%%	frz(and(Conj, HPConj), FC),
	extend(and(Conj, HPConj),Extended),
	frz(Extended,FC),
	simplify(FC, FCS),
	melt(FCS, MCS),
	check_clp(MCS).


get_constraints(true, []).
get_constraints((B1,B2), [Constr|Constrs]):-
	B1 =.. [B1Pred|_],
	decode(B1Pred, _P, Adornment), !,
	apply(Adornment, B1, Constr),
	get_constraints(B2, Constrs).
get_constraints((_B1,B2), Adornments):-
	get_constraints(B2, Adornments).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

no_preds(_, [], [], []) :- !.
no_preds([], A, [], A).
%%%%%%%% ADDED THE FOLLOWING CLAUSE %%%%%%%%%%%%%%%%%
no_preds([Pred|Preds],Adornments, UsedAdornments, NoPredsAdornments):-
	original_free_atom(Pred, _OPred, undefined),!,
	no_preds(Preds, Adornments, UsedAdornments, NoPredsAdornments).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
no_preds([Pred|Preds],Adornments,[OPred-[UsedAd]|UsedAdornments],
	 NoPredsAdornments):-
	original_free_atom(Pred, OPred, UsedAd),
	my_ord_del_element(Adornments, OPred-Ads, NewAdornments, [OPred-Ads]),
	delete(Ads, UsedAd, Ads1),
	no_preds(Preds, [OPred-Ads1|NewAdornments],
		 UsedAdornments, NoPredsAdornments).

preds_to_original_preds_and_adornments(AdornedPreds, List):-
	preds_to_original_preds_and_adornments_(AdornedPreds, List1),
	combine(List1, List).
preds_to_original_preds_and_adornments_([],[]).
preds_to_original_preds_and_adornments_([AP|APs], [P-[A1]|PAs]):-
	original_free_atom(AP,P,A),
	(A = undefined -> A1 = false ; A = A1),
	preds_to_original_preds_and_adornments_(APs,PAs).

compute_c_1([], [], [], []) :- !.
compute_c_1([Pred|Preds],[],[], [OPred-false|C1]) :- !,
	original_free_atom(Pred, OPred, _),
	compute_c_1(Preds, [], [], C1).
compute_c_1(Preds,NoPredsAdornments,Unfoldable, C1) :-
	preds_to_original_preds_and_adornments(Unfoldable,UnfoldableList),
	append(NoPredsAdornments,UnfoldableList,List1),
	other_nonadorned(Preds, List2),
	append(List1,List2,List),
	combine(List,Adornments),
	build_c_1(Adornments,C1).

other_nonadorned([], []).
other_nonadorned([Pred|Preds], [Pred-[false]|NP]):-
	original_free_atom(Pred, Pred, undefined), !,
	other_nonadorned(Preds, NP).
other_nonadorned([_Pred|Preds], NP):-
	other_nonadorned(Preds, NP).

build_c_1([], []).
build_c_1([Pred-Ads|Preds], [Pred-C1|C1s]):-
	list_to_tree(Ads,or,Tree),
	simplify(Tree, C1Var),
	apply(C1Var, Pred, C1),
	build_c_1(Preds,C1s).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% compute_c_2(Preds, C1, C2)
compute_c_2(Preds, C1, C2):-
	compute_c_2_(Preds, C1, C2_),
	sort(C2_, C2).
compute_c_2_([], _, []).
compute_c_2_([Pred|Preds], C1, [OPred-NExp|C2]):-
	original_free_atom(Pred, OPred, _),
	member(OPred-Exp, C1),!,
	frz(OPred-Exp, FOPred-FExp),
	simplify(not(FExp), NFExp),
	melt(FOPred-NFExp, OPred-NExp),
	compute_c_2_(Preds, C1, C2).
compute_c_2_([Pred|Preds], C1, [OPred-true|C2]):-
	original_free_atom(Pred, OPred, _),
	compute_c_2_(Preds, C1, C2).
