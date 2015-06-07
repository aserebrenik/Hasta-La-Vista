:- use_module(library(lists)).
:- use_module(library(ordsets)).
:- use_module(aux).
:- use_module(comma).
:- use_module(numvars).
:- use_module(transform).

:- dynamic simplify/1.

%%% combine(Query,Clauses,CombinedClauses).
combine(Query, Clauses, NewClauses):-
	copy_term(Clauses, CClauses),
	divide(Query, CClauses, DividedClauses),
	findall(Clause,
	   (copy_term(Query,QQuery),
	    pick_one(QQuery, DividedClauses,OneSelection),
	    unify_with_query(QQuery,OneSelection,Clause)),
	NewClauses).

divide((Q,Qs),Clauses,[DC|DividedClauses]) :-
	findall(C,
	   (get_predicate_of_an_atom(Q,N,A),
	    make_dummy_head(H,N,A),
	    member_by_head(H,Clauses,C)),
            DC),
	divide(Qs,Clauses,DividedClauses).
divide(true,_,[]).

member_by_head(H,[(H:-B)|_],(H:-B)).
member_by_head(H,[H|_],H).
member_by_head(X,[_|T],C):-member_by_head(X,T,C).

get_predicate_of_an_atom(Q,N,A) :- functor(Q,N,A).
make_dummy_head(H,N,A):-functor(H,N,A).

read_program(File, Clauses):-
	see(File),
	read_loop([],Clauses0), seen,%timer('After Reading '),
	transform(Clauses0,Clauses)%, timer('After Transformation ')
	.

read_loop([end_of_file|L],L):- !.
read_loop(L1,L2) :-
	read(X),
	read_loop([X|L1],L2).

pick_one(_,[],[]).
pick_one((Q,Query),[[]|Classes], [Q|Representative]) :-!,
	pick_one(Query,Classes,Representative).
pick_one((_,Query),[C|Classes], [R|Representative]) :-
	member(R,C),
	pick_one(Query,Classes,Representative).

build_body(true,[],true).
build_body((Q,Qs),[Q|Representative],Bodies):-
	build_body(Qs,Representative,Bodies).
build_body((Q,Qs),[(Q:-Body)|Representative],(Body,Bodies)):-
	build_body(Qs,Representative,Bodies).

unify_with_query(Query,Representative,Clause):-
	build_body(Query,Representative,Body),
	drop_true(Query,Head),
	(Body = true ->
		Clause = Head
	  ;
		(normal_form(Body,NormalisedBody),
	         drop_true(NormalisedBody,NB),
	         Clause = (Head:-NB))).	


%*********************************************************************
%% valid only for well-moded programs
%% otherwise variables can be further instantiated
simplify_tuples([],_,[]).
simplify_tuples([Tuple|Tuples],Modes,[NewTuple|NewTuples]):-
	find_path(Tuple,Modes,NewTuple),
	simplify_tuples(Tuples,Modes,NewTuples).

find_path(Tuple,Modes,NewTuple):-
	frz(Tuple,FTuple),
	find_path_(FTuple,Modes,FNewTuple),
	melt_new((FTuple,FNewTuple),(Tuple,NewTuple)),
	NewTuple = (_,_,_,K),
	(K >= 2 -> write('combining is needed') ;
	write('no combining is needed')), nl.


% first argument and third are tuples, as produced by find_tuples
%% if LengthOfIntermediate = 0 - no intermediate body atoms
%% if LengthOfIntermediate = 1 - only one intermediate body atom. 
%%            no need to combine
find_path_((Head,Subgoal,Intermediate,LengthOfIntermediate),_Modes,
	  (Head,Subgoal,Intermediate,LengthOfIntermediate)) :-
	LengthOfIntermediate < 2, !.

find_path_((Head,Subgoal,Intermediate,_LengthOfIntermediate),Modes,
	  (Head,Subgoal,NewIntermediate,LengthOfNewIntermediate)) :-
	get_mode(Subgoal,Modes, SArity, SMode),
	get_mode(Head,Modes,HArity, HMode),
	find_io(SMode,Subgoal,i,1,SArity,[],SInputs),
	find_io(HMode,Head,i,1,HArity,[],HInputs),
	comma_reverse_(Intermediate,RevIntermediate),
	find_atoms(RevIntermediate,Modes,SInputs,HInputs,
		true,NewIntermediate,0,LengthOfNewIntermediate).
	
get_mode(Atom, Modes, Arity, Mode):-
	get_predicate_of_an_atom(Atom,N,Arity),
	make_dummy_head(Mode,N,Arity), member(Mode,Modes).

find_io(_Mode,_Atom,_Label,I,Arity,Args,Args):- I > Arity, !.
find_io(Mode,Atom,Label,I,Arity,Args,Result):- I =< Arity,
	(arg(I, Mode, Label) ->
		(arg(I, Atom, Arg), to_list(Arg, L), append(L,Args,Args1)) 
		;
	     Args1 = Args),
	I1 is I+1,
	find_io(Mode,Atom,Label,I1,Arity,Args1,Result).

diff(L1,L2,L):-
	findall(X, (member(X,L1), \+ member(X,L2)), L).
	
%%%% if true is reached and SInputs still contains somth that does not
%%%% appear in HInputs - some var, appearing at input position is neither
%%%% in the input of the head nor in the output of some predecessor -
%%%% contradiction to well-modedness

find_atoms(_RevBody, _Modes, SInputs, HInputs, Subgoals, Subgoals, K,K):-
	diff(SInputs,HInputs,[]),!.

find_atoms((Atom,RevBody), Modes, SInputs, HInputs, Subgoals, Result,K,N):-
	diff(SInputs,HInputs,ToSatisfy),
	get_mode(Atom,Modes,AArity, AMode),
	find_io(AMode,Atom,o,1,AArity,[],AOutputs),	
	diff(ToSatisfy,AOutputs,List),
		(List = ToSatisfy ->
	find_atoms(RevBody, Modes, SInputs,  HInputs,Subgoals, Result,K,N)
		;
	(find_io(AMode,Atom,i,1,AArity,[],AInputs),	
	 append(List,AInputs,NewSInputs),
	 K1 is K + 1,
	 find_atoms(RevBody,Modes,NewSInputs,HInputs,
		(Atom,Subgoals),Result,K1,N))).
/*
cut_till(Goal,Goal,B,B,N,N):-!.
cut_till(Goal,(Goal,_Body),B,B,N,N):-!.
cut_till(Goal,(Goal1,Body),B1,B,K,N):-
	K1 is K+1,
	cut_till(Goal,Body,(Goal1,B1),B,K1,N).
*/
/*

| ?- find_path(quicksort(Bigs,Bs),
     (quicksort([X|Xs],Ys) :-
                     partition(Xs,X,Littles,Bigs),
                     quicksort(Littles,Ls),
                     quicksort(Bigs,Bs),
                     append(Ls,[X|Bs],Ys)),
     [quicksort(i,o),append(i,i,o),partition(i,i,o,o)],
     Path).
no combining is needed
Path = partition(Xs,X,Littles,Bigs),true ? 

| ?- find_path(perm(W,T),
     (perm(L,[H|T]):-
             app1(V,[H|U],L),
                  app2(V,U,W),
             perm(W,T)),
     [perm(i,o),app1(o,o,i),app2(i,i,o)],
     S).
combining is needed
S = app1(V,[H|U],L),app2(V,U,W),true ? 

*/

%*********************************************************************

built_ins([!/0,< /2,= /2,=.. /2,=:= /2,=< /2,== /2,=\= /2,> /2,>= /2,@< /2,
@=< /2,@> /2,@>= /2,'C'/3,\== /2,arg/3,atom/1,atomic/1,close/1,compare/3,
copy_term/2,current_op/3,display/1,erase/1,fail/0,functor/3,ground/1,
integer/1,is/2,keysort/2,length/2,name/2,nl/0,nonvar/1,number/1,numbervars/3,
open/3,read/1,recorda/3,recorded/3,recordz/3,sort/2,statistics/2,true/0,
ttynl/0,ttyput/1,var/1,write/1]).

built_in(P/N):-built_ins(B),ord_member(P/N,B).

rec_comps(Clauses,Comps):-
			process_clauses(Clauses,Arcs),%timer('After arcs'),
			preds(Arcs,Preds),
			%timer('After preds'),
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

preds(Arcs,Preds) :- findall(P,
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

compute_called_preds(Calls,CalledPreds):-
	compute_called_preds_(Calls,CalledPreds_),
	sort(CalledPreds_,CalledPreds).

compute_called_preds_([],[]).
compute_called_preds_([Call|Calls],[N/A|CalledPreds]) :-
	functor(Call,N,A), compute_called_preds_(Calls,CalledPreds).

% Tuple - Head,RecSubgoal,Intermediate, Length of Intermediate
find_tuples(_,_,[],[]).
find_tuples(CalledPreds,RecPreds,[Clause|Clauses],Tuples):-
	(Clause = (H:-B) ->
		(get_predicate_of_an_atom(H,Name,Arity),
		 (ord_member(Name/Arity, CalledPreds) ->
				(
                                (
                                (member(Component,RecPreds),
				member(Name/Arity,Component)) ->
				(findall((H,A,P,N),
					find_recursive_atom_and_prefix(B,
						Component,A,P,N),
					Tuples0),
				append(Tuples0,Tuples1,Tuples))
				; Tuples = Tuples1))
			; Tuples = Tuples1))
	; Tuples = Tuples1),
	find_tuples(CalledPreds,RecPreds,Clauses,Tuples1),!.

find_recursive_atom_and_prefix((B1,_B2),Component,A,P,N):-
	find_recursive_atom_and_prefix(B1,Component,A,P,N).
find_recursive_atom_and_prefix((B1,B2),Component,A,(B1,P),N1):-
	find_recursive_atom_and_prefix(B2,Component,A,P,N),
	comma_length(B1,L), N1 is N+L.
find_recursive_atom_and_prefix(B,Component,B,true,0):-
	get_predicate_of_an_atom(B,N,A),
	member(N/A,Component).

%*********************************************************************
solve_tuples(Tuples,ToIgnore,Clauses):-
	solve_tuples(Tuples,ToIgnore,Clauses,Unsolved),
	(Unsolved = [] -> true;
	(write('**** Combine and Solve ****'),nl,
         combine_unsolved_fixpoint_(Unsolved,Unsolved,Combined),
		(Combined = Tuples -> 
			(write('**** Problem discovered ****'),nl)
			; solve_tuples(Combined,ToIgnore,Clauses) 
	))).

combine_unsolved_fixpoint_(L,M,Combined):-
	find_directs([],M,N,D),
	combine_unsolved_fixpoint(L,N,Combined1),
	append(D,Combined1,Combined).

combine_unsolved_fixpoint(_,[],[]).
combine_unsolved_fixpoint(L,M,Combined):-
	combine_unsolved(L,M,C),
	find_directs(M,C,N,D),
	combine_unsolved_fixpoint(L,N,Combined1),
	append(D,Combined1,Combined).
		

% M - prev. step, C - current, N - next step, D - direct
find_directs(_,[],[],[]).
find_directs(M,[(H,S,I,L)|Cs],N,D):-
	(member((H,S,I,L),M) ->
		(N=N1, D=D1)
	; (
	   (functor(H,HN,HA),functor(S,HN,HA)) ->
		(N=N1, D=[(H,S,I,L)|D1])
		; (N=[(H,S,I,L)|N1], D=D1))),
	find_directs(M,Cs,N1,D1).	

combine_unsolved([],_,[]).
combine_unsolved([Tuple|Tuples],M,Combination):-
	copy_term(M,M1),
	combine_tuple(Tuple,M1,C),
	combine_unsolved(Tuples,M,Cs),
	append(C,Cs,Combination).

combine_tuple(_,[],[]).
combine_tuple(Tuple,[(H,S,I,L)|M], Cs):-
	copy_term(Tuple,(Head,Subgoal,Int,Length)),
	(Subgoal = H ->
		(comma_append(Int,I,I1),
		 L1 is Length+L,
	         Cs = [(Head,S,I1,L1)|Cs1])
	; Cs = Cs1),
	combine_tuple(Tuple,M,Cs1).

solve_tuples([],_,_,[]).
solve_tuples([Tuple|Tuples],ToIgnore,Clauses,Unsolved):-
	(solve_tuple(Tuple,ToIgnore,Clauses) -> 	
		Unsolved = Unsolved1
	; (write('***> Is not solved '), write(Tuple), nl,
	   Unsolved = [Tuple|Unsolved1])
	), 
	solve_tuples(Tuples,ToIgnore,Clauses,Unsolved1).	

solve_tuple((Head,Subgoal,_Intermediate,_Length),ToIgnore,_) :-
	frz((Head,Subgoal),(FHead,FSubgoal)),
	compare_terms(FHead,FSubgoal,ToIgnore,>).
solve_tuple((Head,Subgoal,Intermediate,K),ToIgnore,Clauses) :-
	frz((Head,Subgoal,Intermediate),(FHead,FSubgoal,FIntermediate)),
	construct_condition(FHead,FSubgoal,FIntermediate,ToIgnore,Condition),
	%timer('After constructing decrease condition '),
	drop_true(FIntermediate,FIn),
	(K = 1 ->
		(get_predicate_of_an_atom(FIn,N,A),
		 filter_clauses(N/A,Clauses,NewClauses))
	; combine(Intermediate,Clauses,NewClauses)),
	construct_conditions_on_int(FIn,Condition,NewClauses,
		ToIgnore, Conditions), 
	check_conditions(Conditions).
/*
%% try as transitivity
solve_tuple((Head,Subgoal,Intermediate,K),ToIgnore,Clauses) :-
	K >= 2,
	frz((Head,Subgoal,Intermediate),(FHead,FSubgoal,FIntermediate)),
	construct_condition(FHead,FSubgoal,FIntermediate,ToIgnore,Condition),
	drop_true(FIntermediate,FIn),
*/
check_conditions(Conditions):-
	%timer('After constructing actual conditions '),
	(Conditions = [] -> true
	; (write('Still to be solved '),write(Conditions), nl)).

filter_clauses(_,[],[]).
filter_clauses(N/A,[(H:-B)|Clauses],FC):-
	!,
	(get_predicate_of_an_atom(H,N,A) ->
		FC = [(H:-B)|FC1] ; FC = FC1),
	filter_clauses(N/A,Clauses,FC1) .
filter_clauses(N/A,[C|Clauses],FC):-
	(get_predicate_of_an_atom(C,N,A) ->
		FC = [C|FC1] ; FC = FC1),
	filter_clauses(N/A,Clauses,FC1).


match(Atom,Condition,RealAtom,RealCondition):-
	melt_new((Atom,Condition),(RealAtom,RealCondition)).	
find_atoms((Atom1,Atom2),(B1,B2),(B1,P2)):-
	get_predicate_of_an_atom(Atom1,N,A),
	get_predicate_of_an_atom(B1,N,A),!,
	find_atoms(Atom2,B2,P2).
find_atoms((Atom1,Atom2),(B1,B2),P):-!,
	find_atoms((Atom1,Atom2),B2,P).
find_atoms(Atom,(B1,_B2),B1):-
	get_predicate_of_an_atom(Atom,N,A),
	get_predicate_of_an_atom(B1,N,A).
find_atoms(Atom,B1,B1):-
	get_predicate_of_an_atom(Atom,N,A),
	get_predicate_of_an_atom(B1,N,A).

find_premises((Atom1,Atom2),Condition,(B1,B2),P):-
	!,
	find_atoms((Atom1,Atom2),(B1,B2),N),
	match((Atom1,Atom2),Condition,N,P).
find_premises(Atom,Condition,(B1,B2),P):-!,
	get_predicate_of_an_atom(Atom,N,A),
	(get_predicate_of_an_atom(B1,N,A) ->
		(match(Atom,Condition,B1,P1),
		 find_premises(Atom,Condition,B2,P2),
		 comma_append(P1,P2,P))
	; find_premises(Atom,Condition,B2,P)).
find_premises(Atom,Condition,B,P):-
	match(Atom,Condition,B,P).

construct_conditions_on_int(_Atom,_Condition,[],_,[]).
construct_conditions_on_int(Atom,Condition,[Clause|Clauses],
		ToIgnore,Conditions):-
	match(Atom,Condition,Clause,[Term1>Term2]),
	frz((Term1>Term2),(FT1>FT2)),
	(compare_terms(FT1,FT2,ToIgnore,>) ->
		Conditions = Conditions1
	; Conditions = [Term1>Term2|Conditions1]),
	construct_conditions_on_int(Atom,Condition,
		Clauses,ToIgnore,Conditions1).
construct_conditions_on_int(Atom,Condition,[(H:-B)|Clauses],
		ToIgnore,Conditions):-
	match(Atom,Condition,H,[MCondition]),
	find_premises(Atom,Condition,B,P),
	frz((MCondition,P),(FCondition,FP)),
	(check_implies(FP,ToIgnore,FCondition) ->
		Conditions = Conditions1
	; Conditions = [implies(P,MCondition)|Conditions1]),
	%%%
	retractall(simplify(yes)), assert_if_new(simplify(no)),
	%%%
	construct_conditions_on_int(Atom,Condition,
		Clauses,ToIgnore,Conditions1).
construct_conditions_on_int(Atom,Condition,[_|Clauses],ToIgnore,Conditions):-
	construct_conditions_on_int(Atom,Condition,Clauses,ToIgnore,Conditions).

%%% direct recursion
construct_condition(Head,Subgoal,Intermediate,ToIgnore,Condition):-
	functor(Head,N,A),
	functor(Subgoal,N,A),!,
	construct_by_args(Head,Subgoal,Intermediate,ToIgnore,N,A,1,Condition).

construct_by_args(_Head,_Subgoal,_Intermediate,_ToIgnore,_N,A,I,[]) :-
	I > A.
construct_by_args(Head,Subgoal,Intermediate,ToIgnore,N,A,I,Constr):-
	member(N/A/I,ToIgnore),!,
	I1 is I+1,
	construct_by_args(Head,Subgoal,Intermediate,ToIgnore,N,A,I1,Constr).
construct_by_args(Head,Subgoal,Intermediate,ToIgnore,N,A,I,Constr):-
	arg(I,Head,HI),
	arg(I,Subgoal,SI),
	compare_terms(HI,SI,ToIgnore,undef),
	to_list(HI,HIL), to_list(SI,SIL),
	to_list(Intermediate,IL),
	((subset(HIL,IL), subset(SIL,IL)) ->
		Constr = [HI>SI|Constr1]
		; Constr = Constr1),
	I1 is I+1,
	construct_by_args(Head,Subgoal,Intermediate,ToIgnore,N,A,I1,Constr1).

subset([],_).
subset([X|Xs],L):-
	member(X,L),
	subset(Xs,L).


greater(T1,T2,_ToIgnore,M):- member(T1>T2,M).
greater(T1,T2,ToIgnore,_M):- compare_terms(T1,T2,ToIgnore,>).
			
gen_i(A,A).
gen_i(A,I):-
	A>1, A1 is A-1, gen_i(A1,I).

%%% containment
check_implies(M,_,X) :- member(X,M).
%%% transitivity
check_implies(M,_ToIgnore,Term1>Term3) :- 
	member(Term1>Term2,M), member(Term2>Term3,M).
check_implies(M,ToIgnore,Term1>Term3) :- 
	member(Term1>Term2,M), compare_terms(Term2,Term3,ToIgnore,S),
	(S = '=' ; S = '>').
check_implies(M,ToIgnore,Term1>Term3) :- 
	member(Term2>Term3,M), compare_terms(Term1,Term2,ToIgnore,S),
	(S = '=' ; S = '>').
%%% monotonicity
check_implies(M,ToIgnore,Term1>Term2) :- 
	functor(Term1,N,A), functor(Term2,N,A),
	check_args_in_premis(Term1,Term2,ToIgnore,M,1,A,N).
check_implies(M,ToIgnore,Term1>Term2):-
	\+ simplify(yes), simplify(Term1,Term),
	retract(simplify(no)),
	assert(simplify(yes)),
	check_implies(M,ToIgnore,Term>Term2).

%%% ?!?!?! How to generalize?
simplify([X,Y|T],[Y,X|T]):-
	write('**** Using simplification ([X,Y|T],[Y,X|T])'),nl.

check_args_in_premis(Term1,Term2,ToIgnore,M,I,A,N) :-
	I =< A, 
	(member(N/A/I,ToIgnore) -> 
		(I1 is I+1, 
		 check_args_in_premis(Term1,Term2,ToIgnore,M,I1,A,N))
		;
		(arg(I,Term1,A1), arg(I,Term2,A2),
		 (greater(A1,A2,ToIgnore,M) ->
			(write('**** '), write(N/A),
			 write(' should be monotone on '),
		         write(I), write('th argument.'),nl)
			; 
			(I1 is I+1, 
		 	 check_args_in_premis(Term1,Term2,ToIgnore,
				M,I1,A,N))))).

%%% identity
compare_terms(Term,Term,_,=):-!.
%%% direct recursion = monotonicity
compare_terms(Head,Subgoal,ToIgnore,Sign):-
	functor(Head,N,A),
	functor(Subgoal,N,A),!,
	compare_args(Head,Subgoal,ToIgnore,N,A,1,Sign).
%%% subterm
compare_terms(Term1,Term2,ToIgnore,>):-
	find_arg(I,Term1,Term2),
	functor(Term1,N,A),
	\+ member(N/A/I,ToIgnore),!,
	write('**** '),write(N/A), 
	write(' should have a subterm property on the '),
	write(I), write('th argument.'),nl.

%%% recursive subterm
compare_terms(Term1,Term2,ToIgnore,>):-
	find_arg(I,Term1,Term),
	functor(Term1,N,A),
	\+ member(N/A/I,ToIgnore),
	compare_terms(Term,Term2,ToIgnore,>),
	write('**** '),write(N/A), 
	write(' should have a subterm property on the '),
	write(I), write('th argument.'),nl.

%%% rpo
/*
compare_terms(Term1,Term2,ToIngore,>):-
	functor(Term1,N1,A1),
	functor(Term2,N2,A2),
	assert_if_new(order(N1/A1,N2/A2)),
	greater_loop(Term1,Term2,ToIgnore,1,A2).

greater_loop(Term1,Term2,_,I,A2):- I > A2,!.
greater_loop(Term1,Term2,ToIgnore,I,A2):- 
	arg(I,Term2,ArgI),
	compare_terms(Term1,ArgI,ToIgnore,>),
	I1 is I+1,
	greater_loop(Term1,Term2,ToIgnore,I1,A2).
*/
compare_terms(Term1,Term2,ToIgnore,<):-	
	compare_terms(Term2,Term1,ToIgnore,>).
compare_terms(Term1,Term2,ToIgnore,undef) :-
	\+ compare_terms(Term1,Term2,ToIgnore,>),
	\+ compare_terms(Term1,Term2,ToIgnore,=),
	\+ compare_terms(Term2,Term1,ToIgnore,>).

find_arg(I,Term,Subterm):-
	functor(Term,_,Arity),
	find_arg(Term,Subterm,1,Arity,I).
find_arg(Term,Subterm,I,Arity,I):-
	I =< Arity,
	arg(I,Term,Subterm),!.
find_arg(Term,Subterm,I,Arity,J):-
	I =< Arity,
	I1 is I+1, find_arg(Term,Subterm,I1,Arity,J).

compare_args(_Head,_Subgoal,_ToIgnore,_N,A,I,undef):- I > A,!.
compare_args(_Head,_Subgoal,ToIgnore,N,A,I,undef):- 
	ord_member(N/A/I,ToIgnore),!.
compare_args(Head,Subgoal,ToIgnore,N,A,I,Sign):- 
	arg(I,Head,HI), arg(I,Subgoal,SI),
	compare_terms(HI,SI,ToIgnore,Sign1),
	I1 is I + 1, compare_args(Head,Subgoal,ToIgnore,N,A,I1,Sign2),
	max(Sign1,Sign2,Sign).

max(X,undef,X):-!.
max(undef,X,X).
max(=,>,>).
max(=,<,<).
max(>,=,>).
max(<,=,<).
max(>,>,>).
max(=,=,=).
max(<,<,<).
max(<,>,undef).
max(>,<,undef).
%*********************************************************************
go:-
	retractall(simplify(_)),
	assert(simplify(no)),
	time(_),read_program('../examples/quicksort',Clauses),
          rec_comps(Clauses,Comps), %timer('After comps '),
          compute_called_preds([quicksort(f,f),partition(f,f,f,f),
		append(f,f,f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          %timer('After finding tuples '), 
	  simplify_tuples(Tuples,[quicksort(i,o),
          partition(i,i,o,o),append(i,i,o)],NewTuples), 
	  %timer('After simplifying tuples '), 
	  solve_tuples(NewTuples,[],Clauses),
	  timer('After solving tuples ').
goack:-
	retractall(simplify(_)),
	assert(simplify(no)),
	time(_),read_program('../examples/various/ack',Clauses),
          rec_comps(Clauses,Comps), %timer('After comps '),
          compute_called_preds([ack(f,f,f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          %timer('After finding tuples '), 
	  %simplify_tuples(Tuples,[quicksort(i,o),
          %partition(i,i,o,o),append(i,i,o)],NewTuples), 
	  %timer('After simplifying tuples '), 
	  NewTuples = Tuples,
	  solve_tuples(NewTuples,[],Clauses),
	  timer('After solving tuples ').
gopapp:-
	retractall(simplify(_)),
	assert(simplify(no)),
	time(_),read_program('../examples/perm_app',Clauses),
          rec_comps(Clauses,Comps), %timer('After comps '),
          compute_called_preds([perm(f,f), app1(f,f,f),	app2(f,f,f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          %timer('After finding tuples '), 
	  simplify_tuples(Tuples,[perm(i,o),app1(o,o,i),
          app2(i,i,o)],NewTuples), 
	  %timer('After simplifying tuples '), 
	  solve_tuples(NewTuples,[perm/2/2,app1/3/1,
		app1/3/2,app2/3/3],Clauses),
	  timer('After solving tuples ').

goSS_map:-
	retractall(simplify(_)),
	assert(simplify(no)),
	time(_),read_program('../examples/apt/SS_map',Clauses),
          rec_comps(Clauses,Comps), %timer('After comps '),
          compute_called_preds([color_map(f,f),color_region(f,f,f,f),
		select(f,f,f),member(f,f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          %timer('After finding tuples '), 
	  NewTuples = Tuples,
	  %timer('After simplifying tuples '), 
	  solve_tuples(NewTuples,[],Clauses),
	  timer('After solving tuples ').

go1:-
	retractall(simplify(_)),
	assert(simplify(no)),
	time(_),read_program('../examples/zebra',Clauses),
          rec_comps(Clauses,Comps), %timer('After comps '),
          compute_called_preds([zebra(f,f,f),append(f,f,f),
		nextto(f,f,f),sublist(f,f),member(f,f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          %timer('After finding tuples '), 
	  %%simplify_tuples(Tuples,[quicksort(i,o),
          %%partition(i,i,o,o),append(i,i,o)],NewTuples), 
	  %timer('After simplifying tuples '), 
	  NewTuples = Tuples,
	  solve_tuples(NewTuples,[],Clauses),
	  timer('After solving tuples ').

godds :-
	godds11,godds12,godds38,godds313,
	godds314,godds315,godds317.

godds11:-
	retractall(simplify(_)),
	assert(simplify(no)),
	write('***************** DDS 1.1 *********************'),nl,
	time(_),read_program('../examples/dds/dds1.1',Clauses),
          rec_comps(Clauses,Comps), 
          compute_called_preds([append(f,f,f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          %timer('After finding tuples '), 
	  simplify_tuples(Tuples,[append(i,i,o)],NewTuples), 
	  %timer('After simplifying tuples '), 
	  solve_tuples(NewTuples,[],Clauses),
	  timer('After solving tuples ').

godds12:-
	retractall(simplify(_)),
	assert(simplify(no)),
	write('***************** DDS 1.2 *********************'),nl,
	time(_),read_program('../examples/dds/dds1.2',Clauses),
          rec_comps(Clauses,Comps), 
          compute_called_preds([delete(f,f,f),perm(f,f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          NewTuples = Tuples,
	  solve_tuples(NewTuples,[],Clauses),
	  timer('After solving tuples ').
godds38:-
	retractall(simplify(_)),
	assert(simplify(no)),
	write('***************** DDS 3.8 *********************'),nl,
	time(_),read_program('../examples/dds/dds3.8',Clauses),
          rec_comps(Clauses,Comps), 
          compute_called_preds([reverse(f,f,f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          %timer('After finding tuples '), 
	  %simplify_tuples(Tuples,[reverse(i,o)],NewTuples), 
	  %timer('After simplifying tuples '), 
	  NewTuples = Tuples,
	  solve_tuples(NewTuples,[],Clauses),
	  timer('After solving tuples ').

godds313:-
	retractall(simplify(_)),
	assert(simplify(no)),
	write('***************** DDS 3.13 *********************'),nl,
	time(_),read_program('../examples/dds/dds3.13',Clauses),
          rec_comps(Clauses,Comps), 
          compute_called_preds([duplicate(f,f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          %timer('After finding tuples '), 
	  simplify_tuples(Tuples,[duplicate(i,o)],NewTuples), 
	  %timer('After simplifying tuples '), 
	  solve_tuples(NewTuples,[],Clauses),
	  timer('After solving tuples ').
godds314:-
	retractall(simplify(_)),
	assert(simplify(no)),
	write('***************** DDS 3.14 *********************'),nl,
	time(_),read_program('../examples/dds/dds3.14',Clauses),
          rec_comps(Clauses,Comps), 
          compute_called_preds([sum(f,f,f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          %timer('After finding tuples '), 
	  simplify_tuples(Tuples,[sum(i,i,o)],NewTuples), 
	  %timer('After simplifying tuples '), 
	  solve_tuples(NewTuples,[],Clauses),
	  timer('After solving tuples ').
godds315:-
	retractall(simplify(_)),
	assert(simplify(no)),
	write('***************** DDS 3.15 *********************'),nl,
	time(_),read_program('../examples/dds/dds3.15',Clauses),
          rec_comps(Clauses,Comps), 
          compute_called_preds([merge(f,f,f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          %timer('After finding tuples '), 
	  simplify_tuples(Tuples,[merge(i,i,o)],NewTuples), 
	  %timer('After simplifying tuples '), 
	  solve_tuples(NewTuples,[],Clauses),
	  timer('After solving tuples ').
godds317:-
	retractall(simplify(_)),
	assert(simplify(no)),
	write('***************** DDS 3.17 *********************'),nl,
	time(_),read_program('../examples/dds/dds3.17',Clauses),
          rec_comps(Clauses,Comps), 
          compute_called_preds([dis(f),con(f)],
          CalledPreds),find_tuples(CalledPreds,Comps,Clauses,Tuples),
          %timer('After finding tuples '), 
	  simplify_tuples(Tuples,[dis(i),con(i)],NewTuples), 
	  %timer('After simplifying tuples '), 
	  solve_tuples(NewTuples,[],Clauses),
	  timer('After solving tuples ').

%*********************************************************************
qpa:- time(_), read_program(perm_app,CL), combine((app(V,[H|U],L),
	app(V,U,W), true), CL, NewCL), timer(''), writel(NewCL),
	length(NewCL,L), nl, write(L).

qq0:- time(_), read_program(quicksort,CL), combine(
		(partition(Xs,X,Littles,Bigs),
                quicksort(Littles,Ls),
                quicksort(Bigs,Bs),
                append(Ls,[X|Bs],Ys), true), CL, NewCL), timer(''), 
		writel(NewCL),
	length(NewCL,L), nl, write(L).

qq:- time(_), read_program(quicksort,CL), combine(
		(partition(Xs,X,Littles,Bigs),
                quicksort(Littles,Ls), true), CL, NewCL), timer(''), 
		writel(NewCL),
	length(NewCL,L), nl, write(L).


qz0 :- time(_), read_program(zebra, CL), combine((
        List = [_,_,_,_,_],
        member(house(  red,  englishman,_, _,  _) ,List), 
        member(house(_,spaniard,  dog, _,  _) ,List), 
        member(house(green, _,_, coffee,  _) ,List), 
        member(house(_,ukrainian,_,tea,  _) ,List), 
        nextto(house(ivory, _,_, _,  _),
                house(green, _,_, _,  _),List), 
        member(house(_, _,snail, _,old_gold),List),  
        member(house(yellow,_,_, _,kools),List),  
        [_,_,house(_, _,_,milk, _),_,_] = List,  
        [house(_,norwegian,_, _,  _)|_] = List,  
        nextto(house(_, _,   _, _,chesterfield),
               house(_, _, fox, _,           _),List),
        nextto(house(_, _,    _, _,kools), 
               house(_, _,horse, _,    _),List),
        member(house(_, _,_, orange,lucky_strike),List),
        member(house(_,japanese,_, _,parliaments),List),
        nextto(house(   _,norwegian,_,_,_),
               house(blue,        _,_,_,_),List),
        member(house(_, Drinkswater,_,  water,_),List),
        member(house(_,  Zebraowner,zebra, _,_),List),
        true), CL, NewCL), timer(''), 
		%writel(NewCL),
	length(NewCL,L), nl, write(L).
/*
 ?- qz0.
 5.67

640

*/


