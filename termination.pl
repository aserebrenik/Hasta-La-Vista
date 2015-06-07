:- module(termination, [prove_termination/9]).

:- use_module(library(lists), [append/3, is_list/1, member/2, nth/3, nth0/3]).
:- use_module(library(ordsets), [list_to_ord_set/2, ord_subset/2,
				 ord_union/3]).
:- use_module(adorn, [code_all/3, code/3, decode/3, original_free_atom/3]).
:- use_module(apply, [apply/3]).
:- use_module(atom, [comparison/1, term_comparison/1, fresh_all/2]).
:- use_module(aux, [all_but_nth/4, all_but_nth0/4, assert_list/2,
		    flatten/2, rename/4, time/1, timer/1, up_to_n/2]).
:- use_module(functors, [functors/2]).
:- use_module(intervals, [to_intervals/2,tree_to_list_/3]).
:- use_module(numvars, [diff_vars/2, frz/2, frzl/2, frzl/3, melt/2,
			varname/1, varname/2]).
:- use_module(simplify_symb, [combine/2, simplify_symb/2]).
:- use_module(solve, [solve/4]).





initialize_symbolic_constraints(Preds, Functors):-
	retractall(user:lm(_,_)),
	retractall(user:norm(_,_)),
	retractall(user:size_exp(_,_)),
	initialize_lms_and_sizes(Preds),
	initialize_norms(Functors).

initialize_lms_and_sizes([]).
initialize_lms_and_sizes([Pred|Preds]):-
	fresh_all(Pred, Pred1),
	Pred =.. [Name|Args],
	length(Args, N),
	up_to_n(N,L),
	code_all(Name,[0|L],LMArgs), % AS 13.9.2001
	
	
	code(Name,e,NameE),
	code_all(NameE,[0|L],SizeArgs),
	
	
	(decode(Name, OriginalPred, Adornment) ->
	    functor(OriginalAtom, OriginalPred, N),
	    set_int_args_to_zero(OriginalAtom,LMArgs, LMArgs_),

	    adornment_to_list(Adornment, List),
	    length(List, K),
	      (K > 0 ->
		  up_to_n(K,L1),
		  code(Name,i,NameI),
		  code_all(NameI, L1, LMIArgs),
		  
		  code(Name,'i_e',NameIE),
		  code_all(NameIE,[0|L1],SizeIArgs),
		    
		  append(LMArgs_, LMIArgs, LM),
		  append(SizeArgs, SizeIArgs, Size)  
	      ;
		  LM = LMArgs_, Size = SizeArgs
		  )
	    ;
	    set_int_args_to_zero(Pred,LMArgs, LMArgs_),
	    LM = LMArgs_, Size = SizeArgs),
	
	assertz(user:lm(Pred1,LM)),
	assertz(user:size_exp(Pred1, Size)),
	
	initialize_lms_and_sizes(Preds).

set_int_args_to_zero(OriginalAtom, LMArgs, NewLMArgs):-
	user:iap(OriginalAtom-IntArgs),  ! ,
	set_int_args_to_zero(IntArgs, 0, LMArgs, NewLMArgs).
set_int_args_to_zero(_OriginalAtom, LMArgs, LMArgs).

set_int_args_to_zero([], _N, LMArgs, LMArgs).
set_int_args_to_zero([I|IntArgs], N, [LMArg|LMArgs], [LMArg|NewLMArgs]):-
	N < I, N1 is N+1,
	set_int_args_to_zero([I|IntArgs], N1, LMArgs, NewLMArgs).
set_int_args_to_zero([I|IntArgs], I, [_|LMArgs], [0|NewLMArgs]):-
	I1 is I+1,
	set_int_args_to_zero(IntArgs, I1, LMArgs, NewLMArgs).
	
initialize_norms([]).
initialize_norms([Pred|Preds]):-
	fresh_all(Pred, Pred1),
	Pred =.. [Name|Args],
	length(Args, N),
	up_to_n(N,L),
	code_all(Name,[0|L],NArgs),
	assertz(user:norm(Pred1,NArgs)),
	initialize_norms(Preds).
/*
find_number_of_adornments((_,_,_), 2) :- ! .
find_number_of_adornments(and(X,Y), M):-  ! ,
	find_number_of_adornments(X,M1),
	find_number_of_adornments(Y,M2), M is M1 + M2.
find_number_of_adornments(or(_,_), 0):-  ! .
find_number_of_adornments(_, 1).
*/
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rigidity_conditions([], []).
rigidity_conditions([Call|Calls], Conditions):-
	rigidity_conditions_call(Call, Conditions1),
	rigidity_conditions(Calls, Conditions2),
	append(Conditions1, Conditions2, Conditions).

rigidity_conditions_call(Call, Conditions):-
	fresh_all(Call, Call1),
	Call =.. [_|Args],
	rigidity_conditions_args(Args, Call1, Conditions, 1).


/*
not necessary - potential MAX depending adornments are already
filtered out in adornments.pl

	original_free_atom(Call1, _OPred, Ads),
	( Ads = undefined ->
	    true
	;
	    update_integer_coefficients(Ads, Call, Call1)).

update_integer_coefficients(Ads, Call, Call1):-
	apply(Ads, Call, CallAds),
	adornment_to_list(CallAds, CallAdsL),
	functor(Call, _, Arity),
	Arity1 is Arity+1,
	update_integer_coefficients_(Arity1, Call1, CallAdsL).

update_integer_coefficients_(_, _Call1, []).
update_integer_coefficients_(I, Call1, [CallAd|CallAds]):-
	max_only(CallAd),  ! , retract(user:lm(Call1, L)),
	all_but_nth(I,L,0,L1), asserta(user:lm(Call1, L1)), I1 is I+1, 
	update_integer_coefficients_(I1, Call1, CallAds).
update_integer_coefficients_(I, Call1, [_CallAd|CallAds]):-
	I1 is I+1,update_integer_coefficients_(I1, Call1, CallAds).

max_only([]).
max_only('MAX').
max_only([X|Xs]):-  ! , max_only(X), max_only(Xs).
max_only(X) :- number(X),  ! .
max_only(X):- compound(X), X=..[_|Args], max_only(Args).

*/

rigidity_conditions_args([], _, [], _).
% if the argument is 'MAX' the corresponding coefficient is replaced by 0
rigidity_conditions_args(['MAX'|Args],  Call1, Conditions, N) :-
	 ! , retract(user:lm(Call1, L)),  N1 is N+1,
	all_but_nth(N1,L,0,L1),
	asserta(user:lm(Call1, L1)),  
	rigidity_conditions_args(Args, Call1, Conditions, N1).
rigidity_conditions_args([Arg|Args],  Call1, Conditions, N) :-
	compound(Arg),  ! ,N1 is N+1,
	user:lm(Call1, L), nth(N1, L, Coeff),
	find_branches(Arg, Branches),  ! ,
	construct_conditions(Coeff, Branches, Conditions1),
	rigidity_conditions_args(Args, Call1, Conditions2, N1),
	append(Conditions1, Conditions2, Conditions).
rigidity_conditions_args([_Arg|Args], Call, Conditions, N):-
	N1 is N+1,
	rigidity_conditions_args(Args, Call, Conditions, N1).

find_branches('MAX', [1]).
find_branches([], []).
find_branches('OR'(List), Branches):-
	 ! , find_branches(List, Branches).
find_branches([Arg|Args], Branches):-
	 ! , find_branches(Arg, B1),
	find_branches(Args,B2),
	append(B1,B2,Branches).
find_branches(Arg/0,[]) :-  ! .
find_branches(Arg, Branches):-
	compound(Arg),  ! ,
	Arg =.. [Name,Args],
	length(Args,L),
	functor(Call1,Name,L),
	user:norm(Call1, [_|Norm]),
	find_branches(Norm, Args, Branches).
find_branches(_, []).

find_branches([], [], []).
find_branches([Coeff|Coeffs], [Arg|Args], Branches):-
	find_branches(Arg, B),
	multiply_by_coeff(Coeff, B, B1),
	find_branches(Coeffs, Args, B2),
	append(B1, B2, Branches).

multiply_by_coeff(_, [], []).
multiply_by_coeff(Coeff, [B|Bs], [Coeff*B|CBs]):-
	multiply_by_coeff(Coeff, Bs, CBs).

construct_conditions(_Coeff, [], []).
construct_conditions(Coeff, [Branch|Branches],
		     [Coeff*Branch #= 0|Conditions]):-
	construct_conditions(Coeff, Branches, Conditions).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

model_conditions([], _, []).
model_conditions(_, [], []) :-  ! .
model_conditions([clause(Head, _Body)|Clauses], Needed, Conditions) :-
	functor(Head, N, A),
	\+ member(N/A, Needed),  ! ,
	model_conditions(Clauses, Needed, Conditions).
model_conditions([clause(Head, Body)|Clauses], Needed, Conditions) :-
	user:bad_clause(clause(Head,Body)),  ! ,
	write('*** Clause *** '), 
	write(clause(Head,Body)), write(' *** is ignored ***'), nl,      
	model_conditions(Clauses, Needed, Conditions).
model_conditions([clause(Head, Body)|Clauses], Needed,
		 [implies(Body2,BuiltIns2,Head2)|Conditions]) :-
	model_head(Head, Head1, _, _, _),
	model_body(Body, Body1, BuiltIns, _, _),
	simplify_symb(implies(Body1,BuiltIns,Head1),
		      implies(Body2,BuiltIns2,Head2)),
	model_conditions(Clauses, Needed, Conditions).

% the third argument contains built-ins that do not provide constraints
% but ca be useful at later stages of the analysis, e.g. X > Y
model_body(true, true, true, Needed, Needed).
model_body((B1,B2), and(MB1, MB2), (LB1,LB2), N, N2):-
	model_head(B1, MB1, LB1, N, N1),
	model_body(B2, MB2, LB2, N1, N2).
model_head(T1=T2, S1=S2, true, N, N) :-  ! ,
	get_norm(T1,S1),
	get_norm(T2,S2).
model_head(Head,S #>= 0, true, N, [Name/L|N]):-
	fresh_all(Head, Head_),
	user:size_exp(Head_, SHead),
	user:io((Head_, I, O)),  ! ,
	Head =.. [Name|Args], length(Args, L),
	build_model_head(Head, Args, SHead, 0, I, [0|O], S).
model_head(X is Exp1 mod Exp2, true, X = Exp1 mod Exp2, N, N) :-  ! .
model_head(X is Exp, X = Exp, true, N, N) :-  ! .
% for built-ins. can we do something better?
model_head(X, true, X, N, N) :- comparison(X),  ! .
model_head(X, true, X, N, N) :- term_comparison(X),  ! .
model_head(_, true, true, N, N) :-  ! .



build_model_head(Head, Args, [Coeff|SHead], N, I, [0|O], Coeff*(-1)+S) :-
	 ! , N1 is N+1, build_model_head(Head, Args, SHead, N1, I, O, S).
build_model_head(Head, [Arg|Args], [Coeff|SHead], N,
		 I, [N|O], Exp*Coeff*(-1)+S) :-
	 ! , get_norm(Arg, Exp), N1 is N+1,
	build_model_head(Head, Args, SHead, N1, I, O, S).
build_model_head(Head, [Arg|Args], [Coeff|SHead], N,
		 [N|I], O, Exp*Coeff+S) :-
	 ! , get_norm(Arg, Exp), N1 is N+1,
	build_model_head(Head, Args, SHead, N1, I, O, S).
build_model_head(Head, [], SHead, _, [], [], S):-
	functor(Head, Pred, Arity),
	decode(Pred, _, Adornment), ! ,
	%%% Arity1 is Arity+1,
	adornment_to_list(Adornment, AD),
	build_int_sum(Head, SHead, 1, AD, S). %instead of Arity1
build_model_head(_Head, [], _SHead, _, [], [], 0).

build_sum(Head, SHead, [], S) :-
	functor(Head, Pred, Arg),
	decode(Pred, _, Adornment), ! ,
	Arg1 is Arg+1,
	adornment_to_list(Adornment, AD),
	build_int_sum(Head, SHead, Arg1, AD, S).
build_sum(_Head, _SHead, [], 0).
build_sum(Head, SHead, [0|Is], Coeff+S):-
	 ! , nth0(0, SHead, Coeff),
	build_sum(Head, SHead, Is, S).
build_sum(Head, SHead, [I|Is], Exp*Coeff+S):-
	nth0(I, SHead, Coeff),
	arg(I, Head, Arg),
	get_norm(Arg, Exp),
	build_sum(Head, SHead, Is, S).
get_norm(X,X):- var(X),  ! .
get_norm(X,X):- varname(X),  ! .
get_norm(X,Exp):-
	compound(X), ! ,
	fresh_all(X,X1),
	X =.. [_|L_], length(L_,N1),
	user:norm(X1,N), up_to_n(N1,L),
	build_sum(X,N,[0|L],Exp).
get_norm(X,0):- ground(X).

adornment_to_list(or(_,_), []).
adornment_to_list(and(X,Y), L):-
	adornment_to_list(X, L1),
	adornment_to_list(Y, L2),
	append(L1,L2,L).
adornment_to_list((_X,-inf,inf), []) :- ! .
adornment_to_list((X,Min,inf), [X - Min >= 0]) :- ! .
adornment_to_list((X,-inf,Max),[Max - X >= 0]) :- ! .
adornment_to_list((X,Min,Max), [X - Min >= 0, Max - X >= 0]).
adornment_to_list(X<Y, [Y - X > 0]).
adornment_to_list(Y>X, [Y - X > 0]).
adornment_to_list(X=<Y, [Y - X >= 0]).
adornment_to_list(Y>=X, [Y - X >= 0]).
adornment_to_list(X=Y,  [Y-X >= 0, X-Y >= 0]).

build_int_sum(_Head, _SHead, _, [], 0).
build_int_sum(Head, SHead, I, [Ad|Ads], EH*Arg +S) :-
	Ad =.. [_, E, 0], nth0(I, SHead, Arg),
	apply(E, Head, EH), I1 is I+1,
	build_int_sum(Head, SHead, I1, Ads, S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

decrease_conditions(Clauses, MutRec, NeededForModelConditions, Decreases):-
	decrease_conditions_(Clauses, MutRec,
			     [], NeededForModelConditions_, Decreases_),
	flatten(NeededForModelConditions_,NeededForModelConditions),
	sort(Decreases_, Decreases).
decrease_conditions_([],_,N,N,[]).
decrease_conditions_([Clause|Clauses], MutRec,
		     Needed0, NeededForModelConditions, Decreases):-
	findall((D,N),
		(
		  decrease_conditions_(Clause, MutRec, Needed0 , N, D)
		;
		  N = Needed0, D = []
		    ),
		DNs),
	ds_and_ns(DNs, Ds, Ns_),
	list_to_ord_set(Ns_, Ns),
	decrease_conditions_(Clauses, MutRec, Ns,
			     NeededForModelConditions, Decrease),
	append(Ds, Decrease, Decreases).

decrease_conditions_(clause(Head, Body), MutRec, Needed0, Needed,
		    implies(Body2,BuiltIns2,Head3#>Head4)) :-
	segment(Head, Body, MutRec, SegmentBody, RecSubgoal), 
	decrease_head(Head, Head1),
	decrease_head(RecSubgoal, Head2),
	model_body(SegmentBody, Body1, BuiltIns1, Needed0, Needed),
	simplify_symb(implies(Body1,BuiltIns1,Head1#>Head2),
		      implies(Body2,BuiltIns2,Head3#>Head4)).

ds_and_ns([], [], []).
ds_and_ns([([],[])|DNs], Ds, Ns):-  ! , ds_and_ns(DNs, Ds, Ns).
ds_and_ns([([],N)|DNs], Ds, [N|Ns]):-  ! , ds_and_ns(DNs, Ds, Ns).
ds_and_ns([(D,[])|DNs], [D|Ds], Ns):-  ! , ds_and_ns(DNs, Ds, Ns).
ds_and_ns([(D,N)|DNs], [D|Ds], [N|Ns]):- ds_and_ns(DNs, Ds, Ns).


segment(Head, (B1,_B2), MutRec, true, B1):-
	member(SCC, MutRec),
	member(MRPred, SCC),
	fresh_all(Head, MRPred), 
	fresh_all(B1, FB1),
	member(FB1, SCC).
segment(Head, (B1,_B2), _MutRec, true, B1):-
	fresh_all(Head, FH), 
	fresh_all(B1, FH).
segment(Head, (B1,B2), MutRec, (B1, Segment), RecSubgoal):-
	segment(Head, B2, MutRec, Segment, RecSubgoal).


decrease_head(Head,S):-
	fresh_all(Head, Head_),
	functor(Head, _, N),
	user:lm(Head_, SHead), up_to_n(N,I),

	% zero is added since build_sum starts counting from 0
	%%% build_sum(Head, [0|SHead], I, S).
	build_sum(Head, SHead, [0|I], S).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

find_coeff(S, _Op, [], Exp):-
	find_no_var(S, Exp_),
	simplify_symb(Exp_, Exp).
find_coeff(S, Op, [V|Vars], S1):-
	find_coeff(S, V, L1_),
	simplify_symb(L1_, L1),
	(L1 = 0 -> S1 = S0 ; S1 = V*L1+S0),
	find_coeff(S, Op, Vars, S0).

find_coeff(V*Coeff, V, Coeff):- ! .
find_coeff(V,V,1) :-  ! .
find_coeff(E1+E2, V, L1+L2):-  ! ,
	find_coeff(E1,V,L1),
	find_coeff(E2,V,L2).
find_coeff(_, _, 0).

find_no_var(A*B, A*B):- \+ varname(A),  ! .
find_no_var(E1+E2, L1+L2):-  ! ,
	find_no_var(E1,L1),
	find_no_var(E2,L2).
find_no_var(A, A) :- \+ varname(A), \+ compound(A).
find_no_var(_, 0):-  ! . %%%%%% varname(A)

% first argument is a flag. if its value is after_construction
% then body should be normalised as well, otherwise only head
% should be changed
normalise(_, true, true).
normalise(F, (B1,B2), (B11,B21)):-
	 ! , normalise(F, B1,B11), normalise(F, B2,B21).
normalise(F, and(B1,B2), and(B11,B21)):-
	 ! , normalise(F, B1,B11), normalise(F, B2,B21).
normalise(_, [], []).
% if Body = true rewriting had no effect, thus, no normalisation is needed
normalise(after_rewrite, [implies(true, BuiltIns, Head)|Conditions],
	  [implies(true,BuiltIns, Head)|NConditions]):-
	 ! , normalise(after_rewrite, Conditions, NConditions).
normalise(after_rewrite, [implies(_Body, BuiltIns, Head)|Conditions],
	  [implies(_Body1,BuiltIns, Head1)|NConditions]):-
	 ! ,
	%timer('___'), 
	normalise(after_rewrite, Head, Head1),
	%timer('Normalise head '),
				   % while rewriting Head is the only
	                           % component that may change (1)
                                   % Body will be ignored by further steps
	normalise(after_rewrite, Conditions, NConditions).
normalise(after_construction, [implies(Body, BuiltIns, Head)|Conditions],
	  [implies(Body1,BuiltIns1, Head1)|NConditions]):-
	 ! ,
	normalise(after_construction, Head, Head1),
	normalise(after_construction, BuiltIns, BuiltIns1),
	normalise(after_construction, Body, Body1),
	normalise(after_construction, Conditions, NConditions).
normalise(_, T1=T2, T1=T2) :-  ! .
normalise(_, X < Y,  X < Y) :-  ! .
normalise(_, X =< Y, X =< Y) :-  ! .
normalise(_, X > Y,  X > Y) :-  ! .
normalise(_, X >= Y, X >= Y) :-  ! .
normalise(_, X =\= Y, X =\= Y) :-  ! .
%%%normalise(_, S1 #> 0, S1 #> 0):-  ! %, write('catch 1'), nl
	%%%.
%%%%normalise(_, S1 #>= 0, S1 #>= 0):-  ! %, write('catch 2'), nl
	%%%.

normalise(_, S1 #> 0, S0 #> 0):-  ! ,
	simplify_symb(S1,S0).
normalise(_, S1 #>= 0, S0 #>= 0):-  ! ,
	simplify_symb(S1,S0).
normalise(_, S1 #> S2, S0 #> 0):-
	simplify_symb(S1-S2,S0).
normalise(_, S1 #>= S2, S0 #>= 0):-
	simplify_symb(S1-S2,S0).
/*
normalise(_, S1 #> 0, T #> 0):-  ! ,
	simplify_symb(S1,S0),
	%timer(' > after simplification '),
	standart_form(S0 #> 0, #>, L),
	%timer(' > after standartisation '),
	to_sum(L, T).
normalise(_, S1 #>= 0, T #>= 0):-  ! ,
	simplify_symb(S1,S0),
	%timer(' >= after simplification '),
	standart_form(S0 #>= 0, #>=, L),
	%timer(' >= after standartisation '),
	to_sum(L, T).
normalise(_, S1 #> S2, T #> 0):-
	simplify_symb(S1-S2,S0),
	%timer(' > after simplification '),
	standart_form(S0 #> 0, #>, L),
	%timer(' > after standartisation '),
	to_sum(L, T).
normalise(_, S1 #>= S2, T #>= 0):-
	simplify_symb(S1-S2,S0),
	%timer(' >= after simplification '),
	standart_form(S0 #>= 0, #>=, L),
	%timer(' >= after standartisation '),
	to_sum(L, T).
*/


to_sum(L, T):-
	to_sum_(L, T_), simplify_symb(T_, T).
to_sum_([], 0).
to_sum_([H|T],EH+ET):-
	to_sum_(H, EH),
	to_sum_(T,ET).
to_sum_(_-[H|T], E):-  ! ,
	to_sum_([H|T], E).
to_sum_(novar-Coeff, Coeff) :-  ! .
to_sum_(V-Coeff, V*Coeff).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simplify_non_linear([], _, []).
simplify_non_linear([implies(_Body, BuiltIns, Head)|Conditions],
		    IntVars, Constraints):-
	%%%%% write('>< '), write(BuiltIns), write(' '), write(Head), nl,
	simplify(BuiltIns, Head, IntVars, HeadConstraints),
	simplify_non_linear(Conditions, IntVars, Constraints_),
	append(HeadConstraints, Constraints_, Constraints).

simplify(true, H,IntVars, C) :-
	get_DDV_integer_constraints([implies(_Body, true, H)],
				    IntVars, DDVConditions, IntConditions),
	append(DDVConditions, IntConditions, C).
simplify(BuiltIns,Head,_IntVars,C) :-
	simplify_symb(Head, Head1),
	standart_form(Head1, Op, List), ! ,
	mix_to_zero(List,C1, NonMixed),
	simplify_(BuiltIns, NonMixed,C1,Op,C).

simplify_(BuiltIns, NonMixed,C1,Op,C):-
	to_intervals(((_,BuiltIns), true),[_-Intervals]),
	approximate(NonMixed, Approximation, C2),
	get_constraints(Approximation, Op, Intervals, C3),
	append(C1,C2,C_), append(C3, C_, C).
simplify_(_BuiltIns, NonMixed,C1,Op,C):-
	ignore_non_linear_components(NonMixed,Op, C2),
	append(C1,C2,C).

ignore_non_linear_components([], _, []).
ignore_non_linear_components([_-Exp|Exps],Op, Constraints):-
	ignore_non_linear_components_(Exp,Op, C),
	ignore_non_linear_components(Exps,Op, Cs),
	append(C, Cs, Constraints).

ignore_non_linear_components_([], _, []).
ignore_non_linear_components_([novar-C, X-B|T], Op, [Term|S]) :-
	varname(X), zero_coeffs(T,S), Term =.. [Op, C+X*B,0].

standart_form(Head, Op, L):-
	Head =.. [Op, Exp, 0],
	standart_form_(Exp, L_),
	combine(L_,L__),
	separate(L__, L___),
	add_novar(L___,L).

standart_form_(E1+E2, L):-
	standart_form_(E1,L1),
	standart_form_(E2,L2),
	append(L1,L2,L).
standart_form_(E1*E2, [E-Coeff]):-
	varname(E1), ! ,
	inside_monom(E2,Vars,Coeff),
	(Vars = 1 ->
	    E = E1 ; E = E1*Vars).
standart_form_((E1*E2)*E3, X):-
	standart_form_(E1*(E2*E3),X).
standart_form_(E, [E-1]):-
	varname(E), ! .
standart_form_(E, [novar-E]).

inside_monom(E1*E2, E, Coeff):-
	varname(E1),  ! , inside_monom(E2, Vars, Coeff),
	(Vars = 1 -> E=E1; E=E1*Vars).
inside_monom(E, E, 1) :- varname(E),  ! .
inside_monom(E, 1, E).

separate_([], []).
separate_([E-Exp|T], [X-[E-Exp1]|S]):-
	simplify_symb(Exp, Exp1),
	diff_vars(E,X), separate_(T,S).
separate(List, Separated):-
	separate_(List, S),
	combine(S, S_),
	keysort(S_, Separated).

% zeroes coefficients of monoms involving more than one variable
mix_to_zero([], [], []).
mix_to_zero([[]-Exps|T], C, [[]-Exps|S]):-
	mix_to_zero(T,C,S).
mix_to_zero([[X]-Exps|T], C,[[X]-Exps|S]):-
	mix_to_zero(T,C,S).
mix_to_zero([[_,_|_]-Exps|T], C,S):-
	mix_to_zero_(Exps, C1, S1),
	mix_to_zero(T,C2,S2),
	append(C1,C2,C),
	(S1 = [] -> S = S2 ; S = [[]-S1|S2]).
	%%%append([[]-S1],S2,S).
mix_to_zero_([], [], []).
mix_to_zero_([novar-Exp|Exps], Cs, [novar-Exp|S]):-
	 ! , mix_to_zero_(Exps, Cs,S).
mix_to_zero_([_-Exp|Exps], [Exp #= 0|Cs], S):-
	mix_to_zero_(Exps, Cs, S).

% something more intelligent? ! 
add_novar([[]-[ExpN], V-Exp|T], [V-[ExpN|Exp]|T]) :-  ! .
add_novar(X,X).

%% approximate(NonMixed, Approximation, Constraints)
approximate([],  [], []).
approximate([_-Exp|Exps], [Approx|Approxs], Constraints):-
	approximate_(Exp, Approx, C),
	%%%%% write('> '), write(Exp), write(' '), write(Approx), nl,
	approximate(Exps, Approxs, Cs),
	append(C, Cs, Constraints).

approximate_([], [], []).
approximate_([novar-C, X-B, X*X-A|T], [X,C,B,A], S) :-
	varname(X), \+ A=0,  ! , zero_coeffs(T,S).
approximate_([novar-C, X-B|T], [X,C,B], S) :-
	varname(X), \+ B=0,  ! , zero_coeffs(T,S).
approximate_([novar-C|T],  [C], S) :-
	zero_coeffs(T,S).
approximate_([novar-C, X*X-A|T], [X,C,0,A], S) :-
	varname(X), \+ A=0,  ! , zero_coeffs(T,S).
approximate_([X-B, X*X-A|T], [X,0,B,A], S) :-
	varname(X), \+ A=0,  ! , zero_coeffs(T,S).
approximate_([X-B|T], [X,0,B], S) :-
	varname(X), \+ B=0,  ! , zero_coeffs(T,S).
approximate_([_|T], M, S):-
	approximate_(T, M, S).
/*
approximate_([X*X-A|T], [X,0,0,A], S) :-
	varname(X),  ! , zero_coeffs(T,S).
*/

zero_coeffs([], []).
zero_coeffs([_-Exp|T], [Exp #= 0|S]):-
	zero_coeffs(T,S).

ineq_member((X,Min,Max), [and(I,J)]):-
	ineq_member((X,Min,Max), I),
	ineq_member((X,Min,Max), J).
ineq_member((X,Min,_Max), X >= Min).
ineq_member((X,_Min,Max), X =< Max).

get_constraints_([[]], _, _, []).
get_constraints_([C], Op, _Intervals, [E]):-
	E =.. [Op, C, 0].
get_constraints_([X,C,B], Op, Intervals, E):-
	member((X,Min,Max), Intervals),
	 ! ,
	(number(B) ->
	    (B > 0 ->
		E1 =.. [Op, -C/B, Min]
	    ;
		E1 =.. [Op, Max, -C/B]),
	    E = [E1]
	;
	    (Op = '#>=', number(Min) ->
		B1 = B*Min+C,
		simplify_symb(B1,B2),
		E1 =.. [Op, B2, 0],
		E = [E1]
	    ; 
		(Op = '#=<', number(Max) ->
		    B1 = B*Max+C,
		    simplify_symb(B1,B2),
		    E1 =.. [Op, B2, 0],
		    E = [E1]
		; 
		    E1 =.. [#>=,C,0],
		    E2 =.. [#>=,B,0],
		    E = [E1,E2]))).
get_constraints_([_X,C,B], _Op, _Intervals, [E1,E2]):-
	E1 =.. [#>=,C,0],
	E2 =.. [#>=,B,0].
get_constraints_([X,C,B,A], Op, Intervals, [sqr_ineq(A,B,C,Min,Max,Op)]):-
	( member((X,Min,Max), Intervals)
	; member(and(X >= Min, X =< Max), Intervals)
	; member(and(X =< Max, X >= Min), Intervals)).

get_constraints([], _Op, _Intervals, []).
get_constraints([X|Xs], Op, Intervals, Css):-
	get_constraints_(X, Op, Intervals, C),
	get_constraints(Xs, Op, Intervals, Cs),
	append(C,Cs,Css).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rewrite([],[],[]).
rewrite([implies(Body,BuiltIns,Head)|Conditions],
	LinearConditions, NonlinearConditions):-
	prepare_body(Body, Body1, Equalities),
	rewrite(Body1, Head, Head0, _),
	apply_eq(Equalities, Head0, Head1, Degree),
	(Degree =< 1 ->
	    LinearConditions=[implies(Body,BuiltIns,Head1)|LinearConditions1],
	    NonlinearConditions = NonlinearConditions1
	;
	    LinearConditions = LinearConditions1,
	    NonlinearConditions =
	          [implies(Body,BuiltIns,Head1)|NonlinearConditions1]),
	rewrite(Conditions, LinearConditions1,NonlinearConditions1).
rewrite(true,H,H,0) :-  ! .
%%% since we rewrite only body part the only case
%%% when #> can appear is if > (or <) appeared in
%%% the original clause
rewrite(Exp #> 0, Head1, Head2, 0):-
	rewrite(Exp-1 #>=0, Head1, Head2, 0).
rewrite(Exp #>=0, Head1, Head2, 0):-
	Head1 =.. [Op,Exp1,0],
	simplify_symb(Exp1-Exp,Exp2),
	Head2 =.. [Op,Exp2,0].
rewrite(_V = _I mod _J, H, H, 0) :-  ! .
% the last if-then-else is added to ignore 
% nonlinear equations that are not used
rewrite(V1 = Exp2, Head1, Head2, N1):-
	degree(Exp2,N),
	rename(V1, Exp2, Head1, Head2),
	(Head1 = Head2 -> N1 = 0; N1 = N).
rewrite(and(B1,B2), Head1, Head2, Degree):-
	rewrite(B1, Head1, Head, Degree1),
	rewrite(B2, Head, Head2, Degree2),
	Degree is max(Degree1, Degree2).

% prepare_body distinguishes between #>, #>= and =
prepare_body(and(Exp #> 0, B1), and(Exp #> 0, B2), C):-
	 ! , prepare_body(B1, B2, C).
prepare_body(and(Exp #>= 0, B1), and(Exp #>= 0, B2), C):-
	 ! , prepare_body(B1, B2, C).
prepare_body(and(V = Exp, B1), B, [V = Exp|C]):-
	 ! , prepare_body(B1, B, C).
prepare_body(V = Exp, true, [V = Exp]) :-  ! .
prepare_body(X, X, []).

%in_exp(Var, Exp)
in_exp(Var, Var).
in_exp(Var, Exp):- Exp =.. [_,A1,_A2], in_exp(Var,A1).
in_exp(Var, Exp):- Exp =.. [_,_A1,A2], in_exp(Var,A2).

and_normalise_(and(and(A,B),C),and(A,and(B,C))) :-  ! .
and_normalise_(and(A,and(B,C)),and(A,L)) :- and_normalise_(and(B,C),L).
and_normalise(F,N) :- and_normalise_(F,F1), ! , and_normalise(F1,N).
and_normalise(F,F).

degree(X, 0) :- atomic(X).
degree(X, 1) :- varname(X).
degree(-X,N) :-
	degree(X,N).
degree(E1-E2,N):-
	degree(E1,N1),
	degree(E2,N2),
	N is max(N1,N2).
degree(E1+E2,N):-
	degree(E1,N1),
	degree(E2,N2),
	N is max(N1,N2).
degree(E1*E2, N):-
	degree(E1,N1),
	degree(E2,N2),
	N is N1+N2.
degree(E1/E2, N):-
	degree(E1,N1),
	degree(E2,N2),
	N is N1-N2.
degree(E1 mod E2, N):-
	degree(E1,N1),
	degree(E2,N2),
	N is max(N1,N2).

apply_eq([], H, H, 0):-  ! .
apply_eq([V = V|Eqs], H0, H1, D):-
	 ! , apply_eq(Eqs, H0, H1, D).
apply_eq([V = Exp|Eqs], H0, H1, D):-
	not_in_exps(V, [_=Exp|Eqs]), ! ,
	rewrite(V = Exp, H0, H, D1),
	apply_eq(Eqs, H, H1, D2),
	D is max(D1, D2).
apply_eq([V = Exp|_Eqs], _H0, _H1, _D):-
	in_exp(V, Exp),  ! ,
	write('Potential occur check problem.'), halt.
apply_eq([V = Exp|Eqs], H0, H1, D):-
	find_in_exp(V, Eqs, Ins, NotIns),
	rename(V, Exp, Ins, RenamedIns),
	rename(V, Exp, H0, H),
	append(NotIns,RenamedIns,All),
	apply_eq(All, H, H1, D).

not_in_exps(_, []).
not_in_exps(V, [_ = Exp|Eqs]):-
	\+ in_exp(V, Exp),
	not_in_exps(V, Eqs).

find_in_exp(_, [], [], []).
find_in_exp(V, [V1 = Exp1|Eqs], [V1 = Exp1|Ins], NotIns):-
	in_exp(V, Exp1), find_in_exp(V, Eqs, Ins, NotIns).
find_in_exp(V, [V1 = Exp1|Eqs], Ins, [V1 = Exp1|NotIns]):-
	find_in_exp(V, Eqs, Ins, NotIns). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get_intvars(Clauses, IntVars):-
	get_intvars_(Clauses, IVs),
	list_to_ord_set(IVs, IntVars).
get_intvars_(true, []) :-  ! .
get_intvars_([],[]) :-  ! .
get_intvars_([clause(Head,Body)|Clauses], IntVars):-
	get_intvars_(Head, I),
	get_intvars_(Body, II),
	get_intvars_(Clauses, III),
	append(I,II,I_), append(I_,III, IntVars).
get_intvars_([_|Clauses], IntVars):-  ! ,
	get_intvars_(Clauses, IntVars).
get_intvars_((B1,B2), IntVars):- 
	get_intvars_(B1, I),
	get_intvars_(B2, II),
	append(I,II,IntVars).
get_intvars_(Head, IntVars) :-
	fresh_all(Head, Head1),
	original_free_atom(Head1, Head2, _),
	user:iap((Head2-IntArgs)), ! ,
	get_args(IntArgs, Head, IntVars).
get_intvars_(_, []).

get_args([], _, []).
get_args([Arg|Args], Head, [IV|IVs]):-
	arg(Arg, Head, IV),
	varname(IV),  ! ,
	get_args(Args, Head, IVs).
get_args([_Arg|Args], Head, IVs):-
	get_args(Args, Head, IVs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
get_DDV_integer_constraints([], _, [], []) :-  ! .
get_DDV_integer_constraints([implies(_Body, BuiltIns, Head)|Conditions],
			    IntVars, DDVConditions, IntConditions) :-  ! ,
	get_DDV_integer_constraints(Head, IntVars, DDVC, IntC),
	get_DDV_integer_constraints(Conditions, IntVars, DDVCs, IntCs),
	get_builtins_integer_constraints(BuiltIns, BuiltInsIntCs),
	append(DDVC, DDVCs, DDVConditions),
	append(IntC, IntCs, IC),
	append(IC,BuiltInsIntCs,IntConditions).

get_DDV_integer_constraints(true, _, [], []):- ! .
get_DDV_integer_constraints(Head, IntVars, DDVC, IntConditions) :-
	standart_form(Head, Op, L),
	get_DDV_integer_constraints_(L, Op, IntVars, DDVC, IntSums),
	get_integer_constraints(IntSums, Op, IntConditions).
get_DDV_integer_constraints_([], _, _, [], []).
get_DDV_integer_constraints_([[]-Cond|Conds], Op, IntVars,
			     DDVConditions, IntSums):-
	get_DDV_constraints(Cond, Op, DDVC),
	get_DDV_integer_constraints_(Conds, Op, IntVars, DDVCs, IntSums),
	append(DDVC, DDVCs, DDVConditions).
get_DDV_integer_constraints_([[V]-Cond|Conds], Op, IntVars,
			     DDVConditions, IntSums):-
	 ! , (member(V, IntVars) ->
	    IntS = Cond, % get_integer_constraints(Cond, Op, IntC)
	    DDVC = []
	;
	    get_DDV_constraints(Cond, Op, DDVC),
	    IntS = []),
	get_DDV_integer_constraints_(Conds, Op, IntVars, DDVCs, IntSs),
	append(DDVC, DDVCs, DDVConditions),
	append(IntS, IntSs, IntSums).

get_DDV_integer_constraints_([[_|_]-Cond|Conds], Op, IntVars,
			     DDVConstraints, IntSums):-
	zero_constraints(Cond, Op, Cons),
	get_DDV_integer_constraints_(Conds, Op, IntVars, DDVCs, IntSums),
	append(Cons, DDVCs, DDVConstraints).

zero_constraints([], _, []).
zero_constraints([novar-Cond|Conds], Op, [Constr|Constrs]):-
	 ! , Constr =.. [Op, Cond, 0],
	zero_constraints(Conds, Op, Constrs).
zero_constraints([_-Cond|Conds], Op, [Constr|Constrs]):-
	Constr =.. [#=, Cond, 0],
	zero_constraints(Conds, Op, Constrs).

get_DDV_constraints([], _, []).
get_DDV_constraints([novar-Exp|Exps], Op, [E|Conds]):-  ! ,
	E =.. [Op, Exp, 0], get_DDV_constraints(Exps, Op, Conds).
get_DDV_constraints([_V-Exp|Exps], Op, [Exp #>= 0|Conds]):-
	get_DDV_constraints(Exps, Op, Conds).

get_integer_constraints([], _, []) :-  ! .
get_integer_constraints(Cond, Op, [E]) :-
	to_sum(Cond, Exp), E =.. [Op, Exp, 0].

get_builtins_integer_constraints(true, []).
get_builtins_integer_constraints((B1,B2), [builtin(B1)|L2]) :-
	get_builtins_integer_constraints(B2, L2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% frz_integer_clauses freezes clauses of the program
% however, clauses of predicates with integer argument
% positions are frozen together

frz_integer_clauses(Clauses, FClauses):-
	clauses_int_nonint(Clauses,IntClauses,NonIntClauses),
	frz(IntClauses,FIntClauses),
	diff_vars(FIntClauses,Vs), max_number(Vs, N),
	N1 is N+1,
	frzl(NonIntClauses,N1,FNonIntClauses),
	append(FIntClauses, FNonIntClauses, FClauses).

max_number([], 0).
max_number([X|Xs],K):- varname(X,V), max_number(Xs,L), K is max(V,L).

clauses_int_nonint([], [], []).
clauses_int_nonint([clause(Head,Body)|Clauses],
		   [clause(Head,Body)|IntClauses],NonIntClauses):-
	fresh_all(Head, Head1),
	original_free_atom(Head1,Head2,_),
	user:iap(Head2-[_|_]),  ! ,
	clauses_int_nonint(Clauses, IntClauses, NonIntClauses).
clauses_int_nonint([clause(Head,Body)|Clauses],
		   IntClauses,[clause(Head,Body)|NonIntClauses]):-
	clauses_int_nonint(Clauses, IntClauses, NonIntClauses).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

find_predicates(Assumptions, Clauses, Predicates):-
	find_predicates_(Assumptions, Clauses, Ps_),
	keysort(Ps_, Ps),
	combine_predicates(Ps, Predicates).

combine_predicates([], []).
combine_predicates([X], [X]).
combine_predicates([Pred-C1, Pred-C2|Ps], T):-
	 ! , combine_predicates([(Pred-and(C1, C2))|Ps], T).
combine_predicates([Pred1-C1, Pred2-C2|Ps], [Pred1-C1|T]):-
	combine_predicates([Pred2-C2|Ps], T).

find_predicates_([], _Clauses, []).
find_predicates_([Assumption|Assumptions], Clauses, [PC|PCs]):-
	find_predicate(Assumption, Clauses, PC),
	find_predicates_(Assumptions, Clauses, PCs).

find_predicate(Assumption, [], _):-
	write('The assumption '), write(Assumption),
	write(' needed for proving termination '), nl,
	write('cannot be imposed since it depends on variables in the clause body '), nl,
	fail.
find_predicate(Assumption, [clause(Head,_Body)|_Clauses],
	       Predicate-Condition) :-
	diff_vars(Assumption, VarsAssumption),
	diff_vars(Head, VarsHead),
	list_to_ord_set(VarsAssumption, VA),
	list_to_ord_set(VarsHead, VH),
	ord_subset(VA, VH),  ! ,
	tune(VH,Assumption, Assumption1),
	fresh_all(Head, Head_),
	original_free_atom(Head_, Predicate, _Adornment),
	apply(Assumption1, Predicate, Condition).
find_predicate(Assumption, [clause(_Head,_Body)|Clauses], Predicate) :-
	find_predicate(Assumption, Clauses, Predicate).

tune(VH, Assumption, Assumption1):-
	melt((VH, Assumption), (V, A)),
	frz((V, A), (_, Assumption1)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

prove_termination(_Preds, _IO, _Calls, _Clauses,
		  [], _MutRec, _D, [], _Predicates):-
	 ! , write('There is no recursion in this program.'), nl.
prove_termination(_Preds, _IO, [],  _Clauses,
		  _Rec, _MutRec, _D, _Assumptions, _Predicates):-
	 ! , write('The call set is empty'), nl.
prove_termination(Preds, IO, Calls, Clauses,
		  _Rec, MutRec, D, Assumptions, Predicates):-
	functors(Clauses, Functors),
	initialize_symbolic_constraints(Preds, Functors),
	assert_list(io,IO),
	rigidity_conditions(Calls, RigidityConditions),
	frz_integer_clauses(Clauses, FClauses),

%%%%	aux:writel(FClauses),
	
	get_intvars(FClauses, IntVars),
%%%%	write(IntVars),
%%%%	timer('Loop Termination Proof Init '),
	
		
	decrease_conditions(FClauses, MutRec, NeededForModelConditions, L1_), 
%%%%	aux:writel(L1_),	
	%%%%timer('Loop Termination Proof Decrease Conditions '),

	model_conditions(FClauses, NeededForModelConditions, L_),
%%%	aux:writel(L_),	
	%%%%timer('Loop Termination Proof Model Conditions '),

	append(L_, L1_,LL_),
	normalise(after_construction, LL_, NLL),

	%%%%timer('Loop Termination Proof Normalise1 '),
	rewrite(NLL, LinearConditions, NonlinearConditions),
	%%%%timer('Loop Termination Proof Rewrite '),
	
%%%%	write('LINEAR'), nl,
%%%%	aux:writel(LinearConditions), nl,
%%%%	write('NON-LINEAR'), nl,
%%%%	aux:writel(NonlinearConditions), nl,
	normalise(after_rewrite, LinearConditions, NRLL1),
	%%% timer('Loop Termination Proof Normalise2 '),
	normalise(after_rewrite, NonlinearConditions, NRLL2),
	%%% timer('Loop Termination Proof Normalise3 '),
%	write('NRLL1'),nl,
%	aux:writel(NRLL1),
%	write('NRLL2'),nl,
%	aux:writel(NRLL2),
%	append(NRLL1, NRLL2, NRLL),

	get_DDV_integer_constraints(NRLL1, IntVars, C_, IC), ! ,
	%%% timer('Loop Termination Proof DDV int '),

	simplify_non_linear(NRLL2, IntVars, CNL),
	%%% timer('Loop Termination Proof Simplify '),
%	%%% write('Simplified'),nl,
	aux:writel(CNL),
	append(C_, CNL, C0),
	append(IC, C0, C1),
	append(RigidityConditions, C1, C2),
	sort(C2,C),
%write('All '), nl,
%aux:writel(C),
	%%%%timer('Normalise, Rewrite, ... '),
	 ! ,
	(solve(C,IntVars,D, Assumptions1) ->
	    (find_predicates(Assumptions1, FClauses, Predicates) ->
		Assumptions = Assumptions1
	    ;
		Assumptions = false)
	;
	    Assumptions = false).

/*

:- prove_termination(['q_#VAR(0)_>_#VAR(1)'(_,_), 'q_#VAR(0)_=<_#VAR(1)'(_,_)],
	 [('q_#VAR(0)_>_#VAR(1)'(_,_), [1,2], []),
	     ('q_#VAR(0)_=<_#VAR(1)'(_,_), [1,2], [])],
	['q_#VAR(0)_>_#VAR(1)'(a,a), 'q_#VAR(0)_=<_#VAR(1)'(a,a)],
	[clause('q_#VAR(0)_>_#VAR(1)'(_C,_D),
		(_C>_D,_E is _C-_D,_F is _D+1,
		    'q_#VAR(0)_>_#VAR(1)'(_E,_F),true)),
	 clause('q_#VAR(0)_>_#VAR(1)'(_G,_H),
		(_G>_H,_I is _G-_H,_J is _H+1,
		    'q_#VAR(0)_=<_#VAR(1)'(_I,_J),true))],
	[], D, Assum, P).
:- prove_termination([permute(_,_), delete(_,_,_)],
     [(delete(_,_,_), [2], [1,3]),
	       (permute(_,_), [1], [2])],
     [delete(_,[_],_), permute([_],_)],
	[clause(delete(X,[X|T],T), true),
	 clause(delete(X,[H|T],[H|T1]),
		(delete(X,T,T1), true)),
	 clause(permute([],[]), true),
	 clause(permute(L, [El|T]),
		(delete(El,L,L1), permute(L1,T), true))
	], [], D, Assum).

:- Clauses =
	[clause(append([],L,L), true),
	 clause(append([H|T1],T2,[H|T3]),
		(append(T1,T2,T3), true)),
	 clause(quicksort([X|Xs],Ys),
                (partition(Xs,X,Littles,Bigs),
		    quicksort(Littles,Ls),
		    quicksort(Bigs,Bs),
		    append(Ls,[X|Bs],Ys),
		    true)),
	 clause(quicksort([],[]), true),
	 clause(partition([X|Xs],Y,[X|Ls],Bs),
		(X =< Y, partition(Xs,Y,Ls,Bs), true)),
	 clause(partition([X|Xs],Y,Ls,[X|Bs]),
		(X >  Y, partition(Xs,Y,Ls,Bs), true)),
	 clause(partition([],Y,[],[]), true)],
	
     prove_termination([quicksort(_,_), append(_,_,_), partition(_,_,_,_)],
	  [(quicksort(_,_), [1], [2]),
	       (append(_,_,_), [1,2], [3]),
	       (partition(_,_,_,_), [1,2], [3,4])],
     [quicksort(a,_),append([_],[_],_), partition(a,a,_,_)],
	Clauses, [], D, Assum).

:- Clauses =
	[
	 clause('p_in(#VAR(0),2,999)'(_B),(_B>1,_B<1000,_C is-(_B*_B),'p_in(#VAR(0),-999,-2)'(_C),true)),
	 clause('p_in(#VAR(0),2,999)'(_D),(_D>1,_D<1000,_E is-(_D*_D),'p_or(in(#VAR(0),-inf,-1000)_,_or(in(#VAR(0),-1,1)_,_in(#VAR(0),1000,inf)))'(_E),true)),
	 clause('p_in(#VAR(0),-999,-2)'(_F),(_F< -1,_F> -1000,_G is _F*_F,'p_in(#VAR(0),2,999)'(_G),true)),
	 clause('p_in(#VAR(0),-999,-2)'(_H),(_H< -1,_H> -1000,_I is _H*_H,'p_or(in(#VAR(0),-inf,-1000)_,_or(in(#VAR(0),-1,1)_,_in(#VAR(0),1000,inf)))'(_I),true))],
	prove_termination(['p_in(#VAR(0),2,999)'(_B),'p_in(#VAR(0),-999,-2)'(_C),
	      'p_or(in(#VAR(0),-inf,-1000)_,_or(in(#VAR(0),-1,1)_,_in(#VAR(0),1000,inf)))'(_E)],
	     [('p_in(#VAR(0),2,999)'(_), [1], []),
		  ('p_in(#VAR(0),-999,-2)'(_), [1], []),
		  ('p_or(in(#VAR(0),-inf,-1000)_,_or(in(#VAR(0),-1,1)_,_in(#VAR(0),1000,inf)))'(_), [1], [])],
	     ['p_in(#VAR(0),2,999)'(a),'p_in(#VAR(0),-999,-2)'(a),
	      'p_or(in(#VAR(0),-inf,-1000)_,_or(in(#VAR(0),-1,1)_,_in(#VAR(0),1000,inf)))'(a)],
	     Clauses, 
	     [['p_in(#VAR(0),2,999)'(_B),'p_in(#VAR(0),-999,-2)'(_C)]],
	     D, Assum).


:- Clauses =
	[
	 clause('p_in(#VAR(0),2,999)'(_B),(_B>1,_B<1000,_C is-(_B*_B),'p_in(#VAR(0),-999,-2)'(_C),true))],
	prove_termination(['p_in(#VAR(0),2,999)'(_B),'p_in(#VAR(0),-999,-2)'(_C)],
	     [('p_in(#VAR(0),2,999)'(_), [1], []),
		  ('p_in(#VAR(0),-999,-2)'(_), [1], [])],
	     ['p_in(#VAR(0),2,999)'(a),'p_in(#VAR(0),-999,-2)'(a)],
	     Clauses, 
	     [['p_in(#VAR(0),2,999)'(_B),'p_in(#VAR(0),-999,-2)'(_C)]],
	     D, Assum).


prove_termination(['p_in(#VAR(0),1,inf)'(_B),'p_in(#VAR(0),-inf,0)'(_A)],
     [('p_in(#VAR(0),1,inf)'(_B), [1], []),
	  ('p_in(#VAR(0),-inf,0)'(_A), [1], [])],
     ['p_in(#VAR(0),1,inf)'(a),'p_in(#VAR(0),-inf,0)'(a)],
     [clause('p_in(#VAR(0),1,inf)'(_B),(_B>0,_C is _B-1,'p_in(#VAR(0),1,inf)'(_C),true)),
      clause('p_in(#VAR(0),1,inf)'(1),(1>0,0 is 1-1,'p_in(#VAR(0),-inf,0)'(0),true))],
     [], D, Assum).

prove_termination(['p_in(#VAR(0),-inf,99)'(_B),'p_in(#VAR(0),100,inf)'(_)],
     [('p_in(#VAR(0),-inf,99)'(_B),[1], []),
	  ('p_in(#VAR(0),100,inf)'(_), [1], [])],
     ['p_in(#VAR(0),-inf,99)'(a),'p_in(#VAR(0),100,inf)'(a)],
     [clause('p_in(#VAR(0),-inf,99)'(_B),(_B<100,_C is _B+1,'p_in(#VAR(0),-inf,99)'(_C),true)),
      clause('p_in(#VAR(0),-inf,99)'(99),(99<100,100 is 99+1,'p_in(#VAR(0),100,inf)'(100),true))],
     [], D, Assum).
*/




