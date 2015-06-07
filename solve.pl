:- module(solve, [solve/4]).

:- use_module(library(clpfd)).
:- use_module(library(clpq)).
:- use_module(library(lists), [append/3, reverse/2]).
:- use_module(library(ordsets), [ord_intersection/4]).
:- use_module(numvars, [sym_melt/3, diff_vars/2, melt/2, varname/1]).
:- use_module(aux, [all_in/2, writel/1]).
:- use_module(simplify_symb, [simplify_symb/2]).

solve(C_,IntVars,D,Assumptions) :- !,
	copy_term(C_, C),

	sym_melt(C,MC,D),
	diff_vars(MC, Vs_),
	gr_eq(Vs_, Vs),

	solve1(D, C, MC, Rest, 1), % dictionary, c and number are
				   % added for debug purposes
	
	prepare_for_solve2_and_3(Rest, IntVars, Rest12, Rest13),
	
	diff_vars(Rest12,VVs), 
	sort(Vs, Vs1),
	ord_intersection(VVs, Vs1, Intersect, Diff),
	labeling([],Intersect),

	%%%%write('Trying '), write(Intersect), nl,
	%%%%write(D), nl,
	
	solve2(Rest12,Rest22),
	(\+ Rest22 = [] ->
	    write('*******>>> Internal Error ************'),nl
	;
	    true),

	
	diff_vars(Rest13, V13),
	
	ord_intersection(V13, Diff, Intersect2, Diff2),

	flag(Flag),
	
	labeling([], Intersect2),
	
	simplify_l(Rest13, Rest131),
	
	melt(Rest131,MRest),

	solve3(Rest131,MRest, Flag, Assumptions),
	(\+ Assumptions = [] ->
	      write('*** Assumptions ***'), nl,
	      writel(Assumptions),
	    true
	;
	    true),
	labeling([], Diff2),
	filter(D),nl.

flag(no_assumptions).
flag(assumptions).

prepare_for_solve2_and_3([], _, [], []).
prepare_for_solve2_and_3([sqr_ineq(A,B,C,Min,Max,Op)|Conds], IntVars,
			 [sqr_ineq(A,B,C,Min,Max,Op)|Solve2Conds],
			 Solve3Conds):- !,
	prepare_for_solve2_and_3(Conds, IntVars, Solve2Conds, Solve3Conds).
/*
prepare_for_solve2_and_3([X<Y|Conds],[X<Y|Solve2Conds],Solve3Conds):-!,
	prepare_for_solve2_and_3(Conds, Solve2Conds, Solve3Conds).
prepare_for_solve2_and_3([X=<Y|Conds],[X<Y|Solve2Conds],Solve3Conds):-!,
	prepare_for_solve2_and_3(Conds, Solve2Conds, Solve3Conds).
*/
prepare_for_solve2_and_3([builtin(X)|Conds],IntVars, Solve2Conds,
			 [builtin(X)|Solve3Conds]):-
	diff_vars(X,Vs), all_in(Vs, IntVars), !,
	prepare_for_solve2_and_3(Conds, IntVars, Solve2Conds, Solve3Conds).
% see Sterling Shapiro 8.9; we do not consider arguments of maximum
% as integers, since there is, in fact, no integer computation
% built-ins like these can be ignored
prepare_for_solve2_and_3([builtin(_)|Conds],IntVars, Solve2Conds,Solve3Conds):-
	!, prepare_for_solve2_and_3(Conds, IntVars, Solve2Conds, Solve3Conds).
prepare_for_solve2_and_3([X|Conds],IntVars, Solve2Conds,[X|Solve3Conds]):-
	prepare_for_solve2_and_3(Conds, IntVars, Solve2Conds, Solve3Conds).

gr_eq([],[]).
gr_eq([V|Vs],VVs):-
	\+ var(V),
	varname(V),!,
	gr_eq(Vs,VVs).
gr_eq([V|Vs],[V|VVs]):-
	V in 0..3, % usually 0..1 for pl8.4.2 cange to 0..3
	gr_eq(Vs,VVs).

% first of all consider comparisons that do not depend on '#VAR'-iables
solve1(_, [], [],[], _).
solve1(D, [true|Zs], [true|Xs], Ys, N):-
	!, N1 is N+1, solve1(D, Zs, Xs, Ys, N1).
solve1(D, [Z|Zs], [X|Xs], Ys, N):-
	check(X),
	!, (X -> true ; write(N), write(': '),write(Z),
	       write(' '), write(X), nl, filter(D) ,fail),
	N1 is N+1,
	solve1(D, Zs, Xs, Ys, N1).
solve1(D, [_Z|Zs], [X|Xs], [X|Ys],N):-N1 is N+1,
	solve1(D, Zs, Xs, Ys,N1).


check(X):- var(X), !.
check(X):- number(X), !.
check(X):-
	compound(X),
	X =.. [_,Y,Z],
	check(Y), check(Z).


simplify_l([], []).
simplify_l([X|Xs], [SX|SXs]):-
	simplify_symb(X,SX),!,
	simplify_l(Xs, SXs).

solve2(true, []).
solve2([], []).
solve2([sqr_ineq(A,B,C,Min,Max,Op)|Xs], Ys):-
	!,
	sqr_ineq(A,B,C,Min,Max,Op),
	solve2(Xs, Ys).
solve2((Exp,Exps), Ys):-
	solve2([Exp], Ys1),
	solve2(Exps, Ys2),
	append(Ys1, Ys2, Ys).
solve2([(Exp,Exps)|Expss], Ys):-
	solve2([Exp], Ys1),
	solve2(Exps, Ys2),
	solve2(Expss, Ys3),
	append(Ys1, Ys2, Ys_),
	append(Ys_, Ys3, Ys).
solve2([X<Y|Xs], Ys):-
	X #< Y, !,
	solve2(Xs, Ys).
solve2([X=<Y|Xs], Ys):-
	X #=< Y, !,
	solve2(Xs, Ys).
solve2([X|Xs], [X|Ys]):-
	solve2(Xs,Ys).

filter(X):- var(X),!.
filter(dict(_Var,0,Left,Right)):-
	!, filter(Left), filter(Right).
filter(dict(Var,N,Left,Right)):-
	write((Var,N)),nl,
	filter(Left), filter(Right).

compare_fi(Op,KFloat,Int):-
	K is integer(KFloat),
	(KFloat > K ->
	    E =.. [#>=,K,Int]
	;
	    (KFloat =:= K ->
		E =.. [Op,K,Int]
	    ;			% KFloat < K
		K1 is K-1,
		E =.. [#>=,K1,Int])
	),
	!, E.

compare_if(Op,Int,KFloat):-
	K is integer(KFloat),
	(KFloat > K ->
	    K1 is K+1, 
	    E =.. [#>=,Int,K1]
	;
	    (KFloat =:= K ->
		E =.. [Op,Int,K]
	    ;			% KFloat < K
		E =.. [#>=,Int,K])
	),
	!, E.

sqr_ineq(A,B,C,_,_,Op):-
	%%%%write('Case 1'), nl,
	E1 =.. [#=, A, 0], E1,
	E2 =.. [#=, B, 0], E2, !,
	E =.. [Op,C,0], E.
sqr_ineq(A,B,C,Min,_,Op):-
	%%%%%%write('Case 2'), nl,
	E1 =.. [#=, A, 0], E1,
	E2 =.. [#>, B, 0], E2, !,
	KFloat is -C/B,
	compare_fi(Op,KFloat,Min).
sqr_ineq(A,B,C,_,Max,Op):-
	%%%%%%write('Case 3'), nl,
	E1 =.. [#=, A, 0], E1,
	E2 =.. [#<, B, 0], E2, !,
	KFloat is -C/B,
	compare_if(Op,Max,KFloat).
sqr_ineq(A,B,C,_,_,_):-
	%%%%%%write('Case 4'), nl,
	E1 =.. [#>, A, 0], E1,
	D is B*B-4*A*C,
	E2 =.. [#<, D, 0], E2.
sqr_ineq(A,B,C,_Min,_Max,#=<):-
	%%%%%%write('Case 5'), nl,
	E1 =.. [#>, A, 0], E1,
	D is B*B-4*A*C,
	E2 =.. [#=, D, 0], E2.
sqr_ineq(A,B,C,_Min,Max,Op):-
	%%%%%%write('Case 6'), nl,
	E1 =.. [#>, A, 0], E1,
	D is B*B-4*A*C,
	E2 =.. [#>, D, 0], E2,
	X1Float is (-B-sqrt(B*B-4*A*C)/(2*A)),
	compare_fi(Op,X1Float,Max).
sqr_ineq(A,B,C,Min,_Max,Op):-
	%%%%%%write('Case 7'), nl,
	E1 =.. [#>, A, 0], E1,
	D is B*B-4*A*C,
	E2 =.. [#>, D, 0], E2,
	X2Float is (-B+sqrt(B*B-4*A*C)/(2*A)),
	compare_if(Op,Min,X2Float).
sqr_ineq(A,B,C,Min,Max,Op):-
	%%%%%%write('Case 8'), nl,
	E1 =.. [#<, A, 0], E1, 
	E2 =.. [#>=, B*B-4*A*C, 0], E2, 
	X1Float is (-B-sqrt(B*B-4*A*C)/(2*A)),
	X2Float is (-B+sqrt(B*B-4*A*C)/(2*A)),
	compare_if(Op,Min,X1Float),
	compare_fi(Op,X2Float,Max).

solve3(Fs,Xs,Flag,Ass):-
	prepare_builtins_rest(Fs,Xs,Bs,FOs,Os),
	solve3_b(Bs),
	solve3_(FOs,Os,Flag,Ass).

prepare_builtins_rest([],[],[],[],[]).
prepare_builtins_rest([builtin(_F)|Fs],[builtin(X)|Xs],[X|Bs],FOs,Os):-
	!, prepare_builtins_rest(Fs,Xs,Bs,FOs,Os).
prepare_builtins_rest([F|Fs],[X|Xs],Bs,[F|FOs],[X|Os]):-
	prepare_builtins_rest(Fs,Xs,Bs,FOs,Os).

solve3_([], [], _, []).
solve3_([_F|Fs], [X|Xs], Flag, Ys):-
	%% the constraint is ground
	ground(X), !,
	X, solve3_(Fs, Xs, Flag, Ys).
solve3_([_F|Fs], [X|Xs], Flag, Ys):-
	%% the constraint is entailed by previously added constraints
	Op =.. [#<=>,X,B], Op,
	(
	  B==1	% you can not substitute 1 instead of B, since that will
	        % succeed if there are some values satisfying X
	  %, write('CLPFD - entailed')
	;
	  remove_dies(X,Y),
	  entailed(Y)
	  %, write('CLPQ - entailed')
	    ),
	!,
	solve3_(Fs, Xs, Flag, Ys).
solve3_([F|Fs], [X|Xs], assumptions, [F|Ys]):-
	X, !, 
	solve3_(Fs, Xs, assumptions, Ys).
% if the flag is set to no_assumptions solve3_ should be satisfied
% by one of the three first clauses.

remove_dies(X #< Y, X < Y).
remove_dies(X #> Y, X > Y).
remove_dies(X #=< Y, X =< Y).
remove_dies(X #>= Y, X >= Y).
remove_dies(X #\= Y, X =\= Y).
remove_dies(X #= Y, X = Y).

solve3_b([]).
solve3_b([X|Xs]):-
	ground(X), !,
	X, solve3_b(Xs).
solve3_b([X>Y|Xs]):-
	Op =.. [#>,X,Y], Op, {X>Y}, !, 
	solve3_b(Xs).
solve3_b([X>=Y|Xs]):-
	Op =.. [#>=,X,Y], Op, {X>=Y},!, 
	solve3_b(Xs).
solve3_b([X<Y|Xs]):-
	Op =.. [#<,X,Y], Op, {X<Y},!, 
	solve3_b(Xs).
solve3_b([X=<Y|Xs]):-
	Op =.. [#=<,X,Y], Op, {X=<Y},!,
	solve3_b(Xs).
solve3_b([X=Y mod Z|Xs]):- !,
	Op1 =.. [#>,Y,X], Op1,{Y>X},
	Op2 =.. [#>,Z,X], Op2,{Z>X},
	!, solve3_b(Xs).
solve3_b([X=Y|Xs]):-
	Op =.. [#=,X,Y], Op, {X=Y},!,
	solve3_b(Xs).
solve3_b([X=\=Y|Xs]):-
	Op =.. [#\=,X,Y], Op, {X=\=Y},!,
	solve3_b(Xs).










