:- module(intervals, [interval_to_conjunct/2,extend/2, partition/3,
		      to_intervals/2, tree_to_list_/3,
		      list_to_tree/3, simplify/2]).

:- use_module(library(lists), [append/3, member/2, nth0/3, nth/3]).

%% used for testing and debugging
:- use_module(library(random), [random/3]).
:- use_module(atom, [built_in/1, comparison/1, fresh_all/2]).
:- use_module(aux, [flatten/2, rename/4, time/1, timer/1, id_member/2]).
:- use_module(numvars, [frz/2, melt/2, varname/1, varname/2, vars/2]).
:- use_module(rec, [rec/6]).
:- use_module(simplify_symb, [combine/2]).
:- use_module(check_clp, [check_clp_/1]).

%%% (Min,Max) stays for [Min,Max], i.e., Min =< X =< Max

less(-inf,_X):-!.
less(_X,inf):-!.
less(X,Y):- X < Y.

eq(X, X) :- var(X), !.
eq(X, X) :- number(X), !.

% intervals

eq((_,-inf,-inf), false).
eq((_,inf, inf), false).
eq((_,-inf, inf), true).

eq((X,Min,inf), (X >= Min)) :- !.
eq((X,-inf,Max), (X =< Max)) :- !.
eq((X,Min,Max), and(X >= Min, X =< Max)) :- !.

eq(not((_X,-inf, inf)), false) :- !.
eq(not((_X,-inf, -inf)), true) :- !.
eq(not((_X,inf, inf)), true) :- !.
eq(not((X,Min,inf)), (X, -inf, Min1)):- !, Min1 is Min - 1.
eq(not((X,-inf,Max)), (X, Max1, inf)):- !, Max1 is Max + 1.
eq(not((X,Min,Max)),or((X,-inf,Min1),(X,Max1,inf))) :-
	Min1 is Min - 1, Max1 is Max + 1.
eq(not(not(X)), X) :- !.
eq(or((X,A,B),(Y,A,C)),(X,A,B)) :- X == Y, less(C,B), !.
eq(or((X,A,B),(Y,A,C)),(X,A,C)) :- X == Y,less(B,C), !.
eq(or((X,A,B),(Y,B,C)),(X,A,C)) :- X == Y.
eq(or((X,A,B),(Y,C,D)),(X,A,B)) :-
	X == Y,
	less(C,B), less(A,C),
	less(D,B), less(A,D), !.
eq(or((X,A,B),(Y,C,D)),(X,C,D)) :-
	X == Y,
	less(C,A), less(A,D),
	less(C,B), less(B,D), !.
eq(or((X,A,B),(Y,C,D)),(X,A,D)) :-
	X == Y,
	less(A,C), less(C,B), less(B,D), !.
eq(or((X,A,B),(Y,C,D)),(X,C,B)) :-
	X == Y,
	less(C,A), less(A,D), less(D,B), !.
eq(or((X,C,D),(Y,A,B)),(X,C,D)) :-
	X == Y,
	less(A,D), less(C,A),
	less(B,D), less(C,B), !.
eq(or((X,C,D),(Y,A,B)),(X,A,B)) :-
	X == Y,
	less(D,B), less(A,C),
	less(C,B), less(A,D), !.
eq(or((X,C,D),(Y,A,B)),(X,C,B)) :-
	X == Y,
	less(C,A), less(A,D), less(D,B), !.
eq(or((X,C,D),(Y,A,B)),(X,A,D)) :-
	X == Y,
	less(A,C), less(C,B), less(B,D), !.
eq(or((X,A,B),(Y,C,D)),(X,A,D)) :- X == Y,C is B+1, !.
eq(or((X,C,D),(Y,A,B)),(X,A,D)) :- X == Y,C is B+1, !.
eq(or((X,A,B),(Y,C,D)),(X,C,B)) :- X == Y,A is D+1, !.
eq(or((X,C,D),(Y,A,B)),(X,C,B)) :- X == Y,A is D+1, !.

eq(and((X,A,_B),(Y,_C,D)),false):- X == Y,less(D,A), !.
eq(and((X,_A,B),(Y,C,_D)),false):- X == Y,less(B,C), !.
eq(and((X,A,B),(Y,C,D)),(X,Z,T)):-
	X == Y,
	(less(A,C) -> Z=C; Z=A),!,
	(less(D,B) -> T=D; T=B).

% logic, general
eq(not(true),false).
eq(not(false),true).
eq(not(and(I1,I2)),or(not(I1),not(I2))).
eq(not(or(I1,I2)),and(not(I1),not(I2))).
eq(or(false,A),A).
eq(or(A,false),A).
eq(or(true,_A), true).
eq(or(_A,true), true).
eq(or(I,J),I):- I == J, !.
eq(or(A,and(A,_)), A) :- !.
eq(or(A,and(_,A)), A) :- !.
eq(or(and(A,_),A), A) :- !.
eq(or(and(_,A),A), A) :- !.
eq(or(A,B), C):-
	(A = or(_,_) ; B = or(_,_)),
	%%%%%%only_tree(A, or), only_tree(B, or), !,
	simplify_tree(or(A,B),or,C), \+ or(A,B)=C.
eq(or(I,J),I):- I =.. [OpI,X,Y], J =.. [OpJ,Z,T], Z == Y, T == X,
                 correspond(OpI,OpJ).
eq(and(I,J),I) :- I == J, !.
eq(and(I,J),I):- I =.. [OpI,X,Y], J =.. [OpJ,Z,T], Z == Y, T == X,
                 correspond(OpI,OpJ).
eq(and(_A, false), false).
eq(and(false, _A), false).
eq(and(A, true), A).
eq(and(true, A), A).
eq(and(A,or(A,_)), A) :- !.
eq(and(A,or(_,A)), A) :- !.
eq(and(or(A,_),A), A) :- !.
eq(and(or(_,A),A), A) :- !.
eq(or(and(A,B),and(A,C)), and(A,D)) :-
	eq(or(B,C),D), !.
eq(and(A,or(B,C)),or(and(A,B),and(A,C))).
eq(and(or(B,C),A),or(and(A,B),and(A,C))).
eq(and(A,B), C):-
	(A = and(_, _) ; B = and(_,_)),
	%%%%%only_tree(A, and), only_tree(B, and), !,
	simplify_tree(and(A,B),and,C), \+ and(A,B)=C.

% irrelevant
eq(and(A, irr),A) :- !.
eq(and(irr, A),A) :- !.
eq(or(A, irr),A) :- !.
eq(or(irr, A),A) :- !.

% comparisons

eq(X=Y, true) :- X==Y.
eq(X>=Y, true):- X==Y.
eq(X=<Y, true):- X==Y.
eq(X<Y, false):- X==Y, !.
eq(X>Y, false):- X==Y, !.

eq(X<Y, X=< Y1) :- number(Y), Y1 is Y-1.
eq(X<Y, X1=< Y) :- number(X), X1 is X+1.
eq(X>Y, X>= Y1) :- number(Y), Y1 is Y+1.
eq(X>Y, X1>= Y) :- number(X), X1 is X-1.

eq(not(X=Y), or(X<Y, X>Y)).
eq(not(X<Y), X>=Y).
eq(not(X=<Y), X>Y).
eq(not(X>Y), X=<Y).
eq(not(X>=Y), X<Y).

eq(or(X<Y, Z>=T), true) :- X==Z, Y==T.
eq(or(X=<Y, Z>T), true) :- X==Z, Y==T.
eq(or(X>Y, Z=<T), true) :- X==Z, Y==T.
eq(or(X>=Y, Z<T), true) :- X==Z, Y==T.
eq(or(X<Y, T=<Z), true) :- X==Z, Y==T.
eq(or(X=<Y, T<Z), true) :- X==Z, Y==T.
eq(or(X>Y, T>=Z), true) :- X==Z, Y==T.
eq(or(X>=Y, T>Z), true) :- X==Z, Y==T.

eq(or(X>=Y, Z>T), X>=Y) :- X==Z, Y==T.
eq(or(X>=Y, Z=T), X>=Y) :- X==Z, Y==T.
eq(or(X>=Y, T<Z), X>=Y) :- X==Z, Y==T.
eq(or(X>=Y, T=Z), X>=Y) :- X==Z, Y==T.
eq(or(Z>T, X>=Y), X>=Y) :- X==Z, Y==T.
eq(or(Z=T, X>=Y), X>=Y) :- X==Z, Y==T.
eq(or(T<Z, X>=Y), X>=Y) :- X==Z, Y==T.
eq(or(T=Z, X>=Y), X>=Y) :- X==Z, Y==T.
eq(or(X>Y, Z=T), X>=Y) :- X==Z, Y==T.
eq(or(X>Y, T=Z), X>=Y) :- X==Z, Y==T.
eq(or(X=Y, Z>T), X>=Y) :- X==Z, Y==T.
eq(or(X=Y, T<Z), X>=Y) :- X==Z, Y==T.
eq(or(X=<Y, Z<T), X=<Y) :- X==Z, Y==T.
eq(or(X=<Y, Z=T), X=<Y) :- X==Z, Y==T.
eq(or(X=<Y, T>Z), X=<Y) :- X==Z, Y==T.
eq(or(X=<Y, T=Z), X=<Y) :- X==Z, Y==T.
eq(or(Z<T, X=<Y), X=<Y) :- X==Z, Y==T.
eq(or(Z=T, X=<Y), X=<Y) :- X==Z, Y==T.
eq(or(T>Z, X=<Y), X=<Y) :- X==Z, Y==T.
eq(or(T=Z, X=<Y), X=<Y) :- X==Z, Y==T.
eq(or(X<Y, Z=T), X=<Y) :- X==Z, Y==T.
eq(or(X<Y, T=Z), X=<Y) :- X==Z, Y==T.
eq(or(Z=T, X<Y), X=<Y) :- X==Z, Y==T.
eq(or(T=Z, Y>X), X=<Y) :- X==Z, Y==T.

eq(and(X=Y,Z<T), false) :- X==Z, Y==T.
eq(and(X=Y,Z>T), false) :- X==Z, Y==T.
eq(and(X=Y,T<Z), false) :- X==Z, Y==T.
eq(and(X=Y,T>Z), false) :- X==Z, Y==T.
eq(and(X>Y,Z=T), false) :- X==Z, Y==T.
eq(and(X<Y,Z=T), false) :- X==Z, Y==T.
eq(and(X>Y,T=Z), false) :- X==Z, Y==T.
eq(and(X<Y,T=Z), false) :- X==Z, Y==T.

eq(and(X<Y,Z>=T), false) :- X==Z, Y==T.
eq(and(X>Y,Z=<T), false) :- X==Z, Y==T.
eq(and(X=<Y,Z>T), false) :- X==Z, Y==T.
eq(and(X>=Y,Z<T), false) :- X==Z, Y==T.
eq(and(X>Y,Z<T), false) :- X==Z, Y==T.
eq(and(X<Y,Z>T), false) :- X==Z, Y==T.
eq(and(X<Y,T=<Z), false) :- X==Z, Y==T.
eq(and(X>Y,T>=Z), false) :- X==Z, Y==T.
eq(and(X=<Y,T<Z), false) :- X==Z, Y==T.
eq(and(X>=Y,T>Z), false) :- X==Z, Y==T.
eq(and(X>Y,T>Z), false) :- X==Z, Y==T.
eq(and(X<Y,T<Z), false) :- X==Z, Y==T.

eq(and(X>=Y, Z>T), X>Y) :- X==Z, Y==T.
eq(and(X>=Y, T<Z), X>Y) :- X==Z, Y==T.
eq(and(X>=Y, Z=T), X=Y) :- X==Z, Y==T.
eq(and(X>=Y, T=Z), X=Y) :- X==Z, Y==T.
eq(and(X>Y, Z>=T), X>Y) :- X==Z, Y==T.
eq(and(X=Y, Z>=T), X=Y) :- X==Z, Y==T.
eq(and(X=Y, T>=Z), X=Y) :- X==Z, Y==T.
eq(and(X=<Y, Z<T), X<Y) :- X==Z, Y==T.
eq(and(X=<Y, T>Z), X<Y) :- X==Z, Y==T.
eq(and(X=<Y, Z=T), X=Y) :- X==Z, Y==T.
eq(and(X=<Y, T=Z), X=Y) :- X==Z, Y==T.
eq(and(X<Y, Z=<T), X<Y) :- X==Z, Y==T.
eq(and(X<Y, T>=Z), X<Y) :- X==Z, Y==T.
eq(and(X=Y, Z=<T), X=Y) :- X==Z, Y==T.
eq(and(X=Y, T=<Z), X=Y) :- X==Z, Y==T.

eq(and(X<Y,T>Z), X<Y) :- X==Z, Y==T.
eq(and(X=<Y,T>=Z), X=<Y) :- X==Z, Y==T.
eq(and(X>Y,T<Z), X>Y) :- X==Z, Y==T.
eq(and(X>=Y,T=<Z), X>=Y) :- X==Z, Y==T.

eq(and(X=<Y, Z>=T), X=Y) :- X==Z, Y==T.
eq(and(X>=Y, Z=<T), X=Y) :- X==Z, Y==T.
eq(and(X>=Y, Z>=T), X=Y) :- X==T, Y==Z.
eq(and(X=<Y, Z=<T), X=Y) :- X==T, Y==Z.

eq(and(X >= A, Y =< D),false):- X == Y, number(A), number(D), D < A, !.
eq(and(X =< B, Y >= C),false):- X == Y, number(B), number(C), B < C, !.

eq(and(X=<Y, Z=< T), X=< Y) :- X==Z, Y =< T.
eq(and(X=<Y, Z=< T), X=< T) :- X==Z, Y > T.

eq(and(X>=Y, Z>= T), X>= Y) :- X==Z, Y >= T.
eq(and(X>=Y, Z>= T), X>= T) :- X==Z, Y < T.

correspond('>', '<').
correspond('>=', '=<').
correspond('<', '>').
correspond('=<', '>=').
corresp_atom(I,J) :-
        I =.. [OpI,X,Y], correspond(OpI,OpJ), J =.. [OpJ,Y,X].

only_tree((_,_,_), _):- !.
only_tree(_ > _, _) :- !.
only_tree(_ >= _, _) :- !.
only_tree(_ < _, _) :- !.
only_tree(_ =< _, _) :- !.
only_tree(_ = _, _) :- !.
only_tree(Tree, Op):-
	Tree =.. [Op, A1, A2], !,
	only_tree(A1, Op),
	only_tree(A2, Op).

tree_to_list_(Tree, Op, SL):-
	tree_to_list(Tree, Op, L),
	flatten(L,FL),
	sort(FL, SL).

simplify_tree(Tree, Op, C):-
	tree_to_list(Tree, Op, L),
	flatten(L,FL),
	sort(FL, SL),
	simplify_list2(SL, Op, SSL),
	sort(SSL,SSL1),
	list_to_tree(SSL1, Op, C).

%% simplify_list(List, Op, NewList)
simplify_list([], _, []).
simplify_list([E], _, [E]).
simplify_list([E1, E2|Es], Op, [E|NewEs]):-
	Term =.. [Op, E1, E2],
	simplify(Term, T),
	(T = Term -> E = E1, 
	    simplify_list([E2|Es], Op, NewEs)
	;  E = T, simplify_list([E|Es], Op, NewEs)).
/*
simplify_list2(List, Op, NewList):-
	simplify_list1(List, List, Op, L),
	simplify_list(L, Op, NewList).
*/
simplify_list2(List, Op, NewList):-
        simplify_list1(List, List, Op, L),
        simplify_list(L, Op, NewList1),
%       trees_to_lists(NewList1,Op,NewList2),
        simplify_list3(NewList1,Op,NewList2),
%       NewList2 = NewList1,
        flatten(NewList2,NewList).

simplify_list0([], _L, _, []).
simplify_list0([L|_Ls],List,Op,[Answer]):-
	(eq(not(L),NL) ; simplify(not(L),NL)),
	id_member(NL,List),!,
	(Op = and -> Answer = false ; Answer = true).
simplify_list0([L|Ls],List,Op,NewLs):-
        corresp_atom(L,M),
        id_member(M,List),!,
        simplify_list0(Ls,List,Op,NewLs).
simplify_list0([L|Ls],List,Op,[L|NewLs]):-
	simplify_list0(Ls,List,Op,NewLs).

simplify_list1(List,List,Op,NewList):-
	simplify_list0(List, List, Op, L),
	((member(false,L), Op = and) -> NewList = [false] ;
	    ((member(true,L), Op = or) -> NewList = [true] ;
		NewList = L)).
	simplify_list3(L, or,L).

simplify_list3(L,and,M):-
        !, copy_term(L,L1), melt(L1,L2),
        (simplify_list3_(L2) ->
            M = L
        ;
            M = [false]).
simplify_list3(L,_,L).

simplify_list3_([]).
simplify_list3_([C|Cs]):- 
        check_clp_(C),
        simplify_list3_(Cs).
    
tree_to_list(Tree, Op, [C,D]):-
	Tree =..[Op,A,B], !,
	tree_to_list(A,Op,C),
	tree_to_list(B,Op,D).
tree_to_list(A,_,A).


list_to_tree([A,B],Op,C):-!, C=..[Op,A,B].
list_to_tree([A],and,C):-!,C=..[and,A,true].
list_to_tree([A],or,C):-!,C=..[or,A,false].
list_to_tree([],and,true):-!.
list_to_tree([],or,false):-!.
list_to_tree([A|B],Op,C):-
	list_to_tree(B,Op,D), C=..[Op,A,D].


simplify(X, X) :- var(X), !.
simplify(X, X) :- number(X), !.
simplify((X,Min,Max),I):- eq((X,Min,Max), I), !.
simplify((X,Min,Max),(X,Min,Max)):- !.
simplify(Exp,SExp):-
	eq(Exp,NExp),!,
	simplify(NExp,SExp).
simplify(and(X,Y),SExp):-
	simplify(X,SX),
	simplify(Y,SY),
	\+ (and(X,Y) = and(SX,SY)), !,
	simplify(and(SX,SY),SExp).
simplify(or(X,Y),SExp):-
	simplify(X,SX),
	simplify(Y,SY),
	\+ (or(X,Y) = or(SX,SY)),!,
	simplify(or(SX,SY),SExp).
simplify(Exp,Exp).

intervals_to_partition(Intervals, Partition) :-
	combine(Intervals, Intervals1),
	intervals_to_partition_(Intervals1,Partition).
intervals_to_partition_([],[]).
intervals_to_partition_([Head-Intervals|OtherIntervals],
			[Head-Partition|Partitions]) :-
	findall(Part, pick_up(Intervals, true, Part), Partition),
	intervals_to_partition_(OtherIntervals,Partitions).

pick_up([], Part, Part).
pick_up([I|Is], Exp, Part):-
	simplify(and(I,Exp),L),
	(L = false -> fail;
	    pick_up(Is, L, Part)).
pick_up([I|Is], Exp, Part):-
	simplify(and(not(I),Exp),L),
	(L = false -> fail;
	    pick_up(Is, L, Part)).

to_preint_([X,=,Y],(X,Y,Y)).
to_preint_([X,>=,Y],(X,Y,inf)).
to_preint_([X,>,Y],(X,Y1,inf)):-
	Y1 is Y+1.
to_preint_([X,=<,Y],(X,-inf,Y)).
to_preint_([X,<,Y],(X,-inf,Y1)):-
	Y1 is Y-1.

to_preint([>=,X,Y],[],true) :- X == Y, !.
to_preint([=<,X,Y],[],true) :- X == Y, !.
to_preint([=,X,Y],[],true) :- X == Y, !.
to_preint([>,X,Y],[],false) :- X == Y, !.
to_preint([<,X,Y],[],false) :- X == Y, !.
to_preint([N,X,Y],[X],I):-
	ground(X), varname(X), number(Y), !, to_preint_([X,N,Y],I).
to_preint([N,X,Y],[Y],I):-
	number(X), ground(Y), varname(Y), !, to_preint_([Y,N,X],I).
to_preint([N,X,Y],[X],I):-
	var(X), number(Y), !, to_preint_([X,N,Y],I).
to_preint([N,X,Y],[Y],I):-
	number(X), var(Y), !, to_preint_([Y,N,X],I).
to_preint([N,X,Y],[],I):- number(X), number(Y), !,
	S =.. [N,X,Y], (call(S) -> I = true; I = false).
to_preint([N,X,Y],L,S) :- vars(X,LX), vars(Y,LY),
	append(LX,LY,L0), sort(L0, L), S=.. [N,X,Y].

to_interval_(true, List,List).
to_interval_((!, Constraints), List, L):- !,
	to_interval_(Constraints, List, L).
to_interval_((integer(_), Constraints), List, L):- !,
	to_interval_(Constraints, List, L).
to_interval_((number(_), Constraints), List, L):- !,
	to_interval_(Constraints, List, L).
to_interval_((arg(X, _, _), Constraints), List, L):- !,
	C =.. [>,X,0],
	to_interval_((C, Constraints), List, L).
to_interval_((functor(_, _, X), Constraints), List, L):- !,
	C =.. [>=,X,0],
	to_interval_((C, Constraints), List, L).
to_interval_((Constr, Constraints), List, L):-
	Constr =.. [N,Arg1,Arg2],
	to_preint([N,Arg1,Arg2], Var, PreInt),
	\+ (PreInt = false),!,
	add_var_preint(List,Var,PreInt,List1),
	to_interval_(Constraints, List1, L).
to_interval_((Constr, Constraints), List, L):-
	built_in(Constr), \+ comparison(Constr),
	to_interval_(Constraints, List, L).

to_interval((Predicate,Constraints), (Predicate,Intervals)):-
	to_interval_(Constraints, [], List),
	simplify_all(List, Intervals).
to_intervals(true, []).
to_intervals((Constraints,SequenceOfConstraints),Intervals):-
	(to_interval(Constraints,(Head,Interval)) ->
	    to_intervals(SequenceOfConstraints, Intervals0),
	    interval_to_conjunct(Interval, Conjunct),
	    Intervals = [Head-[Conjunct]|Intervals0]
	; to_intervals(SequenceOfConstraints, Intervals)).

interval_to_conjunct([I1,I2], and(I1,I2)):-!.
interval_to_conjunct([I], I) :- !.
interval_to_conjunct([], true) :- !.
interval_to_conjunct([I1|I2], and(I1,I3)):-!,
	interval_to_conjunct(I2,I3).

sequence_to_conjunct((B1,(B2,true)), and(B1,B2)):-!.
sequence_to_conjunct((B1,B2), and(B1,B3)):-
	sequence_to_conjunct(B2,B3).

and_interval(and((V,A,B),(V,C,D)),(V,C,B)) :- A < C, C < B, B < D, !.
and_interval(X,X).
	     
add_var_preint(List,[],_,List):- !. % false was already removed, thus []=true
add_var_preint([],Var,PreInt,[Var-PreInt]):-!.
add_var_preint([Var-X|List],Var1,PreInt,[Var-AndInt|List]):-
	Var == Var1,
	and_interval(and(PreInt,X),AndInt).
add_var_preint([Var0-Exp0|List],Var,PreInt,[Var0-Exp0|NewList]) :-
	add_var_preint(List, Var, PreInt, NewList).

simplify_all([],[]).
simplify_all([[_]-Exp|List],[Exp1|NewList]):- !,
	simplify(Exp,Exp1),
	simplify_all(List, NewList).
simplify_all([[_,_|_]-Exp|List],[Exp|NewList]) :- !,
	simplify_all(List, NewList).
		   
partition(Clauses, SequenceOfConstraints, Partition):-
	to_intervals(SequenceOfConstraints, Intervals),
	propagate_intervals(Clauses, Intervals, Intervals1),
	append(Intervals, Intervals1, Intervals2),
	intervals_to_partition(Intervals2, Partition3),
	remove_ors(Partition3, Partition).

remove_ors(X, X).
/*
remove_ors([], []).
remove_ors([Head-Partition|Partitions], [Head-NewPartition|NewPartitions]):-
	remove_ors_(Partition, NewPartition),
	remove_ors(Partitions, NewPartitions).
remove_ors_([], []).
remove_ors_([or(C1,C2)|Cs], NewCs):- !,
	remove_ors__(C1, L1),
	remove_ors__(C2, L2),
	remove_ors_(Cs, Ls),
	append(L1, L2, L),
	append(L, Ls, NewCs).
remove_ors_([C|Cs], [C|NewCs]):-
	remove_ors_(Cs, NewCs).
remove_ors__(or(C1, C2), C):- !,
	remove_ors__(C1, L1),
	remove_ors__(C2, L2),
	append(L1, L2, C).
remove_ors__(C, [C]).
*/


%%%%%%% in general, we can propagate in this way
% information from the calling clause to 
propagate_intervals(Clauses, Intervals, Intervals1):-
	rec(Clauses, _, _, MR, _, _), \+ MR = [], !,
	copy_term(Intervals, Intervals_),
	propagate_intervals_(Clauses, MR, Intervals_, Intervals1).
propagate_intervals(_Clauses, _Intervals, []).

propagate_intervals_(Clauses, MR, Intervals, Intervals1) :-
	findall(Interval1,
		propagate_intervals1(Clauses, MR, Intervals, Interval1),
		Intervals1).

propagate_intervals1(Clauses, SCC,Intervals, Subgoal_-[Interval1]):-
	member(Preds,SCC),
	member(Pred,Preds),
	member(Pred-[Interval], Intervals),
	\+ Interval = true,
	member(clause(Pred,Body), Clauses),
	\+ Body = true, 
	find_rec_subgoal(Body, Preds, Preds, Subgoal),
	vars(Interval, VI), vars(Subgoal, VS),
	member(X,VI), member(X,VS),
	Subgoal =.. [_|Args],
	nth(ArgPos, Args, X),
	fresh_all(Subgoal,Subgoal_),
	user:iap(Subgoal_-IntArgPos),
	nth0(CorrVarNumber,IntArgPos,ArgPos),
	varname(VarName, CorrVarNumber),
	rename(X,VarName,Interval,Interval1).

find_rec_subgoal(true, _, _, _):- fail.
find_rec_subgoal((_B1,B2), [], Preds, B):-
	find_rec_subgoal(B2, Preds, Preds, B).
find_rec_subgoal((B1,_B2), [B|_Preds], _, B1):- fresh_all(B1,B).
find_rec_subgoal((B1,B2), [_|Preds], P, B):-
	find_rec_subgoal((B1,B2), Preds, P, B).

%%%%%%% 

extend(Prefix,and(Prefix, T)):-
	melt(Prefix, Prefix_),
	frz(Prefix_, Prefix__),
	findall(Estimate,
		(
		  non_linear(Prefix__, NL),
		  estimate_non_linear(Prefix__,NL,Estimate)
		), E),
	list_to_tree(E, and, Tree),
	melt(and(Prefix__, Tree), and(Prefix, T)).
% extend(Prefix,Prefix).

non_linear(X):- var(X), !, fail.
non_linear(X):- varname(X), !, fail.
non_linear(X):- number(X), !, fail.
non_linear(S):- S=..[Op,_X,_Y], \+ logic(Op), \+ linear_op(Op),!.
non_linear(S):- non_linear(S, _).

non_linear((_,_,_),_) :- !, fail.
non_linear(S,T):- S=..[Op,X,_Y], logic(Op), non_linear(X,T).
non_linear(S,T):- S=..[Op,_X,Y], logic(Op), non_linear(Y,T).
non_linear(S,S):- S=..[Op,X,_Y], linear_op(Op), non_linear(X).
non_linear(S,S):- S=..[Op,_X,Y], linear_op(Op), non_linear(Y).
non_linear(S,T):- S=..[Op,X], logic(Op), non_linear(X,T).
non_linear(S,S):- S=..[Op,X], linear_op(Op), non_linear(X).

logic(and).
logic(or).
logic(not).

linear_op(+).
linear_op(-).
linear_op(>=).
linear_op(=<).
linear_op(>).
linear_op(<).
linear_op(=).
linear_op(is).

% what happens if NL is not in the is-form?
estimate_non_linear(Prefix, Var is Expression, (Var,E1,E2)):-
	vars(Expression, Vars_),!,
	sort(Vars_, Vars),
	get_intervals(Vars,Prefix,Info),
	estimate(Expression, Info, (E1,E2)).
get_intervals([], _, []).
get_intervals([V|Vs], Prefix, [V-Info|Infos]):-
	get_intervals_(V,Prefix,Info_),
	simplify(Info_, Info),
	get_intervals(Vs,Prefix,Infos).
get_intervals_(Var, and(A1,A2), and(I1,I2)) :-
	!, get_intervals_(Var, A1, I1),
	get_intervals_(Var, A2, I2).
get_intervals_(Var, or(O1,O2), or(I1,I2)) :-
	!, get_intervals_(Var, O1, I1),
	get_intervals_(Var, O2, I2).
get_intervals_(Var, (Var, Min, Max), (Var, Min, Max)) :- !.
get_intervals_(Var, Var is Exp, Var is Exp) :- !.
get_intervals_(Var, S, S):-
	\+ S = is(_,_),
	vars(S, Vars), member(Var, Vars), !.
get_intervals_(_Var, _, irr).

% estimate_expression(Expression, Info, Estimate)
estimate(-X, Info, (Min,Max)):-
	estimate(X,Info, (Min1, Max1)),
	Min is -Max1, Max is -Min1.
estimate(X+Y, Info, (Min,Max)):-
	estimate(X,Info, (Min1, Max1)),
	estimate(Y,Info, (Min2, Max2)),
	add(Min1,Min2,Min), add(Max1,Max2,Max).
estimate(X-Y, Info, (Min,Max)):-
	estimate(X,Info, (Min1, Max1)),
	estimate(Y,Info, (Min2, Max2)),
	substract(Min1,Max2,Min), substract(Max1, Min2, Max).
estimate(X*X, Info, (Min,Max)):- !,
	estimate(X,Info, (Min1, Max1)),
	mult(Min1,Min1,M1), mult(Max1,Max1,M2),
	max(M1,M2,Max),
	((Min1 < 0, Max > 0) -> Min = 0;
	    min(M1,M2,Min)), !.
estimate(X*Y, Info, (Min,Max)):-
	estimate(X,Info, (Min1, Max1)),
	estimate(Y,Info, (Min2, Max2)),
	mult(Min1,Min2,M1), mult(Min1,Max2,M2),
	mult(Max1,Min2,M3), mult(Max1,Max2,M4),
	sort([M1,M2,M3,M4],[Min,_,_,Max]).
estimate(X, Info, (Min,Max)):-
	member(X-Tree, Info),
	in_tree(Tree, (X,Min,Max)).

in_tree((X,Min,Max), (X, Min, Max)).
in_tree(and(X =< Y, X >= Z), (X,Z,Y)).
in_tree(and(X >= Y, X =< Z), (X,Y,Z)).
in_tree(and(I1,_I2), (X, Min, Max)) :-
	I1 = (_,_,_),
	in_tree(I1, (X,Min,Max)), !.
in_tree(and(_I1,I2), (X, Min, Max)) :-
	I2 = (_,_,_),
	in_tree(I2, (X,Min,Max)), !.
in_tree(or(I1,_I2), (X, Min, Max)) :-
	in_tree(I1, (X,Min,Max)).
in_tree(or(_I1,I2), (X, Min, Max)) :-
	in_tree(I2, (X,Min,Max)).

max(_, inf, inf):-!.
max(inf, _, inf):-!.
max(-inf,X,X):-!.
max(X,-inf,X):-!.
max(M1,M2,M1):- M1 >= M2, !.
max(_M1,M2,M2).

min(X, inf, X):-!.
min(inf, X, X):-!.
min(-inf,_,-inf):-!.
min(_,-inf,-inf):-!.
min(M1,M2,M1):- M1 =< M2, !.
min(_M1,M2,M2).

add(_,inf,inf) :-!.
add(inf,_, inf):-!.
add(-inf,_, -inf):-!.
add(_,-inf,-inf):-!.
add(X,Y,Z):- Z is X+Y.

substract(-inf, _, -inf):-!.
substract(_, -inf, inf):-!.
substract(inf, _, inf):-!.
substract(_, inf, -inf):-!.
substract(X,Y,Z):- Z is X-Y.

mult(inf, _, inf):-!.
mult(_, inf, inf):-!.
mult(-inf, _, -inf):-!.
mult(_, -inf, -inf):-!.
mult(X,Y,Z):- Z is X*Y.


%%%%%%% debugging
gen_test(N, Partition):-
	gen_test(1,N, Intervals),!,
	time(_),
	partition(Intervals, Partition),
	timer('Partitioning with findall ').
/*
gen_test(I,N,true) :- I >= N-I+1.
gen_test(I,N,(('#VAR'(J)>=I,'#VAR'(J)=<NI,true),Constraints)):-
	NI is N-I+1,I1 is I+1,
	random(0,I,J), 
	gen_test(I1, N, Constraints).
*/
gen_test(I,N,true) :- I >= N-I+1.
gen_test(I,N,(('#VAR'(J)>=I,'#VAR'(J)=<NI, J < N2, '#VAR'(J)>='#VAR'(0),'#VAR'(J)=<'#VAR'(I),true),Constraints)):-
	NI is N-I+1,I1 is I+1,
	N2 is NI - I,
	random(0,I,J), 
	gen_test(I1, N, Constraints).
%%%%%%%%%
