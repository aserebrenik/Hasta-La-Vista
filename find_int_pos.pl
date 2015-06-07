:- module(find_int_pos, [find_int_pos/2]).
:- use_module(atom, [comparison/1, fresh_all/2, is_atom/1]).
:- use_module(aux, [id_member/2]).
:- use_module(simplify_symb, [combine/2]).
:- use_module(library(lists), [append/3, member/2]).
:- use_module(library(ordsets), [list_to_ord_set/2, ord_union/3]).
:- use_module(numvars, [diff_vars/2, frz/2, frzl/2, varname/1]).

%%% in fact we are interested in finding those arg positions that
%%% participate in some integer computation...
%%% thats why we ignore comparisons, simple integer values etc.

find_int_pos(Clauses,Positions):-
	%%%%%%%frzl(Clauses, FClauses),
	find_int_pos_(Clauses,Pos),
	combine(Pos, Positions).
find_int_pos_([],[]).
find_int_pos_([clause(Head,Body)|Clauses],
	      [(HeadF-Positions1)|Positions2]) :-
	fresh_all(Head, HeadF),
	copy_term((Head,Body), (Head1,Body1)),
	find_int_body(Head1, Body1, Positions),
	list_to_ord_set(Positions,Positions1),
	find_int_pos_(Clauses, Positions2).


find_int_args(_, [], []).
find_int_args(I, [Arg|Args], [I|Positions]):-
	integer(Arg),!, I1 is I+1,
	find_int_args(I1, Args, Positions).
find_int_args(I, [_Arg|Args], Positions):-
	I1 is I+1,
	find_int_args(I1, Args, Positions).

find_int_body(Head1, Body1, Positions) :-
	find_int_body(Head1, Body1, [], _Vars, [], Positions).
find_int_body(Head1, Body1, V1, V2, P1, P2):-
	find_int_body_(Head1, Body1, V1, V3, P1, P3),
	sort(P3, P4), sort(V3,V4),
	(P4 = P1 -> P2 = P1, V2 = V1 ; find_int_body(Head1,Body1,V4,V2,P4,P2)).

find_int_body_(_, true, V, V, P, P).
find_int_body_(Head, (B1,B2), IntVars, NewIntVars, Positions, NewPositions):-
	(is_atom(B1), diff_vars(B1, Vars) ; comparison(B1), \+ B1 = (_ = _),
	    diff_vars(B1, Vars), member(V, Vars), id_member(V, IntVars)),
	!, frz(B1, FB1),
	B1 = FB1,
	Head =.. [_|Args],

	find_var_args(Args,1,VarArgs),
	append(Vars, IntVars, IntVars0),

	append(VarArgs,Positions,Positions0),
	find_int_body_(Head, B2, IntVars0, NewIntVars,
		       Positions0, NewPositions).
find_int_body_(Head,(_B1,B2), IntVars, NewIntVars, Positions, NewPositions):-
	find_int_body_(Head,B2, IntVars, NewIntVars, Positions, NewPositions).

find_var_args([], _, []).
find_var_args([A|Args],I,Positions):-
	var(A), !, I1 is I+1,
	find_var_args(Args, I1, Positions).
find_var_args([A|Args],I,[I|Positions]):-
	varname(A), !, I1 is I+1,
	find_var_args(Args, I1, Positions).
find_var_args([_A|Args],I,Positions):-
	I1 is I+1, find_var_args(Args, I1, Positions).
	