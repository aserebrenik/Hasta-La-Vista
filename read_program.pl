:- module(read_program, [read_program/2]).
:- use_module(comma,[add_true/2, has_true/1]).
:- use_module(atom, [built_in/1, comparison/1, fresh_all/2]).
:- use_module(aux, [variant_delete_all/3, flatten/2, id_member/2]).
:- use_module(numvars, [frz/2, meltl/2]).
:- use_module(library(lists), [append/3, length/2, member/2]).
:- use_module(library(terms), [variant/2]).
:- use_module(library(ordsets), [ord_union/3]).
:- use_module(rec, [rec/6]).

read_program(File, Clauses):-
	init,
        see(File),
        read_loop(L), seen,
	flatten(L, Clauses_),
	safe_cut_replace(Clauses_, ClausesC),
	rec(ClausesC, Rec, _DirRec, _MutRec, NonRec, _Unfoldable),
	ord_union(Rec,NonRec,Preds),
	add_lib_preds(Preds,ClausesC,Clauses).

add_lib_preds([], C, C).
add_lib_preds([Head|Preds],ClausesC,Clauses):-
	member(clause(Head,_), ClausesC), !,
	add_lib_preds(Preds,ClausesC,Clauses).
add_lib_preds([length(_,_)|Preds],ClausesC,Clauses):- !,
	add_lib_preds(Preds,
		      [clause(length([],0),true),
		      clause(length([_|T],N1), (N1 > 0, N is N1 - 1,
						   length(T,N), true))|
			    ClausesC],Clauses).
add_lib_preds([numbervars(_,_,_)|Preds],ClausesC,Clauses):- !,
	add_lib_preds(Preds,[clause(numbervars(_,_,_),true)|ClausesC],Clauses).
/*
add_lib_preds([H|Preds],ClausesC,Clauses):- 
	built_in(H), !, 
	add_lib_preds(Preds,[clause(H,true)|ClausesC],Clauses).
*/

add_lib_preds([Head|Preds],ClausesC,Clauses):-
	write('*** No definition for '),
	write(Head), write(' *** '), nl,
	add_lib_preds(Preds,ClausesC,Clauses).

init:- assert(user:bad_clause(clause(nohead, nobody))).

read_loop([Y|L]) :-
        read(X),
	(X = end_of_file ->
	    Y = [], % will be removed by flattening
	    L = []
	;
	    convert(X,Y),
	    read_loop(L)).

convert(end_of_file,end_of_file):-!.
convert((H:-B),ML):-
	!, add_true(B,B1),
	frz(clause(H,B1),clause(FH,FB1)),
	findall(clause(FH,FB),
		transform0(FB1,FB),
		Clauses_),
	remove_variants(Clauses_, Clauses),
	meltl(Clauses,ML),
	update_bad_bodies(Clauses,ML).
convert(H, [clause(H,true)]):- !.

update_bad_bodies([], []).
update_bad_bodies([clause(_FH,FB)|Clauses], [clause(H,B)|MeltedClauses]):-
	retract(user:bad_body(FB)),!,
	assert(user:bad_clause(clause(H,B))),
	update_bad_bodies(Clauses, MeltedClauses).
update_bad_bodies([_|Clauses], [_|MeltedClauses]):-
	update_bad_bodies(Clauses, MeltedClauses).

%%% ;
rewrite_or((X1,X2),(Y1,Y2)) :- !, rewrite_or(X1,Y1),rewrite_or(X2,Y2).
rewrite_or((X1;_),Y) :- rewrite_or(X1,Y).
rewrite_or((_;X2),Y) :- rewrite_or(X2,Y).
rewrite_or(X,X) :- \+ functor(X,';',2).

%%% =\= , \== and =:=
%%% in general \== is equivalent to \+ ==, but we do not make
%%% distinction between == and = should it be done?
%%% in general, =:= (numerically equal) differs from is
%%% as a first attempt, however, we replace =:= with is
rewrite_ineq((X1,X2),(Y1,Y2)) :- !, rewrite_ineq(X1,Y1),rewrite_ineq(X2,Y2).
rewrite_ineq(X =\= Y, X > Y).
rewrite_ineq(X =\= Y, X < Y).
rewrite_ineq(X \== Y, \+ X == Y) :- !.
%%% ????
rewrite_ineq(X =:= Y, X is Y) :- !.
rewrite_ineq(X,X):- \+ functor(X,'=\\=',2).

%%% ->
rewrite_imply((X1,X2),(Y,Z)) :- !, rewrite_imply(X1,Y),rewrite_imply(X2,Z).
rewrite_imply((X1->X2),(Y1,Y2)) :- !,
	rewrite_imply(X1,Y1), rewrite_imply(X2,Y2).
rewrite_imply(X,X).

%%% associativity correction
rewrite_assoc(','(','(A,B),C),','(A,','(B,C))) :- !.
rewrite_assoc(','(A,','(B,C)),','(A,L)) :- rewrite_assoc(','(B,C),L).
normal_form(F,N) :- rewrite_assoc(F,F1),!, normal_form(F1,N).
normal_form(F,F).

%%% \+ this transformation may improve termination
rewrite_not_to_tree(true, true) :- !.
rewrite_not_to_tree((\+ X1,X2), choice(Y1, Y2)):-
	!, rewrite_not_to_tree(X1, Y1), rewrite_not_to_tree(X2, Y2).
rewrite_not_to_tree((X1,X2), (Y1, Y2)):-
	!, rewrite_not_to_tree(X1, Y1), rewrite_not_to_tree(X2, Y2).
rewrite_not_to_tree(X,X).

rewrite_tree_to_clauses((B1, B2), (B11, B12)):-
	!, rewrite_tree_to_clauses(B1, B11),
	rewrite_tree_to_clauses(B2, B12).
rewrite_tree_to_clauses(choice(B1, _B2), B11) :-
	rewrite_tree_to_clauses(B1, B11).
rewrite_tree_to_clauses(choice(_B1, B2), B12) :-
	rewrite_tree_to_clauses(B2, B12).
rewrite_tree_to_clauses(B, B):- \+ functor(B, choice, 2).

rewrite_not(Body1, Body2):-
	rewrite_not_to_tree(Body1, Tree),
	rewrite_tree_to_clauses(Tree, Body),
	(has_true(Body) ->
	    Body2 = Body
	;
	    add_true(Body, Body2),
	    assert(user:bad_body(Body2))).

rewrite_findall((B1, B2), (B11, B12)):-
	!, rewrite_findall(B1, B11),
	rewrite_findall(B2, B12).
rewrite_findall(findall(_,B,_), B) :- !.
rewrite_findall(B, B).

transform0(Body,Body5):-
	rewrite_or(Body, Body0),
	rewrite_findall(Body0,Body00),
	rewrite_imply(Body00, Body1),
	rewrite_ineq(Body1, Body2),
	rewrite_not(Body2, Body3),
	normal_form(Body3, Body4),
	(Body4 == Body0 ->
	    Body5 = Body4
	; transform0(Body4, Body5)).

remove_variants([],[]).
remove_variants([X|L1], L2) :-
	id_member(X,L1),\+ user:bad_clause(X),
	!, remove_variants(L1,L2).
remove_variants([X|L1], L2) :-
	id_member(X,L1), user:bad_clause(X),
	!, findall(_, user:bad_clause(X), VarList),
	length(VarList,M1), M is M1-1,
	appears(X,L1,N),
	(N < M -> write('*** Internal Error ***'), nl
	;
	    (N > M -> %%% some variants of this clause originate
		      %%% from sources different than clauses with \+
		retractall(user:bad_clause(X))
	    ;
		%%% N = M - we will remain with one asserted fact per clause
		retract(user:bad_clause(X)) )),
	!,remove_variants(L1,L2).
remove_variants([X|L1],[X|L2]) :-
	remove_variants(L1,L2).


%****************************************************************

safe_cut_replace(C,C).

/*
safe_cut_replace([], []).
safe_cut_replace([clause(H,B)|Clauses], [clause(H,B)|Clauses1]):-
	copy_term(clause(H,B), clause(H1,B1)),
	cond_cut(B1,C,_R), !,
	copy_term(Clauses, Cs),
	fresh_all(H1, H2),

	findall((clause(H2,B2), NCs),
		(
		  member(clause(H2,B2), Cs),
		  match_heads_(H1, H2),
		  
		  invert_body_conds(C, IC),
		  append(IC, Ineqs, IIC),
		  construct_clauses(H2,B2,IIC,NCs)
		),
		RemoveAdds),
	split_remove_add(RemoveAdds, Removes, Adds),
	variant_delete_all(Removes, Cs, Cs0),
	append(Adds, Cs0, Cs1),
	safe_cut_replace(Cs1, Clauses1).
safe_cut_replace([Clause|Clauses], [Clause|Clauses1]):-
	safe_cut_replace(Clauses, Clauses1).

cond_cut((!, B2), true, B2) :- !.
cond_cut((B1,B2), (B1,C), R) :-
	comparison(B1),
	cond_cut(B2, C, R).

match_heads_(H1, H2):-
	H1 =.. [_|Args1], H2 =.. [_|Args2],
	sort(Args1, A), length(Args1,L), length(A,L),
	match_heads(Args1, Args2, Ineqs).

match_heads([], [], []).
match_heads([X|Xs], [Y|Ys], Ineqs):-
	variant(X,Y), match_heads(Xs, Ys, Ineqs).
match_heads([X|Xs], [Y|Ys], [Y > X, Y < X|Ineqs]):-
	integer(X), var(Y), match_heads(Xs, Ys, Ineqs).

invert_body_conds(true, []).
invert_body_conds(X > Y,  [Y > X]) :- !.
invert_body_conds(X >= Y, [Y >= X]) :- !.
invert_body_conds(X < Y,  [Y < X]) :- !.
invert_body_conds(X =< Y, [Y =< X]) :- !.
invert_body_conds(X = Y, [Y < X, Y > X]) :- !.
invert_body_conds((B1, B2), C):-
	invert_body_conds(B1, C1),
	invert_body_conds(B2, C2),
	append(C1, C2, C).
		  
construct_clauses(_, _, [], []).
construct_clauses(Head, Body, [Ineq|Ineqs],
		  [clause(Head, (Ineq, Body))|Clauses]):-
	construct_clauses(Head, Body, Ineqs, Clauses).

split_remove_add_([], [], []).
split_remove_add_([(R,A)|RAs], [R|Rs], [A|As]):-
	split_remove_add_(RAs, Rs, As).

split_remove_add(RAs, Rs, As):-
	split_remove_add_(RAs, R0s, A0s),
	flatten(R0s, Rs), flatten(A0s, As).

*/