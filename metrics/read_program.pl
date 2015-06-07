:- module(read_program, [read_program/2]).
%:- use_module(comma,[add_true/2, has_true/1]).
%:- use_module(atom, [built_in/1, comparison/1, fresh_all/2]).
%:- use_module(aux, [variant_delete_all/3, flatten/2, id_member/2]).
%:- use_module(numvars, [frz/2, meltl/2]).
:- use_module(library(lists), [append/3, member/2]).
:- use_module(library(terms), [variant/2]).
:- use_module(library(ordsets), [ord_union/3]).
:- use_module(library(system)).
%:- use_module(rec, [rec/6]).


main(Dir,NumberOfFiles) :-
	read_code(Dir,0,NumberOfFiles).

read_code(Dir,InNOF,OutNOF) :-
	working_directory(OldDir,Dir),
	directory_files(Dir,ListOfFiles),
	read_code_loop(ListOfFiles,InNOF,OutNOF),!,
	working_directory(_Dir,OldDir).

read_code_loop([],I,I).
read_code_loop(['.'|Files],InNOF,OutNOF):-
	read_code_loop(Files,InNOF,OutNOF).
read_code_loop(['..'|Files],InNOF,OutNOF):-
	read_code_loop(Files,InNOF,OutNOF).
read_code_loop([File|Files],InNOF,OutNOF):-
	file_property(File,type(T)),
	(T == regular ->
	    IntermNOF is InNOF + 1,
	    read_program(File, Clauses) ;
	 T == directory ->
	    read_code(File,InNOF,IntermNOF) ;
	 true),
	read_code_loop(Files,IntermNOF,OutNOF).

read_program(_,_).

/*
read_program(File, Clauses):-
	init,
        see(File),
        read_loop(L), seen,
	flatten(L, Clauses_),
	rec(Clauses_, Rec, _DirRec, _MutRec, NonRec, _Unfoldable),
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

*/
%****************************************************************


