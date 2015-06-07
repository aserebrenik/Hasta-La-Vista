:- module(adorn, [code/3, decode/3, code_all/3, decode_all/2,
		  original_free_atom/3]).
:- use_module(library(lists), [append/3]).
:- use_module(atom, [atom_list_concat/2, comparison/1, fresh_all/2]).
:- use_module(aux,[flatten/2, without_last/2]).
:- use_module(numvars, [varname/2]).
%%% code(PredicateName, Adornment, NewPredicateName)
code_all(_, [], []).
code_all(P,[A|As],[NewP|NewPs]):-
	code(P,A,NewP),
	code_all(P,As,NewPs).

code(P, true, P) :- !.
code(P,A,NewP):-
	atom_concat(P,'_',PU),
	code_(A,CA), 
	atom_concat(PU,CA,NewP).

code_(Exp,Code):-
	code(Exp,List),
	flatten(List,FList),
	atom_list_concat(FList,Code).

code((Var,Min,Max),['in(',CV,',',Min,',',Max,')']):-!, code(Var,CV).
code(X>Y,[CX,'_>_',CY]):- !, code(X,CX), code(Y,CY).
code(X>=Y,[CX,'_>=_',CY]):- !, code(X,CX), code(Y,CY).
code(X=<Y,[CX,'_=<_',CY]):- !, code(X,CX), code(Y,CY).
code(X<Y,[CX,'_<_',CY]):- !, code(X,CX), code(Y,CY).
code(X=Y,[CX,'_=_',CY]):- !, code(X,CX), code(Y,CY).
code(X+Y,['(',CX,'+',CY,')']):- !, code(X,CX), code(Y,CY).
code(X-Y,['(',CX,'-',CY,')']):- !, code(X,CX), code(Y,CY).
code(X*Y,['(',CX,'*',CY,')']):- !, code(X,CX), code(Y,CY).
code(X/Y,['(',CX,'/',CY,')']):- !, code(X,CX), code(Y,CY).
code(-X,['-',CX]):- !, code(X,CX).
code(or(X,Y),['or(',CX,'_,_',CY,')']):- !, code(X,CX), code(Y,CY).
code(and(X,Y),['and(',CX,'_,_',CY,')']):- !, code(X,CX), code(Y,CY).
code(not(X),['not(',CX,')']):- !, code(X,CX).
code(X,['#VAR(',Y,')']):- varname(X,Y),!.
code(X, [X]):- atomic(X), !.


%%%%%%%%%%%
decode_all([],[]).
decode_all([NewName|NewNames], [(Predicate, Adornment)| Names]):-
	decode(NewName,Predicate,Adornment),
	decode_all(NewNames, Names).

decode(NewName,Predicate,Adornment):-
	atom_chars(NewName,NNChars),
	append(PotentialPredicate, [95|PotentialAdornment], NNChars),
	convert_potential_adornment(PotentialAdornment,Adornment),!,
	atom_chars(Predicate,PotentialPredicate).

%%% or( _,_ )
convert_potential_adornment([111,114,40|L], or(A1,A2)):- !,
	append(LA1,[95,44,95|LA2],L),
	convert_potential_adornment(LA1,A1),
	without_last(LA2,LA),
	convert_potential_adornment(LA,A2).
%%% and( _,_ )
convert_potential_adornment([97,110,100,40|L], and(A1,A2)):-!,
	append(LA1,[95,44,95|LA2],L),
	convert_potential_adornment(LA1,A1),
	without_last(LA2,LA),
	convert_potential_adornment(LA,A2).
%%% not(
convert_potential_adornment([110,111,116,40|L], not(A)):-!,
	without_last(L,L1),
	convert_potential_adornment(L1,A).
%%% -inf
convert_potential_adornment([45,105,110,102], -inf):-!.
%%% inf
convert_potential_adornment([105,110,102], inf):-!.
%%% true
convert_potential_adornment([116,114,117,101], true) :- !.
%%% -
convert_potential_adornment([45|L], A1):-!,
	convert_potential_adornment(L,A),
	(number(A) -> A1 is -A; A1 = -A).
%%% in(
convert_potential_adornment([105,110,40|L], (Var,Min,Max)):-!,
	append(LA1,[44|LA],L),
	append(LA2,[44|LA3],LA),
	without_last(LA3,LA31),
	convert_potential_adornment(LA1,Var),
	convert_potential_adornment(LA2,Min),
	convert_potential_adornment(LA31,Max).
%%% #VAR
convert_potential_adornment([35,86,65,82,40|L], '#VAR'(K)):-
	append(LK,[41],L), number_chars(K,LK).
convert_potential_adornment(L,S):-
	append(LA1,[95,OpCode,95|LA2],L), !,
	convert_potential_adornment(LA1,A1),
	convert_potential_adornment(LA2,A2),
	atom_chars(Op,[OpCode]),
	S =.. [Op,A1,A2].
convert_potential_adornment(L,S):-
	append(LA1,[95,Op1,Op2,95|LA2],L), !,
	convert_potential_adornment(LA1,A1),
	convert_potential_adornment(LA2,A2),
	atom_chars(Op,[Op1,Op2]),
	S =.. [Op,A1,A2].
convert_potential_adornment(L,A1*A2):-
	append([40|LA1],[42|LA2_],L), 
	convert_potential_adornment(LA1,A1),
	without_last(LA2_, LA2),
	convert_potential_adornment(LA2,A2), !.
convert_potential_adornment(L,A1+A2):-
	append([40|LA1],[43|LA2_],L), 
	convert_potential_adornment(LA1,A1),
	without_last(LA2_, LA2),
	convert_potential_adornment(LA2,A2), !.
convert_potential_adornment(L,A1-A2):-
	append([40|LA1],[45|LA2_],L), 
	convert_potential_adornment(LA1,A1),
	without_last(LA2_, LA2),
	convert_potential_adornment(LA2,A2), !.
convert_potential_adornment(L,A1/A2):-
	append([40|LA1],[46|LA2_],L), 
	convert_potential_adornment(LA1,A1),
	without_last(LA2_, LA2),
	convert_potential_adornment(LA2,A2), !.
convert_potential_adornment(L,S):-
	number_chars(S,L).
/*
convert_potential_adornment(L,S):-
	atom_chars(S,L).
*/
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% returns for an adorned atom an atom of the corresponding nonadorned
% predicate with linear vector of arguments; for nonadorned atom returns
% an atom of the same predicate, but also with linear vector of arguments
% the third argument is an adronment in the first case and undefined
% otherwise

original_free_atom(Atom1, Atom2, Ad):-
	Atom1 =.. [Name|Args],
        (decode(Name, Pred1, Ad1) ->
	    Pred = Pred1, Ad = Ad1
	;
	    Pred=Name, Ad=undefined),
	Atom =.. [Pred|Args],
	fresh_all(Atom, Atom2).