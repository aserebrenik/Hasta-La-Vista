%%%%% last changed 17 may 1997
%
%                     the file numvars.pl
%           A MODULE FOR FREEZING AND MELTING TERMS

% taken from Sterling-Shapiro

:- module(numvars,[diff_vars/2, frz/2,frzl/2,frzl/3,melt/2,meltl/2,
		   sym_melt/3,varlist/2,varname/1,varname/2,vars/2]).
:- use_module(library(lists), [append/3]).

varlist(N,L):- varlist(0,N,L).
varlist(I,N,['#VAR'(I)|L]):-
	I < N, !, I1 is I+1, varlist(I1,N,L).
varlist(_,_,[]).

varname('#VAR'(_)).
varname('#VAR'(X), X).

diff_vars(X,V):-
	vars(X,V_), sort(V_, V).
vars(X, [X]) :- var(X), !.
vars([],[]):-!.
vars('#VAR'(X),['#VAR'(X)]) :-!.
vars([Arg|Args], Vars):- !,
	vars(Arg, Vars0),
	vars(Args, Vars1),
	append(Vars0, Vars1, Vars).
vars(F, Vars) :-
	F =.. [_|Args],
	vars(Args,Vars).

frzl(Xs,Fs) :- frzl(Xs, 0, Fs).
frzl([],_,[]).
frzl([X|Xs],Min,[F|Fs]) :-
	frz(X,F,Min),
	frzl(Xs,Min,Fs).
meltl([],[]).
meltl([F|Fs],[X|Xs]) :-
	melt(F,X),
	meltl(Fs,Xs).

numvars('#VAR'(N),N,N1) :- N1 is N+1.
numvars(Term,N1,N2) :- nonvar(Term), functor(Term,_,N),
                          numvars(0,N,Term,N1,N2).
numvars(N,N,_,N1,N1).
numvars(I,N,Term,N1,N3) :- I<N, I1 is I+1,
          arg(I1,Term,Arg), numvars(Arg,N1,N2),
          numvars(I1,N,Term,N2,N3).

frz(A,B) :- frz(A,B,0).
frz(A,B,Min) :- copy_term(A,B), numvars(B,Min,_),!.

melt(A,B) :- melt(A,B,var,_),!.
sym_melt(A,B,D) :- melt(A,B,symbolic,D),!.

melt(X,X,_,_) :- var(X), !.%%%% Added by Alexander Serebrenik, 16 jul 2001
melt('#VAR'(N),X,var,Dictionary) :- lookup(N,Dictionary,X).
melt(X,X,var,_) :- atomic(X).
melt(X,X,symbolic,_) :- number(X), !.
melt([],[],symbolic,_) :- !.
melt(true,true,symbolic,_) :- !.
melt(#>, #>, symbolic, _) :-!.
melt(#>=, #>=, symbolic, _) :-!.
melt(X,Y,symbolic,Dictionary) :-
	atom(X), lookup(X,Dictionary,Y).
melt(X,Y,V,Dictionary) :- compound(X), functor(X,F,N),
                functor(Y,F,N),
                melt(N,X,Y,V,Dictionary).
melt(N,X,Y,V,Dictionary) :- N>0, arg(N,X,ArgX),
                melt(ArgX,ArgY,V,Dictionary),
                arg(N,Y,ArgY),
                N1 is N-1,
                melt(N1,X,Y,V,Dictionary).
melt(0,_,_,_,_).

lookup(Key,dict(Key,X,_,_),Value) :- !, X=Value.
lookup(Key,dict(Key1,_,Left,_),Value) :- Key@<Key1,
                lookup(Key,Left,Value).
lookup(Key,dict(Key1,_,_,Right),Value) :- Key@>Key1,
                lookup(Key,Right,Value).























