%%%%% last changed 17 may 1997
%
%                     the file numvars.pl
%           A MODULE FOR FREEZING AND MELTING TERMS

% taken from Sterling-Shapiro

:- module(numvars,[numvars/3,frz/2,melt_new/2,frzl/2,melt_newl/2]).

frzl([],[]).
frzl([X|Xs],[F|Fs]) :-
	frz(X,F),
	frzl(Xs,Fs).
melt_newl([],[]).
melt_newl([F|Fs],[X|Xs]) :-
	melt_new(F,X),
	melt_newl(Fs,Xs).

numvars('#VAR'(N),N,N1) :- N1 is N+1.
numvars(Term,N1,N2) :- nonvar(Term), functor(Term,_,N),
                          numvars(0,N,Term,N1,N2).
numvars(N,N,_,N1,N1).
numvars(I,N,Term,N1,N3) :- I<N, I1 is I+1,
          arg(I1,Term,Arg), numvars(Arg,N1,N2),
          numvars(I1,N,Term,N2,N3).

frz(A,B) :- copy_term(A,B), numvars(B,0,_).

melt_new(A,B) :- melt(A,B,_),!.
melt('#VAR'(N),X,Dictionary) :- lookup(N,Dictionary,X).
melt(X,X,_) :- atomic(X).
melt(X,Y,Dictionary) :- compound(X), functor(X,F,N),
                functor(Y,F,N),
                melt(N,X,Y,Dictionary).
melt(N,X,Y,Dictionary) :- N>0, arg(N,X,ArgX),
                melt(ArgX,ArgY,Dictionary),
                arg(N,Y,ArgY),
                N1 is N-1,
                melt(N1,X,Y,Dictionary).
melt(0,_,_,_).

lookup(Key,dict(Key,X,_,_),Value) :- !, X=Value.
lookup(Key,dict(Key1,_,Left,_),Value) :- Key<Key1,
                lookup(Key,Left,Value).
lookup(Key,dict(Key1,_,_,Right),Value) :- Key>Key1,
                lookup(Key,Right,Value).























