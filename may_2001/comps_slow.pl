%% find_comps(Clauses,Comps)
find_comps(Clauses,Comps):-
	find_comps(Clauses,[],PV),
	timer('Find comps/3 '),
	length_(PV,N),
	N1 is N - 1,
	def_vars_(PV,N1,Vars),
	timer('Def vars '),
	diffs(Vars,S),
	timer('Diffs '),
	labeling([minimize(S)],Vars),
	timer('Labeling '),
	def_comps(PV,Comps),
	timer('Def comps ').

find_comps([],PV,PV).
find_comps([(Head:-Body)|Clauses], PV1,PV2):-!,
	functor(Head,N,A),
	(member((V - N/A), PV1) ->
	    PV = PV1; PV = [(V - N/A) | PV1]),
	functors(Body,L0),
	sort(L0,L),
	add_for_each_(N/A,V,L,PV,PV0),
	find_comps(Clauses, PV0, PV2).
find_comps([_|Clauses], PV1,PV2):-
        find_comps(Clauses, PV1,PV2).

add_for_each_(_,_,[],PV,PV).
add_for_each_(N/A,V,[F|L],PV1,PV2):-
	(member(VF-F,PV1) ->
	    PV0 = PV1; PV0 = [VF-F|PV1]),
	(F = N/A ->
	    (PV = [VF-fic|PV0], VF #= V)
	; (PV=PV0, V #>= VF)),
	add_for_each_(N/A,V,L,PV,PV2).

def_vars_([],_,[]).
/*
def_vars_([V-fic|Preds],N,Vs):-
	!, V in 0..N,
	def_vars_(Preds,N,Vs).
*/
def_vars_([V-_|Preds],N,[V|Vs]):-
	V in 0..N,
	def_vars_(Preds,N,Vs).

diffs([],0).
diffs([V|Vars],S):-
	diffs([V|Vars],Vars,0,S).

diffs([],_,S,T):- T#=S.
diffs([_|V1],[],S,T):-
	diffs(V1,V1,S,T).
diffs([V1|PV1],[V2|PV2],S1,S2):-
	V1 #= V2 #<=> B,
	S #= B + S1,
	diffs([V1|PV1],PV2,S,S2).

def_comps(PV,Comps):-
	keysort(PV,PV0),
	def_comps_(PV0,Comps0),
	def_rec_comps(Comps0,Comps).

def_comps_([],[]).
def_comps_([K-P|PV],[[P|Comp]|Comps]):-
	def_comps_(K,PV,Comp,PV1),
	def_comps_(PV1,Comps).
def_comps_(_,[],[],[]).
def_comps_(K,[K-P|PV],[P|Comp],PV1):-!,
	def_comps_(K,PV,Comp,PV1).
def_comps_(_,[M-P|PV],[],[M-P|PV]).

def_rec_comps([],[]).
def_rec_comps([Comp|Comps],[C|Cs]):-
	member(fic,Comp),!,
	delete(Comp,fic,C),
	def_rec_comps(Comps,Cs).
def_rec_comps([Comp|Comps],[Comp|Cs]):-
	def_rec_comps(Comps,Cs).

length_(L,N):-
	length_(L,0,N).
length_([],N,N).
length_([_-fic/0|L],M,N):-
	!, length_(L,M,N).
length_([_|L],M,N):-
	M1 is M+1,
	length_(L,M1,N).
