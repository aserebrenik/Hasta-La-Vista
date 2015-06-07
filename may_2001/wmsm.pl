:- use_module(library(lists)).
:- use_module(aux).
:- use_module(comma).
:- use_module(numvars).

well_moded_p([Cl|Cls],Modes):-
	well_moded_cl(Cl,Modes),
	well_moded_p(Cls,Modes).
well_moded_p([],_Modes).

well_moded_cl_(Cl,Modes):-
	frz(Cl,FCl),
	well_moded_cl(FCl,Modes).

well_moded_cl((H:-B),Modes):-
        get_args(H,i,Modes,HI),
	sort(HI,SHI),
	add_true(B,Btrue),
	check_body(Btrue,Modes,SHI,Outs),
	get_args(H,o,Modes,OVars),
	subset(OVars,Outs).

check_body((B1,B2),Modes,PrevO,Outs):-
	get_args(B1,i,Modes,Vars),
	subset(Vars,PrevO),
	get_args(B1,o,Modes,OVars),
	append(OVars,PrevO,Prev_),
	sort(Prev_,Prev),
	check_body(B2,Modes,Prev,Outs).
check_body(true,_,Outs,Outs).

subset(USL,SL2):-
	sort(USL,SL1),
	subset_(SL1,SL2).

subset_([],_).
subset_([X|Xs],[Y|Ys]):-
	X@>Y, subset_([X|Xs],Ys).
subset_([X|Xs],[X|Ys]):-
	subset_(Xs,Ys).


get_args(Atom, Label, Modes, Vars):-
	get_mode(Atom, Modes, Arity, Mode),
	find_io(Mode,Atom,Label,1,Arity,[],Vars).

get_mode(Atom, Modes, Arity, Mode):-
        functor(Atom,N,Arity),
        functor(Mode,N,Arity), member(Mode,Modes).


% Label is either i or o
find_io(_Mode,_Atom,_Label,I,Arity,Args,Args):- I > Arity, !.
find_io(Mode,Atom,Label,I,Arity,Args,Result):- I =< Arity,
        (arg(I, Mode, Label) ->
                (arg(I, Atom, Arg), to_list(Arg, L), append(L,Args,Args1)) 
                ;
             Args1 = Args),
        I1 is I+1,
        find_io(Mode,Atom,Label,I1,Arity,Args1,Result).
