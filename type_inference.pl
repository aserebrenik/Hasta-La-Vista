:- module(type_inference, [type_inference/7]).
:- use_module(comma, [comma_append/3, drop_true/2]).
:- use_module(atom, [built_in/1, fresh_all/2]).
:- use_module(aux, [appears/3, id_member/2, number_to_atom/2, write_quoted/1]).

:- use_module(defs, [operators_file_name/1, output_file_name/1, type_analysis_working_directory/1]).

:- use_module(library(lists), [append/3, delete/3, last/2, member/2, reverse/2]).
:- use_module(library(ordsets), [ord_subset/2]).
:- use_module(library(system), [delete_file/1, exec/3, shell/1, wait/2, working_directory/2]).


integer_term(_*_) :- !.
integer_term(_+_) :- !.
integer_term(_-_) :- !.
integer_term(_/_) :- !.
integer_term(_ mod _) :- !.
integer_term(_ is _) :- !.
integer_term(T) :- integer(T).

add_explicit_unifications(write(Text), write(Text), true) :- !.
add_explicit_unifications([], [], true).
add_explicit_unifications([Term|Terms], [Var|Vars], (Var=Term, Unifications)):-
	var(Term), id_member(Term, Terms),
	!, add_explicit_unifications(Terms, Vars, Unifications).
add_explicit_unifications([Term|Terms], [Term|Vars], Unifications):-
	var(Term),
	!, add_explicit_unifications(Terms, Vars, Unifications).
/*
add_explicit_unifications([Term|Terms], [Var|Vars],
			  (Var is Term, Unifications)):-
	integer_term(Term),
	!, add_explicit_unifications(Terms, Vars, Unifications).
*/
add_explicit_unifications([Term|Terms], [Var|Vars], (Var=Term, Unifications)):-
	!, add_explicit_unifications(Terms, Vars, Unifications).
add_explicit_unifications(Atom, NewAtom, Unifications):-
	Atom =.. [Head|Args],
	add_explicit_unifications(Args, NewArgs, Unifications),
	NewAtom =.. [Head|NewArgs].

add_explicit_unifications([], []).
add_explicit_unifications([Clause|Clauses],[NewClause|NewClauses]):-
	add_explicit_unifications(Clause, NewClause),
	add_explicit_unifications(Clauses, NewClauses).

add_explicit_unifications(clause(nohead, nobody),
			  clause(nohead, nobody)):-!, fail. 
add_explicit_unifications(clause(Head,Body), clause(NewHead, NewBody)):-
	add_explicit_unifications(Head, NewHead, HeadUnifications),
	add_explicit_unifications(Body, NewBody1),
	comma_append(HeadUnifications, NewBody1, NewBody), !.

add_explicit_unifications(true, true).
add_explicit_unifications((Var is Exp,Atom2),
			  (V is Var, V is Exp, NewAtoms2)):-
	\+ var(Var), integer_term(Var), !, 
	add_explicit_unifications(Atom2, NewAtoms2).
add_explicit_unifications((Var is Exp,Atom2), (Var is Exp, NewAtoms2)):- !, 
	add_explicit_unifications(Atom2, NewAtoms2).
add_explicit_unifications((\+ Atom1, Atom2), NewAtoms):- !,
	add_explicit_unifications(Atom1, NewAtom1, AtomUnifications),
	comma_append(AtomUnifications, (\+ NewAtom1, NewAtoms2), NewAtoms),
	add_explicit_unifications(Atom2, NewAtoms2).
add_explicit_unifications((Atom1,Atom2), NewAtoms):-
	add_explicit_unifications(Atom1, NewAtom1, AtomUnifications),
	comma_append(AtomUnifications, (NewAtom1, NewAtoms2), NewAtoms),
	add_explicit_unifications(Atom2, NewAtoms2).

%% prepare_input(Clauses, quicksort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'),[], NewClauses)
prepare_input(Clauses, Query, Share, NewClauses, PredsWithoutDefs):-
	%%%write('preparing input 0'),nl,
	%%%aux:writel(Clauses),

	add_a0(Clauses, Clauses1),

	%%%write('a0 added'),nl,
	%%%aux:writel(Clauses),
	%%%write('a0 added - result, Clauses1'),nl,
	%%%aux:writel(Clauses1),
	add_explicit_unifications(Clauses1, NewClauses1),

	%%%write('explicit unifications added'),nl,
	%%%aux:writel(Clauses),
	
	output_file_name(Output), tell(Output),
	write(':- include('),

	operators_file_name(OFN),
	%%%write('''/home/alexande/aisys/rigidt/operator.pro'''),
	write(OFN),
	
	write(').'), nl, write(':- setdebug.'), nl, nl,

	% added to group all clauses of the same predicate together
	sort(NewClauses1, NewClauses),
	
	write_clauses(NewClauses),
	write_fail_definitions(NewClauses, A0PredsWithoutDefs),
	add_a0(PredsWithoutDefs, A0PredsWithoutDefs),
	
	nl, nl,
	write('query :- tp_construct('),

	functor(Query, Name, Arity), add_a0(Name, A0Name),
	gen_vars(Arity, Vars), write_quoted(Vars), write(', '),
	Query =.. [_|Args], write(Args),
	write(', _tpcomp),'), 
	write('abi(TERM('), write(A0Name/Arity), write(', '),
	write_quoted(Vars), write(', '), write_quoted(Vars), write('),'),
	write('ABSU(_tpcomp,'), write(Share), write(')).'),
	nl, nl,
	write(':- dynamic absu_spec_init/0 .'), nl, 
        write('absu_spec_init .'), nl,
	write(':- dynamic tg_spec_write/2 .'), nl,
	write('tg_spec_write(_key,_ntg) :-fail.'), nl,
	atom_concat(Output1, '.pro', Output),       
	write('?- init(['''), write(Output1), write(''']).'),
	nl, nl,
	write('?- query.'), nl, nl, write('?- halt.'), nl,
        told.
	
% add_a0(Clauses, NewClauses) adds a0 to all predicates. this is
% done to avoid confusion with the built-in predicates of PLeng (Master Prolog)
% works in both directions

add_a0([], []).
add_a0(clause(H,B), clause(H1,B1)) :-
	!, add_a0(H,H1), add_a0(B,B1).
add_a0(true, true) :- !.
add_a0((B1,B2), (B11, B12)):-
	!, add_a0(B1,B11), add_a0(B2,B12).
add_a0([B1|B2], [B11|B12]) :-
	!, add_a0(B1,B11), add_a0(B2,B12).
add_a0(type(Name/A,Args),type(A0Name/A,Args)):- !,
	atom_concat(a0,Name,A0Name).
add_a0(B, B):- built_in(B), !.
add_a0(\+ B1, \+ B2):- !,
	add_a0(B1, B2).
add_a0(B, B):- number(B), !.
add_a0(B1, B2):-
	var(B2), !,
	B1 =.. [Name|Args], atom_concat(a0,Name,A0Name),
	B2 =.. [A0Name|Args].
add_a0(B1, B2):-
	var(B1), !,
	B2 =.. [A0Name|Args], atom_concat(a0,Name,A0Name),
	B1 =.. [Name|Args].


%% it also adds quotes to signs such as ( ) * + etc

user:portray(X) :- atom(X), \+ X = [], \+ X = !,
                   write(''''),
		   (X = '\\' -> write('\\') ; true),
		    write(X),
		     write('''').

write_clauses([]).
write_clauses([clause(Head,Body)|Clauses]):-
	copy_term(clause(Head,Body), CurrClause),
	user:bad_clause(BadClause),
	add_explicit_unifications(BadClause, Explicit),
	add_a0(Explicit, A0Explicit),
	A0Explicit = CurrClause,
	write_clauses(Clauses).
write_clauses([clause(Head,Body)|Clauses]):-
	(drop_true(Body, Body1) ->
	    print((Head:-Body1)),
	    write(' .'), nl,
	    write_clauses(Clauses)
	;
	    write(Head),
	    write(' .'), nl,
	    write_clauses(Clauses)).

% write_fail_definitions writes definitions of predicates that
% do not have definitions in the original program, that is r:- fail.
% this step is required for type analysis, since it assumes that every
% predicate has a definition

write_fail_definitions(Clauses, PredsWithoutDefs) :-
	build_definitions(Clauses, Clauses, NewClauses, PredsWithoutDefs),
	write_clauses(NewClauses).

build_definitions(true, _, [], []).
build_definitions((B1, B2), Clauses, Ns, Ps):-
	fresh_all(B1, B),
	((member(clause(B, _), Clauses) ; built_in(B)) ->
	    build_definitions(B2, Clauses, Ns, Ps)
	;
	    build_definitions(B2, Clauses, N, P),
	    Ps = [B|P],
	    Ns = [clause(B,fail)|N]).
build_definitions([], _, [], []).
build_definitions([clause(_,B)|Cs], Clauses, NewClauses, PredsWithoutDefs) :-
	build_definitions(B, Clauses, Ns, Ps),
	(Ns = [] ->
	    build_definitions(Cs, Clauses, NewClauses, PredsWithoutDefs)
	;
	    build_definitions(Cs, Clauses, NCs, PWOs),
	    append(Ns, NCs, NewClauses),
	    append(Ps, PWOs, PredsWithoutDefs)).



gen_vars(0, []).
gen_vars(N, [_|Vs]):-
	N > 0, N1 is N-1, gen_vars(N1, Vs).


execute_type_inference(OldDirectory) :-
	type_analysis_working_directory(TAWD),
	%%%working_directory(OldDirectory, '/home/alexande/aisys/adi/'),
	working_directory(OldDirectory, TAWD),
	working_directory(D,D), 
	exec('PLeng mystart rtyt/output > rtyt/Di',[std,std,std],Pid),
	wait(Pid, Status),
	(Status = 0 -> true ; write('Type inference failed.'), nl).

analyse_results(OldDirectory, Clauses, Clauses1, IOs, Results1, NewClauses):-
	see('rtyt/Di'),

	% i do not know why this is needed, but let us try
	% if this line is ommitted, after analysing permutation
	% next analysis fails while attempting to read past end of stream
	current_stream(_, read, Stream), seek(Stream, 0, bof, _Pos),

	get_results(Types, Heads),
	%%%delete_file('rtyt/Di'),
	
	check_results(Types, Heads, Clauses, Clauses1,
		      IOs, Results1, NewClauses),
	seen, working_directory(_, OldDirectory).

/*
read_program('../examples/quicksort',Clauses),
type_inference(Clauses, quicksort('[T1 $= [] $| \'.\'(Int, T1)]','[T2 $=MAX]'),
	       [], Calls, IO).
*/
type_inference(Clauses, Query, Share, NewClauses, Calls, IO,
	       PredsWithoutDefs):-

	prepare_input(Clauses, Query, Share, Clauses1, PredsWithoutDefs),
	
	execute_type_inference(OldDirectory),!,
	analyse_results(OldDirectory, Clauses,
			Clauses1, A0IO, Results_, NewClauses),

	%%%%%%%%%tell('MYFILE'), write_clauses(NewClauses), told,
	add_a0(Results, Results_),
	add_a0(IO_, A0IO),
	to_simple_list(IO_,IO),
	get_calls(Results, Calls).

to_simple_list([], []).
to_simple_list([[X]|Xs], [X|Ys]):-
	to_simple_list(Xs, Ys).

get_io([], []).
get_io([type(Name/Arity,Types)|Ts], [(Pred, In, Out)|IOs]):-
	functor(Pred, Name, Arity), args_io(Types, 1, In1, Out1),
	((Arity > 0, In1 = []) ->
	    args_max_io(Types, 1, In, Out)
	;
	    In = In1, Out = Out1),
	get_io(Ts, IOs).

args_max_io([], _, [], []).
args_max_io(['MAX'|Xs], N, Is, [N|Os]):-
	!, N1 is N+1, args_max_io(Xs,N1,Is,Os).
args_max_io([_I|Xs], N, [N|Is], Os):-
	N1 is N+1, args_max_io(Xs,N1,Is,Os).

args_io([], _, [], []).
args_io([O|Xs], N, Is, [N|Os]):-
	atomic(O),!, N1 is N+1, args_io(Xs,N1,Is,Os).
args_io([I|Xs], N, [N|Is], Os):-
	loop_in_type(I),!, N1 is N+1, args_io(Xs,N1,Is,Os).
args_io([_|Xs], N, Is, [N|Os]):-
	N1 is N+1,
	args_io(Xs,N1,Is,Os).

% loop_in_type(I) checks wether the type I contains a loop
loop_in_type(X):-
	number(X).
loop_in_type(I):-
	compound(I), !,
	I =.. [_,L],
	at_least_one_loop_in_type(L).

at_least_one_loop_in_type(L):-
	member(X,L), loop_in_type(X).

get_calls([], []).
get_calls([type(Name/_Arity,Types)|Ts], [Call|Calls]):-
	Call =.. [Name|Types],
	get_calls(Ts, Calls).


get_results_head(type(NName/NArity,NArgs,NTypes,head)):-
	read_until(' ', atom, NName),
	get_char(_), get_char(_), % / and space
	read_until('[', number, NArity),
	read_args_(NArity, NArgs),
	read_until(':', number, NumArgTypes),
	read_types(NumArgTypes, NTypes).
	  
get_results_call(type(Name/Arity,Args,Types)):-
	read_until(' ', atom, Name),
	get_char(_), get_char(_), % / and space
	read_until('[', number, Arity),
	read_args_(Arity, Args), get_char('-'),
	read_types(Arity, Types). %%% get heads of the clauses

get_result_(X):-
	ignore_until('|'),
	get_char(Char),
	(Char = '+' ->
	    get_results_call(X) ; true),
	(Char = '*' ->
	    get_results_head(X) ; true).
	
get_results_(Results):-
	(get_result_(Type) ->
	    Results = [Type|Results1],
	    get_results_(Results1)
	;
	    Results = []).

get_results(Types, Heads):-
	get_results_(Results),
	divide(Results, Types, Heads).

divide([], [], []).
divide([type(_N/_A,_Args,['BOTTOM'-notype])|Rs], Ts, Hs):- !,
	divide(Rs,Ts,Hs).
divide([type(N/A,Args,Types)|Rs], [type(N/A,Args,Types)|Ts], Hs):-
	divide(Rs,Ts,Hs).
divide([type(N/A,Args,Types,head)|Rs], Ts,
       [type(N/A,Args,Types,Related)|Hs]):-
	get_related(type(N/A,Args,Types,head),Rs,Related),
	divide(Rs,Ts,Hs).

% get_related(type(N/A,Args,Types,head),Results,Related)
get_related(type(N/A,Args,Types,head),Results,Related) :-
	get_segment(type(N/A,Args,Types,head),Results,Segment),
	get_related_calls(Segment,Types,Related).

get_segment(type(N/A,Args,_Types,head),Results,Segment) :-
	append(Segment, [type(N/A,Args,_,head)|_],Results), !. 
get_segment(type(_N/_A,_Args,_Types,head),Results,Results).

get_related_calls([], _, []).
get_related_calls([type(_,_,_,head)|Segment],Types,Related):-
	!, get_related_calls(Segment,Types,Related).
get_related_calls([type(N/A,Args,T)|Segment],Types,
		  [type(N/A,Args,T)|Related]):-
	member(Arg, Args), member(Arg-_,Types),
	!, get_related_calls(Segment,Types,Related).
get_related_calls([type(_,_,_)|Segment],Types,Related):-
	get_related_calls(Segment,Types,Related).

check_results(Types, Heads, Clauses, Clauses1, IOs, Results10, NewClauses):-
%	aux:writel(Clauses),
%	aux:writel(Clauses1),
	use_definitions(Types, Results1),
	substitute(Results1, Results2),
	drop_arities(Results2, Results3),
	sort(Results3, Results4),
	compact(Results4, IOs_),
	each_predicate_appears_once(IOs_,MoreThanOnce),
	(MoreThanOnce = [] ->
	    Results10 = Results4,
	    NewClauses = Clauses,
	    IOs = IOs_
	;
	    use_definitions(Heads, Heads1),
	    prepare_variant_names(MoreThanOnce, NewNames),
	    %%%%aux:timer(''),
	    rewrite_clauses(NewNames, Results1, Heads1, Clauses1, NewClauses_),
	    %%%%aux:timer('AFTER '),
	    add_a0(NewClauses__, NewClauses_),
	    remove_quotes(NewClauses__, NewClauses),
	    %%%%aux:writel(NewClauses),
	    build_io(IOs_, NewNames, IOs__),
	    sort(IOs__, IOs),
	    build_results(Results4, NewNames, Results10)).

build_io([], _, []).
build_io([[(Call, In, Out)]|IOs_], NewNames,[[(NewCall, In, Out)]|IOs]):-
	member((Call, In, Out, NewName), NewNames), !,
	functor(Call, _, Arity), functor(NewCall, NewName, Arity),
	build_io(IOs_, NewNames, IOs).
build_io([[(Call, In, Out)]|IOs_], NewNames,[[(Call, In, Out)]|IOs]):-
	build_io(IOs_, NewNames, IOs).

build_results([], _, []).
build_results([type(N/A,Types)|Results], NewNames, NewResults) :-
	findall(type(N1/A, Types),
		(
		  get_io([type(N/A,Types)], [(_, In, Out)]),
		  functor(Head, N, A),
		  ( get_name((Head, In, Out, NewName), NewNames) ->
		      N1 = NewName ; N1 = N)
		), NsAs),
	build_results(Results, NewNames, NewResults1),
	append(NsAs,NewResults1,NewResults).

compact(Types1, IOs):-
	compact(Types1, [], IOs).
compact([], IOs, IOs).
compact([Type1|Types1], IOs, NewIOs):-
	get_io([Type1], IO),
	((member(IO, IOs) ;
	  IO = [(Pred, In, _Out)],
	  member([(Pred, In1, _Out1)], IOs),
	  (ord_subset(In1, In) ; ord_subset(In, In1)))
	    -> IOs2 = IOs ; IOs2 = [IO|IOs]),
	compact(Types1, IOs2, NewIOs).

prepare_variant_names([], []).
prepare_variant_names([[(P,I,O)]|IOs], [(P,I,O,Name)|Names]):-
	appears([(P,_,_)],IOs,Num),
	number_to_atom(Num,Atom),
	functor(P,N,_),
	atom_concat(N,Atom,Name),
	prepare_variant_names(IOs, Names).


rewrite_clauses(_, _, _, [], []).
rewrite_clauses(Dictionary, _Results, Heads,
		[clause(Head,Body)|Clauses], NewClauses) :-
	functor(Head, Name, Arity), Head =.. [_|Args],
	quote_term(Args, QArgs),

	findall(clause(Head1, Body1),
		(
		  member(type(Name/Arity, QArgs, Types, Related), Heads),
		  build_head(Name/Arity, QArgs, Types, Dictionary, Head1),
		  build_body(Body, Dictionary, Related, Body1)
		  ), NewClauses1),
	rewrite_clauses(Dictionary, _Results, Heads, Clauses, NewClauses2),
	append(NewClauses1, NewClauses2, NewClauses).

build_head(Name/Arity, QArgs, Types, Dictionary, Head1):-
	substitute([type(Name/Arity, QArgs, Types)], SubstType),
	get_io(SubstType, [(_, In, Out)]),
	functor(Head, Name, Arity),
	( get_name((Head, In, Out, NewName), Dictionary) ->
	    Head1 =.. [NewName|QArgs] ; Head1 =.. [Name|QArgs]).

build_body(true, _, _, true) :- !.
build_body(B, _, _, B1) :-
	built_in(B),!, quote_term(B,B1).
build_body((B1,B2), Dictionary, Related, (B11, B12)):-
	!, build_body(B1, Dictionary, Related, B11),
	build_body(B2, Dictionary, Related, B12).
build_body(B, Dictionary, Related, B1):-
	functor(B, N, A), B =.. [_|Args],
	quote_term(Args, QArgs),
	member(type(N/A,QArgs,Types), Related), !,
	build_head(N/A, QArgs, Types, Dictionary, B1).
build_body(B, _Dictionary, _Related, B1) :-
	quote_term(B,B1).
		   
get_name((Head, In, Out, NewName), Dictionary) :-
	member((Head, In, Out, NewName), Dictionary), !.
get_name((Head, In, _Out, NewName), Dictionary) :-
	member((Head, In1, _Out1, NewName), Dictionary),
	ord_subset(In1, In).

quote_term(X, X):- ground(X), !.
quote_term(X, Y):- var(X), !, tell('_'), write(X), write('.'), told,
	see('_'), read_until('.', atom, Y), seen.
quote_term([], []).
quote_term([X|Xs], [Y|Ys]):- !, quote_term(X, Y), quote_term(Xs, Ys).
quote_term(X, Y):-
	compound(X), !, X =.. [F|Args],
	quote_term(Args, Args1), Y=.. [F|Args1].

remove_quotes([], []) :- !.
remove_quotes([X|Xs], [Y|Ys]):- !, remove_quotes(X, Y, _),
	remove_quotes(Xs, Ys).
remove_quotes([], [], _) :- !.
remove_quotes([X|Xs], [Y|Ys], D):- !, remove_quotes(X, Y, D),
	remove_quotes(Xs, Ys, D).
remove_quotes(X, Y, D):-
	compound(X), !, X =.. [F|Args],
	remove_quotes(Args, Args1, D), Y=.. [F|Args1].
remove_quotes(X, X, _D):- \+ atom_concat('_', _, X), !.
remove_quotes(X, Y, Z):- vmember((X,Y), Z), !.
remove_quotes(X, Y, Z):- vadd((X,Y), Z).

vmember(_X,L):-var(L),!, fail.
vmember(X,[X|_L]) :- !.
vmember(X,[_|L]) :- vmember(X,L).

vadd(X,L):- var(L), !, L=[X|_].
vadd(X,[_|L]) :- vadd(X,L).

use_definitions_type('List',  'OR'(['[] / 0', .([2, ['Int', 2]])])) :- !. 
use_definitions_type('ListOne',  .([2,['MAX', 'OR'(['[] / 0', 0])]])) :- !. 
use_definitions_type(X, X).

use_definitions([], []).
use_definitions([type(N/A,Vars,Types)|T], [type(N/A,Vars,Types1)|T1]):-
	use_definitions(Types, Types1),
	use_definitions(T,T1).
use_definitions([type(N/A,Vars,Types,Related)|T],
		[type(N/A,Vars,Types1,Related1)|T1]):-
	use_definitions(Types, Types1),
	use_definitions(Related, Related1),
	use_definitions(T,T1).
use_definitions([Var-Type|Pairs], [Var-Type1|Pairs1]):-
	use_definitions_type(Type, Type1),
	use_definitions(Pairs, Pairs1).

substitute([], []).
substitute([type(N/A,Vars,Types)|T], [type(N/A,Types1)|T1]):-
	  replace_vars_types(Vars, Types, Types1),
	  substitute(T, T1).

replace_vars_types([], _, []).
replace_vars_types([Var|Vars], Types, [Type|Types1]):-
	member(Var-Type, Types),
	replace_vars_types(Vars, Types, Types1).

drop_arities([], []).
drop_arities([type(N/A,Types1)|T1], [type(N/A,Types2)|T2]):-
	drop_arities_(Types1, Types2),
	drop_arities(T1, T2).
drop_arities_([], []).
drop_arities_([Type1|Types1], [Type2|Types2]):-
	drop_arities__(Type1, Type2),
	drop_arities_(Types1, Types2).
drop_arities__(X, X):- atomic(X), !.
drop_arities__('OR'(X), 'OR'(Y)):- !,
	drop_arities__(X,Y).
drop_arities__([X|Xs], [Y|Ys]) :- !,
	drop_arities__(X,Y),
	drop_arities__(Xs,Ys).
drop_arities__(X, Y) :-
	X =.. [Name, [_Arity|Args1]],
	drop_arities__(Args1, Args2),
	Y =.. [Name | Args2].

each_predicate_appears_once(IOs,MoreThanOnceIOs) :-
	each_predicate_appears_once(IOs,[],MoreThanOnceIOs).
each_predicate_appears_once([],_,[]).
each_predicate_appears_once([[(P,I,O)]|T], IOs, MoreThanOnce):-
	\+ member([(P, _, _)], T), !,
	(member([(P,_,_)], IOs) ->
	    MoreThanOnce = [[(P,I,O)]|MoreThanOnce_]
	;
	    MoreThanOnce = MoreThanOnce_),
	each_predicate_appears_once(T, IOs, MoreThanOnce_).
each_predicate_appears_once([[(P,I,O)]|T], IOs, [[(P,I,O)]|MoreThanOnce]):-
	each_predicate_appears_once(T, [[(P,I,O)]|IOs], MoreThanOnce).


/*
only_most_general_ones([], []).
only_most_general_ones([type(N/A,Types)|T1], [type(N/A,Types)|T2]):-
	\+ member(type(N/A,_OtherTypes), T1), !,
	only_most_general_ones(T1,T2).
only_most_general_ones([type(N/A,Types)|T1], T2):-
	findall(OtherTypes,
		member(type(N/A,OtherTypes), T1), 
		ListOfOtherTypes),
	l_delete(N/A, T1, ListOfOtherTypes, T3),
	maxima([Types|ListOfOtherTypes], Maxima), 
	only_most_general_ones(T3, T4),
	add_maximal_types(N/A, Maxima, T4, T2).
 
maxima([], []).
maxima([H|List], Maxima):-
	member(G, List),
	bigger_eq(G,H),
	!, maxima(List, Maxima).
maxima([H|List], [H|Maxima]):-
	member(G, List),
	bigger_eq(H, G),
	delete(List, G, List1),
	maxima(List1, Maxima).
maxima([H], [H]).

% add_maximal_types(N/A, Maxima, OldList, NewList)
add_maximal_types(N/A, [M|Maxima], OldList, NewList):-
	add_maximal_types(N/A, Maxima, [type(N/A,M)|OldList], NewList).
add_maximal_types(_, [], List, List).

bigger_eq([], []).
bigger_eq([Type1|Types1], [Type2|Types2]):-
	geq(Type1, Type2, []),
	bigger_eq(Types1, Types2).

lb(X, _OrX, N/A):- \+ number(X),!, functor(X,N,A).
lb(0, OrX, N/A) :- functor(OrX, N,A).
lb(X, _OrX, _N/A) :- X > 0,
	write('*** Temporary unavailable ***'), nl.

args(X, _OrX, Args):- \+ number(X), !, X =.. [_,Args].
args(0, OrX, Args):- OrX =.. [_, Args].
args(X, _OrX, _N/A) :- X > 0,
	write('*** Temporary unavailable ***'), nl.
	
% prnd(n) Janssens Bruynooghe, p. 224

prnd(X, OrX, S):- lb(X, OrX, 'OR'/1), !,
	args(X, OrX, XArgs), prnd_list(XArgs, OrX, S).
prnd(X, _, [X]).

prnd_list([], _, []).
prnd_list([X|Xs], OrX, S):-
	prnd(X, OrX, S1), prnd_list(Xs, OrX, S2), append(S1, S2, S).

geq(X,Y,S):-
	leq(Y,X,Y,X,S).
% leq - containment check (Algorithm =<. Janssens Bruynooghe, p. 227)
% third and fourth arguments were added to resolve backwarts edges
leq(_,'MAX',_,_,_) :- !.
leq(X,X,_,_,_)     :- !.
leq(X,Y,_,_,S):-
	member((X,Y), S), !.
leq(X, Y, OrX, OrY,S):-
	lb(X, OrX, 'OR'/1), lb(Y, OrY, 'OR'/1), 
	!, args(X, OrX, XArgs),
	leq_for_all_args(XArgs, Y, OrX, OrY, [(X,Y)|S]).
leq(X, Y, OrX, OrY, S):-
	lb(Y, OrY, 'OR'/1), !,
	prnd(Y, OrY, SY), lb(X, OrX, N/A),
	member(MD, SY), lb(MD, Y, N/A), 
	leq(X, MD, OrX, OrY, [(X,Y)|S]).
leq(X, Y, OrX, OrY, S):- % nodes labeled by functors
	lb(X, OrX, N/A),lb(Y, OrY, N/A), A>0, !,
	X =.. [_|XArgs], Y =.. [_|YArgs],
	leq_for_all_args(XArgs, YArgs, OrX, OrY, [(X,Y)|S]).
leq(X,Y, OrX, OrY, _) :-
	lb(X, OrX, N/A),lb(Y, OrY, N/A).

leq_for_all_args([], _, _, _, _).
leq_for_all_args([X|Xs],[Y|Ys],OrX, OrY, S):-
	!, leq(X,Y,OrX, OrY,S),
	leq_for_all_args(Xs,Ys,OrX, OrY,S).
leq_for_all_args([X|Xs],Y,OrX, OrY,S):-
	leq(X,Y,OrX,OrY,S), leq_for_all_args(Xs,Y,OrX, OrY,S).

l_delete(_, List, [], List).
l_delete(N/A, List1, [H|List2], List3):-
	delete(List1, type(N/A, H), List),
	l_delete(N/A, List, List2, List3).
*/
ignore_until(Char):-
	get_char(C),
	(C = Char -> true ;
	    (C = end_of_file -> fail ; ignore_until(Char))).

read_until_var(Type):-
	read_until('_', atom, Type1),
	get_code(G),
	((G >= 49, G =< 57) ->	% G is a digit.
	    current_stream(_, read, Stream),
	    seek(Stream, -1, current, _),
	    Type = Type1
	;
	    atom_concat(Type1, '_', Type1_),
	    current_stream(_, read, Stream),
	    seek(Stream, -1, current, _),
	    read_until_var(Type2),
	    atom_concat(Type1_, Type2, Type)
	    ).

read_until(Char, Mode, Word):-
	read_until(Char, Mode, Word, EOF),
	(EOF = true ->
	    write('Unexpected end of file'), nl, halt
	;
	    true).
read_until(Char, Mode, Word, EOF):-
	atom_chars(Char, [Code]),
	read_until_(Code, List, EOF),
	(Mode = atom -> atom_codes(Word, List)
	; (Mode = number -> number_codes(Word, List)
	  ; write('internal error'))).
read_until_(Code, L, EOF):-
	get_code(C),
	(C = Code -> L = [], EOF = false ;
	    (C = -1 -> L = [], EOF = true ;
		L=[C|L1], read_until_(Code, L1, EOF))).


read_args_(0, []) :-
	get_char(']').
read_args_(1, [Variable]) :-
	read_until(']', atom, Variable).
read_args_(Arity, [Variable|Variables]):-
	Arity > 1, read_until(',', atom, Variable), 
	Arity1 is Arity -1, read_args_(Arity1, Variables).

remove_share_info(Type1, Type2):-
	atom_chars(Type1, Chars),
	reverse(Chars, [_|RevChars]),
	cut_list(RevChars, 1, RestChars),
	reverse(RestChars, RevRestChars),
	atom_chars(Type2, RevRestChars).

cut_list(L, 0, L) :- !.
cut_list([93|L], N, Rest):- !,
	N1 is N+1,
	cut_list(L, N1, Rest).
cut_list([91|L], N, Rest):- !,
	N1 is N-1,
	cut_list(L, N1, Rest).
cut_list([_|L], N, M):- cut_list(L, N, M).

read_types(0, []).
read_types(1, [Variable-Type]):-
	read_until(' ', atom, Variable),
	(Variable = 'BOTTOM' -> Type = notype
	;
	    get_char(' '),
	    read_until('\n', atom, Type1, _EOF),
	    (atom_concat(Type_, '[]', Type1) ->
		true ;
		(remove_share_info(Type1, Type_) ->
		    true ;
		    write('Unexpected end of file'), nl, halt)),
	    to_type(Type_, Type)).
read_types(Arity, [Variable-Type|Types]):-
	Arity > 1, read_until(' ', atom, Variable),
	get_char(' '), read_until_var(Type_),
	to_type(Type_, Type),
	current_stream(_, read, Stream),
	seek(Stream, -1, current, _),
	Arity1 is Arity-1, read_types(Arity1, Types).


to_type('MAX',     'MAX')        :- !.
to_type('Int',     'Int')        :- !.
to_type('List',    'List')       :- !.
to_type('ListOne', 'ListOne')    :- !.
to_type(X, X):- number(X).
to_type(String,    Term)         :-
	atom_chars(String, StringCodes),
	append(StringCodes_, [41], StringCodes), % ')'
	append(FunctorCodes, [40|ArgCodes], StringCodes_), % '('
	!,
	atom_chars(Functor, FunctorCodes),
	to_type_args(ArgCodes, ListOfLists),
	to_args(ListOfLists, [Args]),
	Term =.. [Functor, Args].
to_type(String,    Term)         :-
	atom_chars(String, StringCodes),
	append([91|ArgCodes], [93], StringCodes), % '[' ']'
	!,
	to_type_args(ArgCodes, ListOfLists),
	to_args(ListOfLists, Args),
	Term = Args.
to_type(String,    Term)         :-
	atom_chars(String, StringCodes),
	append(FunctorArgCodes, [93], StringCodes), % ']'
	append(FunctorCodes_, [91|ArgCodes], FunctorArgCodes), % '['
	drop_spaces(FunctorCodes_, FunctorCodes),
	atom_chars(Functor, FunctorCodes),
	to_type_args(ArgCodes, ListOfLists),
	to_args(ListOfLists, Args),
	Term =.. [Functor, Args].
to_type(String, String).

drop_spaces([32|T],H):- !, drop_spaces(T,H).
drop_spaces(T,H):- drop_spaces_(T,H).

drop_spaces_([32|T],H):- !, drop_spaces__(T,H).
drop_spaces_([X|T],[X|H]) :- drop_spaces_(T,H).

drop_spaces__([32|T],H):- drop_spaces__(T,H).
drop_spaces__([], []).

divide_by_comma(Codes, [First|ListOfLists]):-
	append(First, [44|Second], Codes), 
	balanced(First), \+ First = [], !,
	divide_by_comma(Second, ListOfLists).
divide_by_comma(Codes, [Codes]).

% special case '( / 0' and ') / 0' are also balanced
balanced([40,32,47,32,48]) :- !.
balanced([41,32,47,32,48]) :- !.
balanced(Codes):-
	balanced(Codes, 0, 0).
balanced([], 0, 0).
balanced([91|Codes], N, M) :-
	!, balanced(Codes, N, s(M)).
balanced([93|Codes], N, s(M)) :-
	!, balanced(Codes, N, M).
balanced([40|Codes], N, M) :-
	!, balanced(Codes, s(N), M).
balanced([41|Codes], s(N), M) :-
	!, balanced(Codes, N, M).
balanced([_|Codes], N, M):-
	 balanced(Codes, N, M).

to_type_args([91|ArgCodes], (ListOfLists, [])) :- !,
	append(ArgCodes_, [93], ArgCodes),
	divide_by_comma(ArgCodes_, ListOfLists).
to_type_args([40|ArgCodes], (ListOfLists, '()')) :- !,
	append(ArgCodes_, [41], ArgCodes),
	divide_by_comma(ArgCodes_, ListOfLists).
to_type_args(ArgCodes, ListOfLists) :- 
	divide_by_comma(ArgCodes, ListOfLists).

to_args([], []).
to_args((Codes, []), [Args]):-
	to_args(Codes, Args).
to_args((Codes, '()'), (Args)):-
	to_args(Codes, Args).
to_args([Code|Codes], [Arg|Args]):-
	name(String, Code),
	to_type(String, Arg),
	to_args(Codes, Args).
/*
to_type('MAX',     'MAX')        :- !.
to_type('Int',     'Int')        :- !.
to_type('List',    'List')       :- !.
to_type('ListOne', 'ListOne')    :- !.
	
to_type(String,    Term)         :-
	atom_chars(String, StringCodes),
	add_quotes(StringCodes, QuotedCodes),
	atom_chars(Quoted, QuotedCodes),
	tell(t), write(Quoted), told,
	see(t), read(Term), seen.
add_quotes([], []).
add_quotes([Code|Codes], [39, Code|QuotedCodes]) :- % add quote
	capital(Code), !,
	add_quotes_(Codes, QuotedCodes).
add_quotes([Code|Codes], [Code|QuotedCodes]) :- 
	add_quotes(Codes, QuotedCodes).

add_quotes_([], []).
add_quotes_([Code|Codes], [39, Code|QuotedCodes]) :- % add quote
	delimiter(Code), !,
	add_quotes(Codes, QuotedCodes).
add_quotes_([Code|Codes], [Code|QuotedCodes]) :- 
	add_quotes_(Codes, QuotedCodes).

capital(Code):-
	cap_a(A), cap_z(Z),
	Code >= A, Code =< Z.

cap_a(65).
cap_z(90).

delimiter(Code) :- Code =< 32. % layout
delimiter(40).                 % (
delimiter(41).                 % )
delimiter(91).                 % [
delimiter(93).                 % ]
delimiter(44).		       % ,
delimiter(46).                 % .

*/