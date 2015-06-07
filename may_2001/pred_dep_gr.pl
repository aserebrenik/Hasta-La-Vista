%%%%% last changed 23 03 2001
%
%                          the file pred_dep_gr
%            CONSTRUCTION OF THE PREDICATE DEPENDENCY GRAPH

% This module gets a logic program(without comments) and creates its predicate
% graph, where the nodes are predicate descriptors in the form 
% Predicate/Arity.
% It can find the non-trivial strongly connected components of this graph 
% (i.e. strongly connected components which do not consist of a single node 
% that does not have an arc from itself to itself) and enumerate
% the recursive predicates, that is, the predicates in these strongly connected
% components.

:- module(pred_dep_gr,[graph/3,strong_comps/3,rec_preds/2,subq/3,conn/3,
		       mut_rec/3,exist_mut_rec/1]).
:- use_module(library(lists)).
:- use_module(library(ordsets)).
:- use_module(aux).

% Given a logic program in file 'File' (without comments) 
% graph(File,Preds,Arcs)  returns its predicate graph. The vertices are
% predicate descriptors in the form  Predicate/Arity.
% Fils is used only for compatability - is not used !!!!!!!!!!!!!!!!!!!!
graph(File,Preds,Arcs) :-make_graph(File,Arcs),
			  preds(Arcs,Preds).

rec_preds(File,RPreds) :- make_graph(File,Arcs),
			  preds(Arcs,Preds),
			  strong_comps(Preds,Arcs,Comps),
			  flatten(Comps,RPreds).
  
conn(Pred1,Pred2,Arcs) :- conn(Pred1,Pred2,Arcs,[],_).
conn(Pred1,Pred2,Arcs,P,[Pred2,Pred1|P]) :- 
		\+member(Pred1,P),
		member(dep(Pred1,Pred2),Arcs).

conn(Pred1,Pred2,Arcs,P1,P) :- member(dep(Pred1,N),Arcs), 
		\+member(Pred1,P1), N \== Pred2,
		conn(N,Pred2,Arcs,[Pred1|P1],P).

mut_rec(Pred1,Pred2,Arcs) :- conn(Pred1,Pred2,Arcs),conn(Pred2,Pred1,Arcs).

node(P,Arcs) :- member(dep(P,_),Arcs).
node(P,Arcs) :- member(dep(_,P),Arcs).

exist_mut_rec(Arcs) :-
    node(P1,Arcs),
    node(P2,Arcs),
    P1 \== P2,
    mut_rec(P1,P2,Arcs).

comp(Pred,Comp,Arcs) :- findall(Q, mut_rec(Pred,Q,Arcs),Comp1), 
			sort(Comp1,Comp).

write_arcs([]).
write_arcs([X|Xs]) :- write(X),nl,write_arcs(Xs).

subq(Query,Arcs,Sub_Section) :-
	findall(New_Query,conn(Query,New_Query,Arcs),SS),
	sort([Query|SS],Sub_Section).

% we assume that the predicate graph is given by an ordered list   Arcs  of the
% form  [dep(Pred1,Pred2),dep(Pred3,Pred4),...] and compute its strong
% components
strong_comps([],_,[]).
strong_comps([P|Preds],Arcs,Comps) :-
       comp(P,C,Arcs), 
       ((C=[], !, Comps=Comps1, Preds=P1) ; 
	     (Comps=[C|Comps1],ord_subtract(Preds,C,P1)) ),
       strong_comps(P1,Arcs,Comps1).

preds(Arcs,Preds) :- findall(P,
	(member(dep(P,_),Arcs) ; member(dep(_,P),Arcs)),
		Preds1), sort(Preds1,Preds).

% MAKING THE DEPENDENCY GRAPH OF THE PROGRAM

make_graph(_File,Arcs) :- 
	process_file([],Arcs1),
	deal_rules,
	sort(Arcs1,Arcs).


deal_rules :-
	retract(user:rule(process_file,Clause)),
	assert(user:rule(Clause)),fail.
deal_rules.



% process_file(Oldarcs,Newarcs) :- read(Clause),  
%                                 make_arcs(Clause,Oldarcs,Newarcs).
process_file(Oldarcs,Newarcs) :- 
         (user:rule(Clause) -> 
	    ( 
		retract(user:rule(Clause)),
		assert(user:rule(process_file,Clause)),
		make_arcs(Clause,Oldarcs,Newarcs))
	    ;
	    Newarcs = Oldarcs).













































