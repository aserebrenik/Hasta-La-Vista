%%%%% last changed wtd_graph.pl
%
%                        the file   wtd_graph.pl
%                       WEIGHTED GRAPH PREDICATES
%		       =========================
:- module(wtd_graph,[w_edge/4,w_arc/5,consistent/3,
	make_weighted_rule_graph/3]).
:- use_module(library(lists)).
:- use_module(numvars).
:- use_module(compare).
:- use_module(aux).

% make_weighted_rule_graph  gets the head  Head  of a rule and its body  B,
% and returns a graph whose nodes represent the arguments of the atoms of the
% rule, its edges and weighted arcs determined by term-size comparison of the
% arguments.
make_weighted_rule_graph(Head, B, Node_sets) :-
        make_nodes(Head,B,Node_sets,Nodes).

reduce_edges_diff_arcs(Edges1,Arcs1,Diff_arcs1,Edges,Arcs,Diff_Arcs):-
        reduce_diff_arcs(Edges1,Arcs1,Diff_arcs1,Diff_arcs2),
        reduce_edges(Edges1,Diff_arcs2,Edges2),
        reduce_arcs(Edges2,Arcs1,Diff_arcs2,Arcs2),
        ( eq_e_da((Edges1,Arcs1,Diff_arcs1),(Edges2,Arcs2,Diff_arcs2)) ->
	 (Edges=Edges2,Diff_Arcs=Diff_arcs2,Arcs=Arcs2) ;
	 reduce_edges_diff_arcs(Edges2,Arcs2,Diff_arcs2,Edges,Arcs,Diff_Arcs)).

eq_e_da((L,M,J),(N,K,P)):-
    sort(L,T),sort(N,T),sort(J,Q),
    sort(P,Q),sort(M,S),sort(K,S).

reduce_edges([],_,[]).
reduce_edges([edge(N1,N2)|Edges],DiffArcs,ReducedEdges):-
		 w_edge(N1,N2,Edges,DiffArcs),!,
                 reduce_edges(Edges,DiffArcs,ReducedEdges).
reduce_edges([edge(N1,N2)|Edges],DiffArcs,[edge(N1,N2)|ReducedEdges]):-
                 reduce_edges(Edges,DiffArcs,ReducedEdges).

reduce_arcs(_,[],_,[]).
reduce_arcs(Edges,[arc(N1,N2)|Arcs],DA,ReducedArcs):-
		 pos_path(N1,N2,Edges,Arcs,DA),!,
                 reduce_arcs(Edges,Arcs,DA,ReducedArcs).
reduce_arcs(Edges,[arc(N1,N2)|Arcs],DA,[arc(N1,N2)|ReducedArcs]):-
                 reduce_arcs(Edges,Arcs,DA,ReducedArcs).

reduce_diff_arcs(_,_,[],[]).
reduce_diff_arcs(Edges,Arcs,[diff_arc(N1,N2,W)|Diff_Arcs],ReducedDiff_Arcs):-
		 wtd_path(N1,N2,Edges,Arcs,Diff_Arcs,W),!,
                 reduce_diff_arcs(Edges,Arcs,Diff_Arcs,ReducedDiff_Arcs).
reduce_diff_arcs(Edges,Arcs,[diff_arc(N1,N2,W)|Diff_Arcs],
		 [diff_arc(N1,N2,W)|ReducedDiff_Arcs]):-
                 reduce_diff_arcs(Edges,Arcs,Diff_Arcs,ReducedDiff_Arcs).

wtd_path(N1,N2,Edges,Arcs,Diff_Arcs,W) :-
    w_arc(N1,N2,Edges,Arcs,Diff_Arcs,[0],[0],[],_,W).
pos_path(N1,N2,Edges,Arcs,Diff_Arcs) :-
    w_arc(N1,N2,Edges,Arcs,Diff_Arcs,[0],[0],[],_,_).

   
make_nodes(Head, B, Node_sets, Nodes) :-
	make_s_nodes(Head,[0],Head_nodes),
	make_s_body_nodes(B,1,Body_node_sets),
	Node_sets = [Head_nodes|Body_node_sets],
	flatten(Node_sets,Nodes).
get_edges(Nodes,Edges) :-
	findall(edge(node(Functor1,Id1,Argnum1),node(Functor2,Id2,Argnum2)),
	       ( member(Node1,Nodes), member(Node2,Nodes), neq(Node1,Node2),
		 Node1=node(Functor1,Id1,Argnum1,Term1,_Size1),
		 Node2=node(Functor2,Id2,Argnum2,Term2,_Size2),
		 Node1 @< Node2,
		 compare_terms(Term1,Term2,=)),
		Edges),
		numvars(Nodes,0,_N). %%%% very important
get_diff_arcs(Nodes,Diff_arcs) :-
	     findall(diff_arc(node(Functor2,Id2,Argnum2),
		node(Functor1,Id1,Argnum1),[Diff_N|Diff_Vars]),
	       ( member(Node1,Nodes), member(Node2,Nodes),
		 Node1=node(Functor1,Id1,Argnum1,_Term1,Size1),
		 Node2=node(Functor2,Id2,Argnum2,_Term2,Size2),
		 diff(Size1,Size2,[Diff_N|Diff_Vars]), Diff_N>0),
		Diff_arcs).

% make_s_nodes(Atom,ID,Nodes) takes an Atom identified by ID,
% and constructs the nodes corresponding to its arguments.
% The ID serves to differentiate different nodes with the same predicate.
% The form of the nodes is  node(Predicate, Atom_ID, Arg_no, Arg, Size)
% where  Size  is the size of  Arg.

make_s_nodes(Atom,ID,Nodes) :- functor(Atom,P,Arity),
		make_s_nodes(Atom,ID,P,1,Arity,[],Nodes).

make_s_nodes(Atom,ID,P,I,Arity,Oldnodes,Nodes) :- I =< Arity,
		arg(I,Atom,Arg),
		size(Arg,Size), 
		I1 is I+1,
		make_s_nodes(Atom,ID,P,I1,Arity,
		     [node(P,ID,I,Arg,Size)|Oldnodes],Nodes).
make_s_nodes(_,_,_,I,Arity,Nodes,Nodes) :- I > Arity. 

make_s_body_nodes(Body,I,[Gnodes|Restnodes]) :- Body = (G,Rest), !,
		     make_s_nodes(G,[I],Gnodes),
		     I1 is I+1,
		     make_s_body_nodes(Rest,I1,Restnodes).

make_s_body_nodes(G,I,[Gnodes]) :- make_s_nodes(G,[I],Gnodes).     

% When inferring constraints for a predicate in the head of a rule, we use 
% constraints already inferred for the predicates in the body, and also the
% weighted rule graph, which also includes the weighted difference arcs.
% So we need to take into account weights when inferring the existence of edges
% or arcs. This is alluded to by the 'w' in 'w_edge' and 'w_arc'.

w_edge(Node1,Node2,Edges,Diff_Arcs) :-
     w_edge(Node1,Node2,Edges,Diff_Arcs,[0],[0],[],_).

w_edge(Node,Node,_Edges,_Diff_Arcs,Plus,Minus,Path,[Node|Path]) :-
     \+member(Node,Path), diff(Plus,Minus,[0]).
w_edge(Node1,Node2,Edges,Diff_Arcs,Plus,Minus,P1,P) :- 
     Node1\==Node2,
     (member(edge(Node1,N),Edges);member(edge(N,Node1),Edges)),
     \+member(Node1,P1),
     w_edge(N,Node2,Edges,Diff_Arcs,Plus,Minus,[Node1|P1],P).
w_edge(Node1,Node2,Edges,Diff_Arcs,Plus,Minus,P1,P) :-
     Node1\==Node2,
     member(diff_arc(Node1,N,Diff),Diff_Arcs),
     \+member(Node1,P1),
     add(Diff,Minus,Minus1),
     w_edge(N,Node2,Edges,Diff_Arcs,Plus,Minus1,[Node1|P1],P).     
w_edge(Node1,Node2,Edges,Diff_Arcs,Plus,Minus,P1,P) :-
     Node1\==Node2,
     member(diff_arc(N,Node1,Diff),Diff_Arcs),
     \+member(Node1,P1),
     add(Diff,Plus,Plus1),
     w_edge(N,Node2,Edges,Diff_Arcs,Plus1,Minus,[Node1|P1],P).     
     
w_arc(Node1,Node2,Edges,Arcs,Diff_Arcs) :-
    w_arc(Node1,Node2,Edges,Arcs,Diff_Arcs,_).
w_arc(Node1,Node2,Edges,Arcs,Diff_Arcs,N) :-    
 w_arc(Node1,Node2,Edges,Arcs,Diff_Arcs,[0],[0],[],_,N).

w_arc(Node1,Node2,Edges,_,_,Plus,Minus,P,[Node2,Node1|P],[N|R]) :-
     \+member(Node1,P),
     (member(edge(Node1,Node2),Edges);member(edge(Node2,Node1),Edges)),
     diff(Plus,Minus,[N|R]),N>0.

w_arc(Node1,Node2,_,Arcs,_,Plus,Minus,P,[Node2,Node1|P],[N|R]) :-
     \+member(Node1,P),
     member(arc(Node1,Node2),Arcs),
     diff(Plus,Minus,[N|R]),N>=0.

w_arc(Node1,Node2,_,_,Diff_Arcs,Plus,Minus,P,[Node2,Node1|P],[N|R]) :-
     \+member(Node1,P),
     member(diff_arc(Node1,Node2,Diff),Diff_Arcs),
     add(Minus,Diff,Minus1),
     diff(Plus,Minus1,[N|R]),N>0.

w_arc(Node1,Node2,_,_,Diff_Arcs,Plus,Minus,P,[Node2,Node1|P],[N|R]) :-
     \+member(Node1,P),
     member(diff_arc(Node2,Node1,Diff),Diff_Arcs),
     add(Plus,Diff,Plus1),
     diff(Plus1,Minus,[N|R]),N>0.

w_arc(Node1,Node2,Edges,Arcs,Diff_Arcs,Plus,Minus,P1,P,NN) :-
     (member(edge(Node1,N),Edges);member(edge(N,Node1),Edges)),
     \+member(Node1,P1), N\==Node2,
     w_arc(N,Node2,Edges,Arcs,Diff_Arcs,Plus,Minus,[Node1|P1],P,NN).

w_arc(Node1,Node2,Edges,Arcs,Diff_Arcs,Plus,Minus,P1,P,NN) :-
     member(arc(Node1,N),Arcs),
     \+member(Node1,P1), N\==Node2,
     add(Minus,[1],Minus1),
     w_arc(N,Node2,Edges,Arcs,Diff_Arcs,Plus,Minus1,[Node1|P1],P,NN).

w_arc(Node1,Node2,Edges,Arcs,Diff_Arcs,Plus,Minus,P1,P,NN) :-
     member(diff_arc(Node1,N,Diff),Diff_Arcs),
     \+member(Node1,P1), N\==Node2,
     add(Minus,Diff,Minus1),
     w_arc(N,Node2,Edges,Arcs,Diff_Arcs,Plus,Minus1,[Node1|P1],P,NN).

w_arc(Node1,Node2,Edges,Arcs,Diff_Arcs,Plus,Minus,P1,P,NN) :-
     member(diff_arc(N,Node1,Diff),Diff_Arcs),
     \+member(Node1,P1), N\==Node2,
     add(Plus,Diff,Plus1),
     w_arc(N,Node2,Edges,Arcs,Diff_Arcs,Plus1,Minus,[Node1|P1],P,NN).

consistent(Edges,Arcs,Diff_Arcs) :- 
    reduce_edges_diff_arcs(Edges,Arcs,Diff_Arcs,Es,As,DAs),
     \+w_arc(N,N,Es,As,DAs).



