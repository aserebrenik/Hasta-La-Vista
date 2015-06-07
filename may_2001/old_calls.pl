:- module(calls,[find_calls/3]).
:- use_module(library(ordsets)).
:- use_module(library(lists)).
:- use_module(wtd_graph).

find_calls(Query,Clauses,Calls):-
	findqueries(Query,[],Calls,Clauses).

nodies(X,X).

findqueries([],L,L,_) :- !.
findqueries(Querylist,Oldqueries,L,Clauses) :-
%%% the following 3 lines are just to see how the algorithm is progressing
%(verbose -> (
             nl,
             write('New queries:'),nl,
             nodies(Querylist,Ql1),write(Ql1),nl%) ; true)
	     ,
%%%

   find_new_qs_l(Querylist,Newqueries,Clauses),
   list_to_ord_set(Newqueries,Newqueries1),
   ord_subtract(Newqueries1,Oldqueries,NewQ),
   ord_union(Oldqueries,NewQ,NewOldQ),
   findqueries(NewQ,NewOldQ,L,Clauses).

find_new_qs_l([Q|Qs],Newqueries,Clauses) :-
   find_new_qs(Q,NQ,Clauses),
   find_new_qs_l(Qs,NQ1,Clauses),
   append(NQ,NQ1,Newqueries).
find_new_qs_l([],[],_).

find_new_qs(query(Query,List),Newqueries,Clauses) :-
   functor(Query,F,A), functor(Head,F,A),
   findall(Queries,
             (member((Head:-Body),Clauses),
              find_new_qs_(query(Query,List),(Head:-Body),
                                              Queries)),
           Qs),
   ord_union(Qs, Newqueries).

find_new_qs_(query(Query,List),(Head1:-Body1),Newqueries) :-
   make_weighted_rule_graph(Head1, Body1, Node_sets1),
   melt_new([Head1,Body1,Node_sets1],
                              [Head,Body,Node_sets]),
   adjust(Head,Query),
   functor(Query,F,_Arity),
   findall(edge(node(F,[0],I),node(F,[0],J)),
           member(eq(I,J),List), Edges0),
   append(Edges,Edges0,EE),
   findall(arc(node(F,[0],I),node(F,[0],J)),
           member(l(J,I),List),Arcs0),
   make_subqueries_list(Body,Body_subgoals),
   makequeries(Query,List,Node_sets,Body_subgoals,
        EE,Arcs0,DA,[],1,Newqueries1),
   sort(Newqueries1,Newqueries).


% adjust(Head,Query) 'blackens' (i.e. substitutes  b  for variables)
% arguments of  Head  for which the respective arguments of  Query  are  b.
adjust(Head,Query) :- functor(Head,_F,A), adjust(Head,Query,1,A).
 
adjust(Head,Query,J,A) :- J =< A, arg(J,Query,'#b'), 
                     arg(J,Head,Arg), size(Arg,ArgSize),
                     blacken_nodes(ArgSize),
                     J1 is J+1, adjust(Head,Query,J1,A).
adjust(Head,Query,J,A) :- J =< A, arg(J,Query,'#f'), 
                     J1 is J+1, adjust(Head,Query,J1,A).
adjust(_Head,_Query,J,A) :- J > A.

% blacken_nodes(Term) substitutes 'b' for all variables in  Term.

blacken_nodes('#b') :- !.
blacken_nodes(T) :- atomic(T),!.
blacken_nodes([H|T]) :- !,  blacken_nodes(H), blacken_nodes(T).
blacken_nodes(Comp) :- \+atomic(Comp),
     Comp =.. [_|Args], blacken_nodes(Args).



% makequeries(Query,List,Node_sets,Body_subgoals,Edges,
% Arcs,DA,Oldqueries,I,Newqueries)

makequeries(_Query,_List,Node_sets,_Body_subgoals,
            _Edges,_Arcs,_DA,Queries,I,Queries) :-
   length(Node_sets,N),I>=N,!.
makequeries(Query,List,Node_sets,Body_subgoals,
            Edges,Arcs,DA,Oldqueries,I,Newqueries) 
:-
   length(Node_sets,N), I < N,
   nth(I,Body_subgoals,G), 
   functor(G,F,Arity),
   flatten(Node_sets,Nodes),
   findall(eq(J,K),
           (member(node(F,[I],J,_,_),Nodes),
            member(node(F,[I],K,_,_),Nodes),J<K,
            once(w_edge(node(F,[I],J),node(F,[I],K),Edges,DA))),
           Eqs0),
   minimize_eq(Eqs0,Eqs),
   findall(l(J,K),
           (member(node(F,[I],J,A1,_),Nodes),
            member(node(F,[I],K,A2,_),Nodes),
            i_e_arg(A1),i_e_arg(A2),
            once(w_arc(node(F,[I],K),node(F,[I],J),Edges,Arcs,DA))),
          InEqs0),
   minimize_l(Eqs,InEqs0,InEqs),
   append(Eqs,InEqs,LList),
   sort(LList,List1),
   copy_term(G,G1), put_bf(G1,G2),
   Oldqueries1=[query(G2,List1)|Oldqueries],
   Iplus1 is I+1,
   functor(G,F,Arity),
   functor(Inst,F,Arity),
   '#inst'(Inst),
   put_b(G,Inst),  %inferring instantiation for I'th body subgoal

   makequeries(Query,List,Node_sets,Body_subgoals,
                                   Edges,Arcs,DA,Oldqueries1,
                                   Iplus1,Newqueries).

% make_subqueries_list gets subgoals separated by commas and makes a list
% from them.
make_subqueries_list((B1,B2),Body_subgoals) :- make_subqueries_list(B2,G),
      Body_subgoals = [B1|G].
make_subqueries_list(B,[B]) :- functor(B,F,_), F \== ','.








































