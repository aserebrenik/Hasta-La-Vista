:- module(comma,[add_true/2,comma_append/3,comma_append1/3,
		 comma_eliminate_redundancy/2,
		 comma_length/2, comma_member/2, comma_reverse/2,
		 comma_reverse_/2,drop_true/2,
		 has_true/1, remove_trues/2]).

drop_true((Q,true),Q) :- !.
drop_true((Q,Qs),(Q,Rs)):-
	drop_true(Qs,Rs).

has_true((_Q,Qs)):- has_true(Qs).
has_true(true).

remove_trues(true, true).
remove_trues((true,Q2), Q3):-
	!, remove_trues(Q2,Q3).
remove_trues((Q1,Q2), (Q1,Q3)):-
	remove_trues(Q2,Q3).

% adds true, if the list does not have true already
add_true((Q,Qs),(Q,Rs)):- !,
	add_true(Qs,Rs).
add_true(true, true) :- !.
add_true(Q,(Q,true)).

comma_length(true,0):-!.
comma_length((_,B2),L) :- !,
	comma_length(B2,L1), L is L1+1.
comma_length(_B,1).

%% adds true at the end
comma_reverse_(Qs,Rs):-
	comma_reverse_(Qs,true,Rs).
comma_reverse_((Q,Qs),Acc,Rs):-
	!, comma_reverse_(Qs,(Q,Acc),Rs).
comma_reverse_(true,Acc,Acc).
comma_reverse_(Q,Acc,(Q,Acc)).

%% does not add true at the end
comma_reverse((Q,Qs),Rs):- !,
	comma_reverse_(Qs,Q,Rs).
comma_reverse(Q,Q).

comma_append(true,L,L).
comma_append((B1,B2),B,(B1,B3)):-
	comma_append(B2,B,B3).

comma_append1(L1,L2,L3):-
	add_true(L1,L11),
	comma_append(L11,L2,L31),
	drop_true(L31,L3).

comma_eliminate_redundancy(S1, S2) :-
	comma_eliminate_redundancy(S1, true, S2).
comma_eliminate_redundancy(true, _, true).
comma_eliminate_redundancy((B1,B2), Visited, B3):-
	comma_member(B1, Visited),!,
	comma_eliminate_redundancy(B2, Visited, B3).
comma_eliminate_redundancy((B=B,B2), Visited, B3):-
	!, comma_eliminate_redundancy(B2, Visited, B3).
comma_eliminate_redundancy((B1,B2), Visited, (B1,B3)):-
	comma_eliminate_redundancy(B2, (B1, Visited), B3).

comma_member(B,B):-!.
comma_member(B, (B,_)) :- !.
comma_member(B1, (_,B2)) :- 
	comma_member(B1, B2).



