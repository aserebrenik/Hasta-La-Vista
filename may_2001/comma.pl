:- module(comma,[add_true/2,comma_append/3,comma_append1/3,
		 comma_length/2, comma_reverse/2,
		 comma_reverse_/2,drop_true/2]).

drop_true((Q,true),Q) :- !.
drop_true((Q,Qs),(Q,Rs)):-
	drop_true(Qs,Rs).

add_true((Q,Qs),(Q,Rs)):- !,
	add_true(Qs,Rs).
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