occur_check([]).
occur_check([clause(Head,Body)|Clauses]) :-
	occur_check(Body), 
	occur_check(Clauses).
occur_check((B1, B2)):-
	occur_check(B1), occur_check(B2).
