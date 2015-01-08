use_module(library(lists)).


not(P) :- call(P), !, fail. 
not(P).

% ----------------------------------------

verify(InputFileName) :- see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).	

valid_proof(Prems, Goal, Proof) :-
	seq_verifier(Proof, Proof).
	
prem_check(_,_,0) :-
	false.
prem_check(Premis, [ProofH|_], N) :-
	[_,Premis, premise] = ProofH, true.
prem_check(Premis, [_|ProofT], N) :-
	prem_check(Premis, ProofT, (N-1)).

prems_check([], _, _) :-
	true.
prems_check([HPrems|TPrems], Proof, N) :-
	prem_check(HPrems, Proof, N),
	prems_check(TPrems, Proof, N).

goal_check(Goal, Proof) :-
	last([_,Goal,T], Proof),
	T \== assumption.

seq_verifier(_, []) :- true.
seq_verifier(Proof, [[HH|HT]|T]) :-
	not(is_list(HH)),
	rule(Proof, [HH|HT]),
	seq_verifier(Proof, T).
seq_verifier(Proof, [[HH|HT]|T]) :-
	is_list(HH),
	seq_verifier(Proof, HH),
	seq_verifier(Proof, HT).


% use_module(library(lists)). consult(proofcontr). verify('valid1.txt').
% ----------------------------------------

accessible_box(Ass,Goal,Line,Proof) :-
	find(Ass,Proof, Box),
	last(Goal, Box),
	accessible(Ass,Line,Proof).

accessible([HX|TX], [HL|TL], Proof) :-
	HL > HX,
	find([HX|TX],Proof, XList),
	find([HL|TL],XList, LineList).
find(_, [], _) :- false.	% Nothing found

find(X, Allowed, Return) :-	% Something found
	member(X, Allowed),
	Return = Allowed.
find(X, [H|_], Return) :-	% Continue looking
	not(member(X, Allowed)),	
	find(X, H, Return).
find(X, [_|T], Return) :-
	not(member(X,Allowed)),
	find(X, T, Return).

% ----------------------------------------

% premise
rule(_, Line) :-
	[_, A, premise] = Line.

% assumption
rule(_, Line) :-
	[_, A, assumption] = Line.

% copy
rule(Proof, Line) :-
	[_, A, copy(X)] = Line,
	accessible([X, A, _], Line, Proof).

% andint
rule(Proof, Line) :-
	[_, and(A, B), andint(X, Y)] = Line,
	accessible([X, A, _], Line, Proof),
	accessible([Y, B, _], Line, Proof).

% andel1
rule(Proof, Line) :-
	[_, A, andel1(X)] = Line,
	accessible([X, and(A, _), _], Line, Proof).

% andel2
rule(Proof, Line) :-
	[_, A, andel2(X)] = Line,
	accessible([X, and(_, A), _], Line, Proof).

% orint1
rule(Proof, Line) :-
	[_, or(A, _), orint1(X)] = Line,
	accessible([X, A, _], Line, Proof).

% orint2
rule(Proof, Line) :-
	[_, or(_, A), orint1(X)] = Line,
	accessible([X, A, _], Line, Proof).

% orel
rule(Proof, Line) :-
	[_, A, orel(x,y,u,v,w)] = Line,
	accessible([x, or(y, v), _], Line, Proof),
	accessible_box([_,y,assumption],[_,u,T1], Line, Proof),
	T1 \== assumption,
	accessible_box([_,v,assumption],[_,w,T2], Line, Proof),
	T2 \== assumption.

% impint
rule(Proof, Line) :-
	[_, imp(A, B), impint(X, Y)] = Line,
	accessible_box([X, A, assumption], [Y, B, T], Line, Proof),
	T \== assumption.
% impel
rule(Proof, Line) :-
	[_, A, impel(X, Y)] = Line,
	accessible([X, B, _], Line, Proof),
	accessible([Y, imp(B, A), _], Line, Proof).

% negint
rule(Proof, Line) :-
	[_, neg(A), negint(X, Y)] = Line,
	accessible_box([X, A, assumption], [Y, cont, T], Line, Proof),
	T \== assumption.

% negel
rule(Proof, Line) :-
	[_, cont, negel(X, Y)] = Line,
	accessible([X, A, _], Line, Proof),
	accessible([Y, neg(A), _], Line, Proof).

% contel
rule(Proof, Line) :-
	[_, A, contel(X)] = Line,
	accessible([X, cont, _], Line, Proof).

% negnegint
rule(Proof, Line) :-
	[_, neg(neg(A)), negnegint(X)] = Line,
	accessible([X, A, _], Line, Proof).

% negnegel
rule(Proof, Line) :-
	[_, A, negnegel(X)] = Line,
	accessible([X, neg(neg(A)), _], Line, Proof).

% mt
rule(Proof, Line) :-
	[_, neg(A), mt(X, Y)] = Line,
	accessible([X, imp(A, B), _], Line, Proof),
	accessible([Y, neg(B), _], Line, Proof).

% pbc
rule(Proof, Line) :-
	[_, A, pbc(X, Y)] = Line,
	accessible_box([X, neg(A), assumption], [Y, cont, T], Line, Proof),
	T \== assumption.

% lem
rule(_, Line) :-
	[_, or(A, neg(A)), lem] = Line.
