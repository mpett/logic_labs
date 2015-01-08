not(P) :- call(P), !, fail. 
not(P).

last([X],X).
last([H|T],X):- last(T,X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

verify(InputFileName) :- see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	valid_prem(Prems,Proof),
	valid_deduction(Proof),
	valid_goal(Proof,Goal).
valid_goal(Proof,Goal):-
	last(Proof,Last),
	Last=[_,Goal,_],
	Last \= [_,_,assumption].
			
valid_prem([],Proof).
valid_prem([H|T],Proof):-
	member([_,H,premise],Proof).

valid_deduction(Proof):-
	valid_deduction(Proof,[],Proof1).
valid_deduction([],Proof,Proof1).
valid_deduction([H|T],Help,Res):-
	H = [_,_,premise],
	append(Help,[H],Res1),
	valid_deduction(T,Res1,Res).
valid_deduction([H|T],Help,Res):-
	H = [_,_,assumption],
	append(Help,[H],Res1),
	valid_deduction(T,Res1,Res).
valid_deduction([H|T],Help,Res):-
	box(H),
	valid_deduction(H,Help,NewH),
	append(Help,[H],Res1),
	valid_deduction(T,Res1,Res).
valid_deduction([H|T],Help,Res):-
	H = [Nb,Expr,Lines],
	rule(Help,H),
	append(Help,[H],Res1),
	valid_deduction(T,Res1,Res).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

box(X):- X = [H|T], H=[A|_].
boxmember(Box,List):- member(Box,List), box(Box).


% copy
rule(Proof, Line) :-
	Line = [_, A, copy(X)], 
	member([X, A, _],Proof).

% andint
rule(Proof, Line) :-
	[_, and(A, B), andint(X, Y)] = Line,
	member([X, A, _], Proof),
	member([Y, B, _], Proof).

% andel1
rule(Proof, Line) :-
	[_, A, andel1(X)] = Line,
	member([X, and(A, _), _], Proof).

% andel2
rule(Proof, Line) :-
	[_, A, andel2(X)] = Line,
	member([X, and(_, A), _], Proof).

% orint1
rule(Proof, Line) :-
	[_, or(A, _), orint1(X)] = Line,
	member([X, A, _],Proof).

% orint2
rule(Proof, Line) :-
	[_, or(_, A), orint1(X)] = Line,
	member([X, A, _], Proof).

% orel
rule(Proof, Line) :-
	[_, cont, orel(X,Y,U,V,W)] = Line,
	member([X, or(Q, R), _], Proof),
	boxmember(Box,Proof).
	member([Y,Q,assumption],Box),
	member([U,cont,T1],Box),
	
	boxmember(Box1,Proof),
	member([V,R,assumption],Box1),
	member([W,cont,T2],Box1).
	
% impint
rule(Proof,Line):-
	[_, imp(A, B), impint(X, Y)] = Line,
	boxmember(Box,Proof),
	member([X, A, assumption],Box),
	member([Y,B,Expr],Box).
	
	
% impel
rule(Proof, Line) :-
	[_, A, impel(X, Y)] = Line,
	member([X, B, _],Proof),
	member([Y, imp(B, A), _],Proof).

% negint
rule(Proof, Line) :-
	[_, neg(A), negint(X, Y)] = Line,
	boxmember(Box,Proof),
	member([X, A, assumption],Box),
	member([Y,cont,T],Box).
	
% negel
rule(Proof, Line) :-
	[_, cont, negel(X, Y)] = Line,
	member([X, A, _],Proof),
	member([Y, neg(A), _],Proof).

% contel
rule(Proof, Line) :-
	[_, A, contel(X)] = Line,
	member([X, cont, _],Proof).

% negnegint
rule(Proof, Line) :-
	[_, neg(neg(A)), negnegint(X)] = Line,
	member([X, A, _],Proof).

% negnegel
rule(Proof, Line) :-
	[_, A, negnegel(X)] = Line,
	member([X, neg(neg(A)), _],Proof).

% mt
rule(Proof, Line) :-
	[_, neg(A), mt(X, Y)] = Line,
	member([X, imp(A, B), _],Proof),
	member([Y, neg(B), _],Proof).

% pbc
rule(Proof, Line) :-
	[_, A, pbc(X, Y)] = Line,
	boxmember(Box,Proof),
	member([X, neg(A),assumption],Box),
	member([Y,cont,T],Box).
	
% lem
rule(Proof, Line) :-
	[_, or(A, neg(A)), lem] = Line.
