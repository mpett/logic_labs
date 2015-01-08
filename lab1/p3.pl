not(P) :- call(P), !, fail. 
not(P).

is_list(X) :-
        var(X), !,
        fail.
is_list([]).
is_list([_|T]) :-
        is_list(T).
		
last([X],X).
last([H|T],X):- last(T,X).

% ----------------------------------------



verify(InputFileName) :- see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).	

test(N):- prems(N,Prems),proof(N,Proof),goal(N,Goal),
				valid_proof(Prems,_,Proof), valid_goal(Proof,Goal).

prems(1,[imp(p, q), p]).
prems(2,[q]).
prems(3,[imp(p,or(q,r)),p,neg(r)]).
prems(5, [imp(p,q),neg(q)]).
prems(6, [and(imp(p, neg(p)), imp(neg(r), p))]).
prems(11,[and(p, q)]).
prems(15,[]).
/* [
  [1, and(p, q), premise ],
  [2, p, andel1(1)],
  [
    [3, p, assumption]
  ],
  [4, imp(p, p),    impint(3,3)]
].
*/

%invalida
prems(114,[q]).
prems(161,[]).
prems(111,[q, neg(and(p,q))]).


proof(1,[[1, imp(p,q), premise],
  [2, p,premise],
  [3, q,impel(2,1)]]).
  
  
 proof(2,[[1, q, premise],[[2, p, assumption],[3, q, copy(1)]],[4, imp(p,q), impint(2,3)]]).
 proof(3,[
  [1, imp(p,or(q,r)),    premise],
  [2, p,                 premise],
  [3, neg(r),            premise],
  [4, or(q,r),           impel(2,1)],
  [
    [5, neg(q),          assumption],
    [
      [6, q,             assumption],
      [7, cont,          negel(6,5)]
    ],
    [
      [8, r,             assumption],
      [9, cont,          negel(8,3)]
    ],
    [10, cont,           orel(4,6,7,8,9)]
  ],
  [11, q,                pbc(5,10)]
]).

proof(5, [
  [1, imp(p,q),   premise],
  [
    [2, p,        assumption],
    [3, q,        impel(2,1)],
    [4, neg(q),   premise],
    [5, cont,     negel(3,4)]
  ],
  [6, neg(p),     negint(2,5)]
]).

proof(15, [
  [1, or(p, neg(p)), lem]
]).

proof(6,[
  [1, and(imp(p, neg(p)), imp(neg(r), p)), premise],
  [2, imp(p, neg(p)),                      andel1(1)],
  [
    [3, p,                                 assumption],
    [4, neg(p),                            impel(3,2)],
    [5, cont,                              negel(3,4)]
  ],
  [6, neg(p),                              negint(3,5)]
  ]).
  
  proof(11,[
  [1, and(p, q), premise ],
  [2, p, andel1(1)],
  [
    [3, p, assumption]
  ],
  [4, imp(p, p),    impint(3,3)]
]).


%invalida


proof(161, [
  [1, or(p, neg(p)), lem]
]).



proof(114,[]).
%---------

goal(1,q).

goal(2,imp(p,q)).

goal(3,q).
goal(5, neg(p)).
goal(6, neg(p)).
goal(11,imp(p, p)).

goal(15,or(p, neg(p))).

%invalid

goal(114,[]).
goal(161,or(p, neg(q))).
goal(111, neg(p)).
  
  
/*  [q].
imp(p,q).
[
    [1, q,        premise],
    [
      [2, p,      assumption],
      [3, q,      copy(1)]
    ],
    [4, imp(p,q), impint(2,3)]
].*/
	
/*input format: [imp(p, q), p].

q.

[
  [1, imp(p,q), premise],
  [2, p,        premise],
  [3, q,        impel(2,1)]
].*/

valid_proof(Prems, Goal, Proof) :-
	valid_prem(Prems,Proof),
		valid_deduction(Proof),
			valid_goal(Proof,Goal).
			
%dummy for test


valid_goal(Proof,Goal):- last(Proof,Last), Last=[_,Goal,_].
			
%undersöker om alla premiser återfinns i beviset

valid_prem([],Proof).

valid_prem([H|T],Proof):- member([_,H,premise],Proof),valid_prem(T,Proof).
valid_prem([H|T],Proof):- boxmember(Box,Proof), member([_,H,premise],Box),valid_prem(T,Proof).

%valid_prem([H|T],Proof):- member([_,H,premise],Proof).

valid_deduction(Proof):- member([A,B,C],Proof), C\== premise,C\== assumption, valid_deduction(Proof,[],Proof1).

valid_deduction([],Proof,Proof1).
valid_deduction([H|T],Help,Res):- H= [_,_,premise], append(Help,[H],Res1), valid_deduction(T,Res1,Res).
valid_deduction([H|T],Help,Res):- H= [_,_,assumption], append(Help,[H],Res1), valid_deduction(T,Res1,Res).
valid_deduction([H|T],Help,Res):- box(H), valid_deduction(H,Help,NewH), append(Help,[H],Res1), valid_deduction(T,Res1,Res).
valid_deduction([H|T],Help,Res):- H= [Nb,Expr,Lines], rule(Help,H),append(Help,[H],Res1), valid_deduction(T,Res1,Res).
	


% use_module(library(lists)). consult(proofcontr). verify('valid1.txt').
% ----------------------------------------

accessible_box(Ass,Goal,Line,Proof) :-
	find(Ass,Proof, Box),
	last(Box,Goal),
	accessible(Goal,Line,Proof).

accessible([HX|TX], [HL|TL], Proof) :-
	HL > HX,
	find([HX|TX],Proof, XList),
	find([HL|TL],XList, LineList),
	!,
	LineList \== [].

find(_, [], []). 	% Nothing found
find(_,[X,_,_],Return) :-
	not(is_list(X)),
	Return = [].
find(X, Allowed, Return) :-	% Something found
	member(X, Allowed),
	Return = Allowed.
find(X, [H|T], Return) :-	% Continue looking
	find(X, H, Return1),
	find(X, T, Return2),
	append(Return1, Return2, Return).

in_area(_, []) :- false. 	% Nothing found
in_area(_,[_,_,_]) :- false.
in_area(X, Allowed) :-	% Something found
	member(X, Allowed).
in_area(X, [[HH|HT]|T], Return) :-	% Continue looking
	find(X, HH);
	find(X, HT);
	find(X, T).
	

% ----------------------------------------
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
	[_, B, orel(X,Y,U,V,W)] = Line,
	member([X, or(Q, R), _], Proof),
	boxmember(Box,Proof).
	member([Y,Q,assumption],Box),
	member([U,B,_],Box),
	
	boxmember(Box1,Proof),
	member([V,R,assumption],Box1),
	member([W,B,_],Box1).
	
	
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
/* rule(Proof, Line) :-
	[_, neg(A), negint(X, Y)] = Line,
	accessible_box([X, A, assumption], [Y, cont, T], Line, Proof),
	T \== assumption.*/
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
/*rule(Proof, Line) :-
	[_, A, pbc(X, Y)] = Line,
	accessible_box([X, neg(A), assumption], [Y, cont, T], Line, Proof),
	T \== assumption.*/
	
rule(Proof, Line) :-
	[_, A, pbc(X, Y)] = Line,
	boxmember(Box,Proof),
	member([X, neg(A),assumption],Box),
	member([Y,cont,T],Box).
	
	

% lem
rule(Proof, Line) :-
	[_, or(A, neg(A)), lem] = Line.
