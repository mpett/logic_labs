% For SICStus: (needed for member/2)
:- use_module(library(lists)).

% Load model, initial state and formula from file.
verify(Input) :-
   see(Input), read(T), read(L), read(S), read(F), seen,
   check(T, L, [], F, S).

% OBS changed to so maplist works on S
% check(T, L, U, F, S)
%    T - the transitions in form of an adjacency list;
%    L - the labeling function;
%    U - the states recorded so far;
%    F - the CTL Formula to check.
%    S - the current state;
%
% Should evaluate to true iff the sequent below is valid:
%
%    (T,L), S |-  F
%               U

% To execute: consult('your_file.pl'). verify('input.txt').

% Literals
check(_,L,_,X,S) :-
  member([S,Z],L),
  member(X,Z).
check(_,L,U,neg(X),S) :-
  \+check(_,L,U,X,S).

% And
check(T,L,U,and(F,G),S) :-
  check(T,L,U,F,S),
  check(T,L,U,G,S).

% Or
check(T,L,U,or(F,G),S) :-
  check(T,L,U,F,S);
  check(T,L,U,G,S).

% AX
%check(T,L,U,ax(F),S) :-
%	member(S,U).
check(T,L,U,ax(F),S) :-
	\+member(S,U),
  member([S,Neighs],T),
	maplist(check(T,L,[S|U],F), Neighs).

% EX
%check(T,L,U,ex(F),S) :-
%	member(S,U).
check(T,L,U,ex(F),S) :-
	\+member(S,U),
  %check(T,L,[],F,S),
  member([S,Neighs],T),
  member(Neigh,Neighs),
  check(T,L,[S|U],F,Neigh).

%%%%%%%%%%%%%%% COMPOSITIONS ...

% AG
%check(_,_,U,ag(_),S) :-
%  member(S,U). % kontrollera slinga
check(T,L,U,ag(F),S) :-
  %\+member(S,U), % kontrollera slinga
	check(T,L,U,and(F,ax(ag(F))),S).
	% check(T,L,[],F,S), % kontrollera current
	% member([S,Neighs],T), % kontrollera noder
	% maplist(check(T,L,[S|U],ag(F)), Neighs).

% EG
%check(_,_,U,eg(_),S) :-
%  member(S,U).
check(T,L,U,eg(F),S) :-
  %\+member(S,U), % kontrollera slinga
	check(T,L,U,and(F,ex(eg(F))),S).
  %check(T,L,[],F,S),
  %member([S,Neighs],T),
  %member(Neigh,Neighs),
  %check(T,L,[S|U],eg(F),Neigh).

% EF
%check(T,L,U,ef(F),S) :-
%  \+member(S,U).
  %check(T,L,[],F,S).
check(T,L,U,ef(F),S) :-
  %\+member(S,U), % kontrollera slinga
	check(T,L,U,or(F,ex(ef(F))),S).
  %member([S,Neighs],T),
  %member(Neigh,Neighs),
  %check(T,L,[S|U],ef(F),Neigh).

% AF
%check(T,L,U,af(F),S) :-
%  \+member(S,U).
  %check(T,L,[],F,S).
check(T,L,U,af(F),S) :-
  %\+member(S,U),
	check(T,L,U,or(F,ax(af(F))),S).
  %member([S,Neighs],T),
	%maplist(check(T,L,[S|U],af(F)), Neighs).
