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
check(_,L,[],F,S) :-
  member([S,Z],L),
  member(F,Z).
check(_,L,[],neg(F),S) :-
  \+check(_,L,[],F,S).

% And
check(T,L,[],and(F,G),S) :-
  check(T,L,[],F,S),
  check(T,L,[],G,S).

% Or
check(T,L,[],or(F,G),S) :-
  check(T,L,[],F,S);
  check(T,L,[],G,S).

% AX
check(T,L,_,ax(F),S) :-
  member([S,Nodes],T),
	maplist(check(T,L,[],F), Nodes).

% EX
check(T,L,[],ex(F),S) :-
  member([S,Nodes],T),
  member(Node,Nodes),
  check(T,L,[],F,Node).

% AG
check(_,_,U,ag(_),S) :-
  member(S,U).
check(T,L,U,ag(F),S) :-
  \+member(S,U),
  check(T,L,[],F,S),
  member([S,Nodes],T),
	maplist(check(T,L,[S|U],ag(F)),Nodes).

% EG
check(_,_,U,eg(_),S) :-
  member(S,U).
check(T,L,U,eg(F),S) :-
  \+member(S,U),
  check(T,L,[],F,S),
  member([S,Nodes],T),
  member(Node,Nodes),
  check(T,L,[S|U],eg(F),Node).

% EF
check(T,L,U,ef(F),S) :-
  \+member(S,U),
  check(T,L,[],F,S).
check(T,L,U,ef(F),S) :-
  \+member(S,U),
  member([S,Nodes],T),
  member(Node,Nodes),
  check(T,L,[S|U],ef(F),Node).

% AF
check(T,L,U,af(F),S) :-
  \+member(S,U),
    check(T,L,[],F,S).
check(T,L,U,af(F),S) :-
  \+member(S,U),
  member([S,Nodes],T),
	maplist(check(T,L,[S|U],af(F)), Nodes).
