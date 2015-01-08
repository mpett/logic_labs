% For SICStus: (needed for member/2)
:- use_module(library(lists)).

% Load model, initial state and formula from file.
verify(Input) :-
   see(Input), read(T), read(L), read(S), read(F), seen,
   check(T, L, S, [], F).

% OBS changed to so maplist works on S
% check(S, T, L, U, F)
%    T - the transitions in form of an adjacency list;
%    L - the labeling function;
%    S - the current state;
%    U - the states recorded so far;
%    F - the CTL Formula to check.
%
% Should evaluate to true iff the sequent below is valid:
%
%    (T,L), S |-  F
%               U

% To execute: consult('your_file.pl'). verify('input.txt').

% Literals
check(_,L,S,[],X) :-
  member([S,Z],L),
  member(X,Z).
% write('Literal check\n')
check(_,L,S,[],neg(X)) :-
  (\+check(_,L,S,[],X)).
% write('Literal check\n')

% And
check(T,L,S,[],and(F,G)) :-
  check(T,L,S,[],F),
  check(T,L,S,[],G).
% write('AND\n')

% Or
check(T,L,S,[],or(F,G)) :-
  check(T,L,S,[],F);
  check(T,L,S,[],G).
% write('OR\n')

% AX
check(T,L,S,_,ax(F)) :-
  member([S,Neighs],T),
  \+((member(Neigh,Neighs),\+(check(T,L,Neigh,[],F)))).
  %check_list(check(T,L,Neigh,[],F), Neighs).
% write('AX\n')

% EX
check(T,L,S,[],ex(F)) :-
  member([S,Neighs],T),
  member(Neigh,Neighs),
  check(T,L,Neigh,[],F).
% write('EX\n')

% AG
check(_,_,S,U,ag(_)) :-
  member(S,U).
% write('AG1\n')
check(T,L,S,U,ag(F)) :-
  (\+member(S,U)),
    check(T,L,S,[],F),
    member([S,Neighs],T),
    \+((member(Neigh,Neighs),
    \+(check(T,L,Neigh,[S|U],ag(F))))).
% write('AG2\n')

% EG
check(_,_,S,U,eg(_)) :-
  member(S,U).
% write('EG1\n')
check(T,L,S,U,eg(F)) :-
  (\+member(S,U)),
    check(T,L,S,[],F),
    member([S,Neighs],T),
    member(Neigh,Neighs),
    check(T,L,Neigh,[S|U],eg(F)).
% write('EG2\n')

% EF
check(T,L,S,U,ef(F)) :-
  (\+member(S,U)),
    check(T,L,S,[],F).
% write('EF1\n')
check(T,L,S,U,ef(F)) :-
  (\+member(S,U)),
    member([S,Neighs],T),
    member(Neigh,Neighs),
    check(T,L,Neigh,[S|U],ef(F)).
% write('EF2\n')

% AF
check(T,L,S,U,af(F)) :-
  (\+member(S,U)),
    check(T,L,S,[],F).
% write('AF1\n')
check(T,L,S,U,af(F)) :-
  \+member(S,U),
  member([S,Neighs],T),
  \+((member(Neigh,Neighs),
  \+check(T,L,Neigh,[S|U],af(F)))).
% write('AF2\n').
