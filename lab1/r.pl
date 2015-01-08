% For sicstus: use_module(library(lists)).  before consulting the file.
r :- run_all_tests(p).
run_all_tests(ProgramToTest) :-
    catch(consult(ProgramToTest),
          B,
          (write('Could not consult \"'), write(ProgramToTest),
           write('\": '), write(B), nl, halt)),
    all_valid_ok(['valid1.txt', 'valid2.txt', 'valid3.txt',
                  'valid4.txt', 'valid5.txt', 'valid6.txt',
                  'valid7.txt', 'valid8.txt', 'valid9.txt',
                  'valid10.txt','valid11.txt','valid12.txt',
                  'valid13.txt','valid14.txt','valid15.txt',
                  'valid16.txt','valid17.txt']),
    all_invalid_ok(['invalid1.txt', 'invalid2.txt', 'invalid3.txt',
                    'invalid4.txt', 'invalid5.txt', 'invalid6.txt',
                    'invalid7.txt', 'invalid8.txt', 'invalid9.txt',
                    'invalid10.txt','invalid11.txt','invalid12.txt',
                    'invalid13.txt','invalid14.txt']),
    halt.



all_valid_ok([]).
all_valid_ok([Test | Remaining]) :-
    write(Test), 
    (verify(Test), write(' passed');
    write(' failed. The proof is valid but your program rejected it!')),
    nl, all_valid_ok(Remaining).

all_invalid_ok([]).
all_invalid_ok([Test | Remaining]) :-
    write(Test), 
    (\+verify(Test), write(' passed');
    write(' failed. The proof is invalid but your program accepted it!')),
    nl, all_invalid_ok(Remaining).
