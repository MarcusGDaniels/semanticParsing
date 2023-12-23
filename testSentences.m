:- module testSentences.
:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module mrs.
:- import_module calls.
:- import_module list.

:- import_module solutions.

main(!IO) :-
  solutions(pred(E::out) is nondet :- kill_v_1(RelHandle,E,A,B),L2),
  io.print(to_string(det_head(L2)),!IO),
  io.print(to_string(det_head(det_tail(L2))),!IO),
  io.nl(!IO). 
