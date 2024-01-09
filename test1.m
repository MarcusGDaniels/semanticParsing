:- module test1.
:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module mrs.
:- import_module sentence0.
:- import_module sentence_vars_event0.
:- import_module sentence_vars_handle0.
:- import_module sentence_vars_inst0.
:- import_module sentence_accessors.

:- import_module solutions.
:- import_module list.
:- import_module multi_map.
:- import_module pair.

main(!IO) :-
  L = solutions(pred(Rstr::out) is nondet :- proper_q(_,_,Rstr,_)),
  mrs_rstr_handle(H0) = list.det_head(list.det_tail(L)),
  io.print(H0,!IO),
  {RelHandle,_,_,P} = det_head(multi_map.lookup(handleMap,mrs_rel_handle(H0))),
  (if pred_named(P0) = P then
     solutions(pred(C::out) is nondet :- named(RelHandle,I,C),L2),
     io.print(det_head(L2),!IO)
  else
    io.print("mismatch",!IO)),
  io.nl(!IO). 
