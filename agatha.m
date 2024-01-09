:- module agatha.
:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module sentence_predicates.
:- import_module sentences.
:- import_module sentence_types.
:- import_module mrs.
:- import_module calls.

:- import_module solutions.
:- import_module list.
:- import_module multi_map.
:- import_module pair.
:- import_module require.

:- pred unpackRelation(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),mrs_rel_handle,preds,io,io).
:- mode unpackRelation(in,in,in,di,uo) is det.
unpackRelation(MM,RelHandle,Pred,IoIn,IoOut) :-
  if pred_therein_p_dir(_) = Pred then
    io.print("therein_p_dir(",IoIn,Io0),
    solutions(pred(E1::out) is nondet :- therein_p_dir(RelHandle,E1,_), E1L),
    solutions(pred(E2::out) is nondet :- therein_p_dir(RelHandle,_,E2), E2L),
    io.print({E1L,E2L},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_live_v_1(_) = Pred then
    io.print("live_v_1(",IoIn,Io0),
    solutions(pred(E::out) is nondet :- live_v_1(RelHandle,E,_), EL),
    solutions(pred(Inst::out) is nondet :- live_v_1(RelHandle,_,Inst), IL),
    io.print({EL,IL},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_people_n_of(_) = Pred then
    io.print("people_n_of",IoIn,Io0),
    solutions(pred(Inst::out) is nondet :- people_n_of(RelHandle,Inst,_), InstL),
    solutions(pred(Indiv::out) is nondet :- people_n_of(RelHandle,_,Indiv), IndivL),
    io.print({InstL,IndivL},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_only_a_1(_) = Pred then
    io.print("only_a_1",IoIn,Io0),
    solutions(pred(E::out) is nondet :- only_a_1(RelHandle,E,_), EL),
    solutions(pred(Inst::out) is nondet :- only_a_1(RelHandle,_,Inst), IL),
    io.print({EL,IL},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_kill_v_1(_) = Pred then
    io.print("kill_v_1",IoIn,Io0),
    solutions(pred(E::out) is nondet :- kill_v_1(RelHandle,E,_,_), EL),
    solutions(pred(I1::out) is nondet :- kill_v_1(RelHandle,_,I1,_), I1L),
    solutions(pred(I2::out) is nondet :- kill_v_1(RelHandle,_,_,I2), I2L),
    io.print({EL,I1L,I2L},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_in_p_loc(_) = Pred then
    io.print("in_p_loc(",IoIn,Io0),
    solutions(pred(E1::out) is nondet :- in_p_loc(RelHandle,E1,_,_), E1L),
    solutions(pred(E2::out) is nondet :- in_p_loc(RelHandle,_,E2,_), E2L),
    solutions(pred(Inst::out) is nondet :- in_p_loc(RelHandle,_,_,Inst), IL),
    io.print({E1L,E2L,IL},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_and_c_e(_) = Pred then
    io.print("and_c_e(",IoIn,Io0),
    solutions(pred(E1::out) is nondet :- and_c_e(RelHandle,E1,_,_), E1L),
    solutions(pred(E2::out) is nondet :- and_c_e(RelHandle,_,E2,_), E2L),
    solutions(pred(E3::out) is nondet :- and_c_e(RelHandle,_,_,E3), E3L),
    io.print({E1L,E2L,E3L},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_be_v_id(_) = Pred then
    io.print("be_v_id(",IoIn,Io0),
    solutions(pred(E::out) is nondet :- be_v_id(RelHandle,E,_,_), EL),
    solutions(pred(I1::out) is nondet :- be_v_id(RelHandle,_,I1,_), I1L),
    solutions(pred(I2::out) is nondet :- be_v_id(RelHandle,_,_,I2), I2L),
    io.print({EL,I1L,I2L},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_always_a_1(_) = Pred then
    io.print("always_a_1(",IoIn,Io0),
    solutions(pred(Indiv::out) is nondet :- always_a_1(RelHandle,Indiv,_), IL),
    solutions(pred(Event::out) is nondet :- always_a_1(RelHandle,_,Event), EL),
    io.print({IL,EL},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_hate_v_1(_) = Pred then
    io.print("hate_v_1(",IoIn,Io0),
    solutions(pred(Event::out) is nondet :- hate_v_1(RelHandle,Event,_,_), EL),
    solutions(pred(I1::out) is nondet :- hate_v_1(RelHandle,_,I1,_), I1L),
    solutions(pred(I2::out) is nondet :- hate_v_1(RelHandle,_,I2,_), I2L),
    io.print({EL,I1L,I2L},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_never_a_1(_) = Pred then
    io.print("never_a_1(",IoIn,Io0),
    solutions(pred(Indiv::out) is nondet :- never_a_1(RelHandle,Indiv,_), IL),
    solutions(pred(Ret::out) is nondet :-
       (never_a_1(RelHandle,_,H),
        multi_map.lookup(MM,mrs_rel_handle(H),Refs),
        Ret = list.map(func({RelHandle,_,_,Preds}) = Val is det :- Val = {RelHandle,Preds}, Refs)),
       HL),
    io.print({IL,HL},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_neg(_) = Pred then
    io.print("neg(",IoIn,Io0),
    solutions(pred(Event::out) is nondet :- neg(RelHandle,Event,_), EL),
    solutions(pred(Ret::out) is nondet :-
       (neg(RelHandle,_,H),
        multi_map.lookup(MM,mrs_rel_handle(H),Refs),
        Ret = list.map(func({RelHandle,_,_,Preds}) = Val is det :- Val = {RelHandle,Preds}, Refs)),
       HL),
    io.print({EL,HL},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_colon_p_namely(_) = Pred then
    io.print("colon_p_namely(",IoIn,Io0),
    solutions(pred(Event::out) is nondet :- colon_p_namely(RelHandle,Event,_,_), EL),
    solutions(pred(Ret::out) is nondet :-
       (colon_p_namely(RelHandle,_,H1,_),
        multi_map.lookup(MM,mrs_rel_handle(H1),Refs),
        Ret = list.map(func({RelHandle,_,_,Preds}) = Val is det :- Val = {RelHandle,Preds}, Refs)),
       H1L),
    solutions(pred(Ret::out) is nondet :-
       (colon_p_namely(RelHandle,_,_,H2),
        multi_map.lookup(MM,mrs_rel_handle(H2),Refs),
        Ret = list.map(func({RelHandle,_,_,Preds}) = Val is det :- Val = {RelHandle,Preds}, Refs)),
       H2L),
    io.print({EL,H1L,H2L},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else	
    io.print(Pred,IoIn,IoOut),
    error("unknown predicate").

:- pred processSentence(mrs_psoa_post,io,io).
:- mode processSentence(in,di,uo) is det.
processSentence(Sentence,!IO) :-
  psoa_post(TopHandle,Event,MM) = Sentence,
  RelHandle = mrs_rel_handle(TopHandle),
  (if multi_map.contains(MM,RelHandle) then
    multi_map.lookup(MM,RelHandle,Rels),
    list.foldl(pred({RelHandle,_,_,Pred}::in,IoIn::di,IoOut::uo) is det :-
      unpackRelation(MM,RelHandle,Pred,IoIn,IoOut),Rels,!IO)
   else
    error("impossible")),
  io.nl(!IO).

main(!IO) :-
  list.foldl(processSentence,sentences.sentences,!IO).
