:- module testSentences.
:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module mrs.
:- import_module calls.
:- import_module list.
:- import_module multi_map.
:- import_module sentences.
:- import_module sentence_predicates.
:- import_module sentence_types.

:- import_module solutions.

:- func collectRelations(mrs_rel_handle) = list(preds).
collectRelations(RelHandle) = L :-
  list.foldl(pred(psoa_post(_,_,MM)::in,LIn::in,LOut::out) is det :- 
    ((if multi_map.contains(MM,RelHandle) then
        LL = multi_map.lookup(MM,RelHandle)
      else
        LL = []),
     Preds = list.map(func({_,_,_,Pred}) = Ret :- Ret = Pred,LL),
     LOut = LIn ++ Preds),
    sentences.sentences, [], L).

:- pred unpackRelation(mrs_rel_handle,preds,io,io).
:- mode unpackRelation(in,in,di,uo) is det.
unpackRelation(RelHandle,Pred,IoIn,IoOut) :-
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
  else
    io.print("unknown predicate",IoIn,IoOut).
		   

main(!IO) :-
  solutions(pred(RelHandle::out) is nondet :- only_a_1(RelHandle,_,_), Handles),
  list.foldl(pred(RelHandle::in,IoIn::di,IoOut::uo) is det :- 
    (Preds = collectRelations(RelHandle),
     list.foldl(unpackRelation(RelHandle), Preds, IoIn, IoOut)),
    Handles, !IO).
