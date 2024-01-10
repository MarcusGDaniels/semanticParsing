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
:- import_module unsafe.

:- import_module sentence_vars_inst0.

:- pred expandIO(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),mrs_rel_handle,io,io).
:- mode expandIO(in,in,di,uo) is det.
expandIO(RelMap,RelHandle,!IO) :-
  (if multi_map.contains(RelMap,RelHandle) then
    multi_map.lookup(RelMap,RelHandle,Rels),
    list.foldl(pred({RelHandle0,_,_,Pred}::in,IoIn::di,IoOut::uo) is det :-
      unpackRelation(RelMap,RelHandle0,Pred,IoIn,IoOut),Rels,!IO)
   else
    error("impossible")),
  io.nl(!IO).

:- pred expandArgMap(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                     multi_map(mrs_types, mrs_rel_handle),
	             multi_map(mrs_types, mrs_rel_handle)).
:- mode expandArgMap(in,in,out) is det.
expandArgMap(RelMap,ArgMapIn,ArgMapOut) :-
    list.foldl(pred({RelHandle0,_,_,Pred}::in,ArgMapIn0::in,ArgMapOut0::out) is det :- collectArguments(RelMap,RelHandle0,Pred,ArgMapIn0,ArgMapOut0),
               multi_map.values(RelMap),ArgMapIn,ArgMapOut).

:- pragma promise_pure(collectArguments/5).
:- pred collectArguments(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                         mrs_rel_handle,
			 preds,
                         multi_map(mrs_types, mrs_rel_handle),
			 multi_map(mrs_types, mrs_rel_handle)).
:- mode collectArguments(in,in,in,in,out) is det.
collectArguments(RelMap,RelHandle,Pred,ArgMapIn,ArgMapOut) :-
  if pred_therein_p_dir(_) = Pred then
    solutions(pred(E1::out) is nondet :- therein_p_dir(RelHandle,E1,_), E1L),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),E1L,ArgMapIn,ArgMap0),
    solutions(pred(E2::out) is nondet :- therein_p_dir(RelHandle,_,E2), E2L),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),E2L,ArgMap0,ArgMapOut)
  else if pred_live_v_1(_) = Pred then
    solutions(pred(E::out) is nondet :- live_v_1(RelHandle,E,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(Inst::out) is nondet :- live_v_1(RelHandle,_,Inst), IL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Event),RelHandle),IL,ArgMap0,ArgMapOut)
  else if pred_people_n_of(_) = Pred then
    solutions(pred(Inst::out) is nondet :- people_n_of(RelHandle,Inst,_), InstL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),InstL,ArgMapIn,ArgMap0),
    solutions(pred(Indiv::out) is nondet :- people_n_of(RelHandle,_,Indiv), IndivL),
    list.foldl(pred(Indiv::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_indiv(Indiv),RelHandle),IndivL,ArgMap0,ArgMapOut)
  else if pred_only_a_1(_) = Pred then
    solutions(pred(E::out) is nondet :- only_a_1(RelHandle,E,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(Inst::out) is nondet :- only_a_1(RelHandle,_,Inst), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMap0,ArgMapOut)
  else if pred_kill_v_1(_) = Pred then
    solutions(pred(E::out) is nondet :- kill_v_1(RelHandle,E,_,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(I1::out) is nondet :- kill_v_1(RelHandle,_,I1,_), I1L),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),I1L,ArgMap0,ArgMap1),
    solutions(pred(I2::out) is nondet :- kill_v_1(RelHandle,_,_,I2), I2L),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),I2L,ArgMap1,ArgMapOut)
  else if pred_in_p_loc(_) = Pred then
    solutions(pred(E1::out) is nondet :- in_p_loc(RelHandle,E1,_,_), E1L),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),E1L,ArgMapIn,ArgMap0),
    solutions(pred(E2::out) is nondet :- in_p_loc(RelHandle,_,E2,_), E2L),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),E2L,ArgMap0,ArgMap1),
    solutions(pred(Inst::out) is nondet :- in_p_loc(RelHandle,_,_,Inst), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMap1,ArgMapOut)
  else if pred_and_c_e(_) = Pred then
    solutions(pred(E1::out) is nondet :- and_c_e(RelHandle,E1,_,_), E1L),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),E1L,ArgMapIn,ArgMap0),
    solutions(pred(E2::out) is nondet :- and_c_e(RelHandle,_,E2,_), E2L),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),E2L,ArgMap0,ArgMap1),
    solutions(pred(E3::out) is nondet :- and_c_e(RelHandle,_,_,E3), E3L),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),E3L,ArgMap1,ArgMapOut)
  else if pred_be_v_id(_) = Pred then
    solutions(pred(E::out) is nondet :- be_v_id(RelHandle,E,_,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(I1::out) is nondet :- be_v_id(RelHandle,_,I1,_), I1L),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),I1L,ArgMap0,ArgMap1),
    solutions(pred(I2::out) is nondet :- be_v_id(RelHandle,_,_,I2), I2L),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),I2L,ArgMap1,ArgMapOut)
  else if pred_always_a_1(_) = Pred then
    solutions(pred(Indiv::out) is nondet :- always_a_1(RelHandle,Indiv,_), IL),
    list.foldl(pred(Indiv::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_indiv(Indiv),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(Event::out) is nondet :- always_a_1(RelHandle,_,Event), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMap0,ArgMapOut)
  else if pred_hate_v_1(_) = Pred then
    solutions(pred(Event::out) is nondet :- hate_v_1(RelHandle,Event,_,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(I1::out) is nondet :- hate_v_1(RelHandle,_,I1,_), I1L),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),I1L,ArgMap0,ArgMap1),
    solutions(pred(I2::out) is nondet :- hate_v_1(RelHandle,_,_,I2), I2L),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),I2L,ArgMap1,ArgMapOut)
  else if pred_never_a_1(_) = Pred then
    solutions(pred(Indiv::out) is nondet :- never_a_1(RelHandle,Indiv,_), IL),
    list.foldl(pred(Indiv::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_indiv(Indiv),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(RH::out) is nondet :- never_a_1(RelHandle,_,RH), RHL),
    list.foldl(pred(RH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rel_handle(RH),RelHandle),RHL,ArgMap0,ArgMapOut)
  else if pred_neg(_) = Pred then
    solutions(pred(Event::out) is nondet :- neg(RelHandle,Event,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(RH::out) is nondet :- neg(RelHandle,_,RH), RHL),
    list.foldl(pred(RH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rel_handle(RH),RelHandle),RHL,ArgMap0,ArgMapOut)
  else if pred_colon_p_namely(_) = Pred then
    solutions(pred(Event::out) is nondet :- colon_p_namely(RelHandle,Event,_,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(RH::out) is nondet :- colon_p_namely(RelHandle,_,RH,_), RH1L),
    list.foldl(pred(RH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rel_handle(RH),RelHandle),RH1L,ArgMap0,ArgMap1),
    solutions(pred(RH::out) is nondet :- colon_p_namely(RelHandle,_,_,RH), RH2L),
    list.foldl(pred(RH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rel_handle(RH),RelHandle),RH2L,ArgMap1,ArgMapOut)
  else if pred_proper_q(_) = Pred then
    solutions(pred(Inst::out) is nondet :- proper_q(RelHandle,Inst,_,_), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(RstrHandle::out) is nondet :- proper_q(RelHandle,_,RstrHandle,_), RSHL),
    list.foldl(pred(RSH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rstr_handle(RSH),RelHandle),RSHL,ArgMap0,ArgMap1),
    solutions(pred(BodyHandle::out) is nondet :- proper_q(RelHandle,_,_,BodyHandle), BHL),
    list.foldl(pred(BH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_body_handle(BH),RelHandle),BHL,ArgMap1,ArgMapOut)
  else if pred_compound(_) = Pred then
    solutions(pred(Event::out) is nondet :- compound(RelHandle,Event,_,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(Inst::out) is nondet :- compound(RelHandle,_,Inst,_), IL1),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL1,ArgMap0,ArgMap1),
    solutions(pred(Inst::out) is nondet :- compound(RelHandle,_,_,Inst), IL2),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL2,ArgMap1,ArgMapOut)
  else if pred_named(_) = Pred then
    solutions(pred(Inst::out) is nondet :- named(RelHandle,Inst,_), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(Carg::out) is nondet :- named(RelHandle,_,Carg), CargL),
    list.foldl(pred(Carg::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_carg(Carg),RelHandle),CargL,ArgMap0,ArgMapOut)
  else if pred_person(_) = Pred then
    solutions(pred(Inst::out) is nondet :- person(RelHandle,Inst), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMapOut)
  else if pred_some_q(_) = Pred then
    solutions(pred(Inst::out) is nondet :- some_q(RelHandle,Inst,_,_), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(RstrHandle::out) is nondet :- some_q(RelHandle,_,RstrHandle,_), RSHL),
    list.foldl(pred(RSH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rstr_handle(RSH),RelHandle),RSHL,ArgMap0,ArgMap1),
    solutions(pred(BodyHandle::out) is nondet :- some_q(RelHandle,_,_,BodyHandle), BHL),
    list.foldl(pred(BH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_body_handle(BH),RelHandle),BHL,ArgMap1,ArgMapOut)
  else if pred_udef_q(_) = Pred then
    solutions(pred(Inst::out) is nondet :- udef_q(RelHandle,Inst,_,_), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(RstrHandle::out) is nondet :- udef_q(RelHandle,_,RstrHandle,_), RSHL),
    list.foldl(pred(RSH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rstr_handle(RSH),RelHandle),RSHL,ArgMap0,ArgMap1),
    solutions(pred(BodyHandle::out) is nondet :- udef_q(RelHandle,_,_,BodyHandle), BHL),
    list.foldl(pred(BH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_body_handle(BH),RelHandle),BHL,ArgMap1,ArgMapOut)
  else if pred_and_c_x(_) = Pred then
    solutions(pred(Inst::out) is nondet :- and_c_x(RelHandle,Inst,_,_), IL0),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL0,ArgMapIn,ArgMap0),
    solutions(pred(Inst::out) is nondet :- and_c_x(RelHandle,_,Inst,_), IL1),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL1,ArgMap0,ArgMap1),
    solutions(pred(Inst::out) is nondet :- and_c_x(RelHandle,_,_,Inst), IL2),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL2,ArgMap1,ArgMapOut)
  else if pred_implicit_conj(_) = Pred then
    solutions(pred(Inst::out) is nondet :- implicit_conj(RelHandle,Inst,_,_), IL0),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL0,ArgMapIn,ArgMap0),
    solutions(pred(Inst::out) is nondet :- implicit_conj(RelHandle,_,Inst,_), IL1),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL1,ArgMap0,ArgMap1),
    solutions(pred(Inst::out) is nondet :- implicit_conj(RelHandle,_,_,Inst), IL2),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL2,ArgMap1,ArgMapOut)
  else if pred_the_q(_) = Pred then
    solutions(pred(Inst::out) is nondet :- the_q(RelHandle,Inst,_,_), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(RstrHandle::out) is nondet :- the_q(RelHandle,_,RstrHandle,_), RSHL),
    list.foldl(pred(RSH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rstr_handle(RSH),RelHandle),RSHL,ArgMap0,ArgMap1),
    solutions(pred(BodyHandle::out) is nondet :- the_q(RelHandle,_,_,BodyHandle), BHL),
    list.foldl(pred(BH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_body_handle(BH),RelHandle),BHL,ArgMap1,ArgMapOut)
  else if pred_butler_n_1(_) = Pred then
    solutions(pred(Inst::out) is nondet :- butler_n_1(RelHandle,Inst), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMapOut)
  else if pred_def_explicit_q(_) = Pred then
    solutions(pred(Inst::out) is nondet :- def_explicit_q(RelHandle,Inst,_,_), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(RstrHandle::out) is nondet :- def_explicit_q(RelHandle,_,RstrHandle,_), RSHL),
    list.foldl(pred(RSH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rstr_handle(RSH),RelHandle),RSHL,ArgMap0,ArgMap1),
    solutions(pred(BodyHandle::out) is nondet :- def_explicit_q(RelHandle,_,_,BodyHandle), BHL),
    list.foldl(pred(BH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_body_handle(BH),RelHandle),BHL,ArgMap1,ArgMapOut)
  else if pred_poss(_) = Pred then
    solutions(pred(Event::out) is nondet :- poss(RelHandle,Event,_,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(Inst::out) is nondet :- poss(RelHandle,_,Inst,_), IL0),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL0,ArgMap0,ArgMap1),
    solutions(pred(Inst::out) is nondet :- poss(RelHandle,_,_,Inst), IL1),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL1,ArgMap1,ArgMapOut)
  else if pred_victim_n_of(_) = Pred then
    solutions(pred(Inst::out) is nondet :- victim_n_of(RelHandle,Inst,_), InstL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),InstL,ArgMapIn,ArgMap0),
    solutions(pred(Indiv::out) is nondet :- victim_n_of(RelHandle,_,Indiv), IndivL),
    list.foldl(pred(Indiv::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_indiv(Indiv),RelHandle),IndivL,ArgMap0,ArgMapOut)
  else if pred_pronoun_q(_) = Pred then
    solutions(pred(Inst::out) is nondet :- pronoun_q(RelHandle,Inst,_,_), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(RstrHandle::out) is nondet :- pronoun_q(RelHandle,_,RstrHandle,_), RSHL),
    list.foldl(pred(RSH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rstr_handle(RSH),RelHandle),RSHL,ArgMap0,ArgMap1),
    solutions(pred(BodyHandle::out) is nondet :- pronoun_q(RelHandle,_,_,BodyHandle), BHL),
    list.foldl(pred(BH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_body_handle(BH),RelHandle),BHL,ArgMap1,ArgMapOut)
  else if pred_pron(_) = Pred then
    solutions(pred(Inst::out) is nondet :- pron(RelHandle,Inst), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMapOut)
  else if pred_rich_a_in(_) = Pred then
    solutions(pred(Event::out) is nondet :- rich_a_in(RelHandle,Event,_,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(Inst::out) is nondet :- rich_a_in(RelHandle,_,Inst,_), InstL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),InstL,ArgMap0,ArgMap1),
    solutions(pred(Inst::out) is nondet :- rich_a_in(RelHandle,_,_,Inst), IndivL),
    list.foldl(pred(Indiv::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_indiv(Indiv),RelHandle),IndivL,ArgMap1,ArgMapOut)
  else if pred_more_comp(_) = Pred then
    solutions(pred(Event::out) is nondet :- more_comp(RelHandle,Event,_,_), EL0),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL0,ArgMapIn,ArgMap0),
    solutions(pred(Event::out) is nondet :- more_comp(RelHandle,_,Event,_), EL1),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL1,ArgMap0,ArgMap1),
    solutions(pred(Inst::out) is nondet :- more_comp(RelHandle,_,_,Inst), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMap1,ArgMapOut)
  else if pred_a_q(_) = Pred then
    solutions(pred(Inst::out) is nondet :- a_q(RelHandle,Inst,_,_), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(RstrHandle::out) is nondet :- a_q(RelHandle,_,RstrHandle,_), RSHL),
    list.foldl(pred(RSH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rstr_handle(RSH),RelHandle),RSHL,ArgMap0,ArgMap1),
    solutions(pred(BodyHandle::out) is nondet :- a_q(RelHandle,_,_,BodyHandle), BHL),
    list.foldl(pred(BH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_body_handle(BH),RelHandle),BHL,ArgMap1,ArgMapOut)
  else if pred_killer_n_1(_) = Pred then
    solutions(pred(Inst::out) is nondet :- killer_n_1(RelHandle,Inst), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMapOut)
  else if pred_no_q(_) = Pred then
    solutions(pred(Inst::out) is nondet :- no_q(RelHandle,Inst,_,_), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(RstrHandle::out) is nondet :- no_q(RelHandle,_,RstrHandle,_), RSHL),
    list.foldl(pred(RSH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rstr_handle(RSH),RelHandle),RSHL,ArgMap0,ArgMap1),
    solutions(pred(BodyHandle::out) is nondet :- no_q(RelHandle,_,_,BodyHandle), BHL),
    list.foldl(pred(BH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_body_handle(BH),RelHandle),BHL,ArgMap1,ArgMapOut)
  else if pred_generic_entity(_) = Pred then
    solutions(pred(Inst::out) is nondet :- generic_entity(RelHandle,Inst), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMapOut)
  else if pred_card(_) = Pred then
    solutions(pred(Event::out) is nondet :- card(RelHandle,Event,_,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(Inst::out) is nondet :- card(RelHandle,_,Inst,_), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMap0,ArgMap1),
    solutions(pred(Carg::out) is nondet :- card(RelHandle,_,_,Carg), CargL),
    list.foldl(pred(Carg::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_carg(Carg),RelHandle),CargL,ArgMap1,ArgMapOut)
  else if pred_aunt_n_of(_) = Pred then
    solutions(pred(Inst::out) is nondet :- aunt_n_of(RelHandle,Inst,_), InstL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),InstL,ArgMapIn,ArgMap0),
    solutions(pred(Indiv::out) is nondet :- aunt_n_of(RelHandle,_,Indiv), IndivL),
    list.foldl(pred(Indiv::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_indiv(Indiv),RelHandle),IndivL,ArgMap0,ArgMapOut)
  else if pred_every_q(_) = Pred then
    solutions(pred(Inst::out) is nondet :- every_q(RelHandle,Inst,_,_), IL),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL,ArgMapIn,ArgMap0),
    solutions(pred(RstrHandle::out) is nondet :- every_q(RelHandle,_,RstrHandle,_), RSHL),
    list.foldl(pred(RSH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rstr_handle(RSH),RelHandle),RSHL,ArgMap0,ArgMap1),
    solutions(pred(BodyHandle::out) is nondet :- every_q(RelHandle,_,_,BodyHandle), BHL),
    list.foldl(pred(BH::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_body_handle(BH),RelHandle),BHL,ArgMap1,ArgMapOut)
  else if pred_therefore_a_1(_) = Pred then
    solutions(pred(Indiv::out) is nondet :- therefore_a_1(RelHandle,Indiv,_), IndivL),
    list.foldl(pred(Indiv::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_indiv(Indiv),RelHandle),IndivL,ArgMapIn,ArgMap0),
    solutions(pred(RelHandle0::out) is nondet :- therefore_a_1(RelHandle,_,RelHandle0), RHL),
    list.foldl(pred(RelHandle0::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_rel_handle(RelHandle0),RelHandle),RHL,ArgMap0,ArgMapOut)
  else if pred_except_p(_) = Pred then
    solutions(pred(Event::out) is nondet :- except_p(RelHandle,Event,_,_), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMapIn,ArgMap0),
    solutions(pred(Inst::out) is nondet :- except_p(RelHandle,_,Inst,_), IL0),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL0,ArgMap0,ArgMap1),
    solutions(pred(Inst::out) is nondet :- except_p(RelHandle,_,_,Inst), IL1),
    list.foldl(pred(Inst::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_inst(Inst),RelHandle),IL1,ArgMap1,ArgMapOut)
  else if pred_unknown(_) = Pred then
    solutions(pred(Unknown::out) is nondet :- unknown(RelHandle,Unknown,_), UL),
    list.foldl(pred(Unknown::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_unknown(Unknown),RelHandle),UL,ArgMapIn,ArgMap0),
    solutions(pred(Event::out) is nondet :- unknown(RelHandle,_,Event), EL),
    list.foldl(pred(Event::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,wrap_event(Event),RelHandle),EL,ArgMap0,ArgMapOut)
  else
    impure unsafe_perform_io(print(Pred)),
    error("unknown predicate").

:- pred unpackRelation(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),mrs_rel_handle,preds,io,io).
:- mode unpackRelation(in,in,in,di,uo) is det.
unpackRelation(RelMap,RelHandle,Pred,IoIn,IoOut) :-
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
       (never_a_1(RelHandle,_,RH),
        multi_map.lookup(RelMap,RH,Refs),
        Ret = list.map(func({RelHandle0,_,_,Preds}) = Val is det :- Val = {RelHandle0,Preds}, Refs)),
       HL),
    io.print({IL,HL},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_neg(_) = Pred then
    io.print("neg(",IoIn,Io0),
    solutions(pred(Event::out) is nondet :- neg(RelHandle,Event,_), EL),
    solutions(pred(Ret::out) is nondet :-
       (neg(RelHandle,_,RH),
        multi_map.lookup(RelMap,RH,Refs),
        Ret = list.map(func({RelHandle0,_,_,Preds}) = Val is det :- Val = {RelHandle0,Preds}, Refs)),
       HL),
    io.print({EL,HL},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else if pred_colon_p_namely(_) = Pred then
    io.print("colon_p_namely(",IoIn,Io0),
    solutions(pred(Event::out) is nondet :- colon_p_namely(RelHandle,Event,_,_), EL),
    solutions(pred(Ret::out) is nondet :-
       (colon_p_namely(RelHandle,_,RH1,_),
        multi_map.lookup(RelMap,RH1,Refs),
        Ret = list.map(func({RelHandle0,_,_,Preds}) = Val is det :- Val = {RelHandle0,Preds}, Refs)),
       H1L),
    solutions(pred(Ret::out) is nondet :-
       (colon_p_namely(RelHandle,_,_,RH2),
        multi_map.lookup(RelMap,RH2,Refs),
        Ret = list.map(func({RelHandle0,_,_,Preds}) = Val is det :- Val = {RelHandle0,Preds}, Refs)),
       H2L),
    io.print({EL,H1L,H2L},Io0,Io1),
    io.print(")",Io1,Io2),
    io.nl(Io2,IoOut)
  else	
    io.print(Pred,IoIn,IoOut),
    error("unknown predicate").

:- pred processSentence(mrs_psoa_post,
                        multi_map(mrs_types, mrs_rel_handle),
			multi_map(mrs_types, mrs_rel_handle)).
:- mode processSentence(in,in,out) is det.
processSentence(Sentence,ArgMapIn,ArgMapOut) :-
  psoa_post(TopHandle,Event,RelMap) = Sentence,
  expandArgMap(RelMap,ArgMapIn,ArgMapOut).

main(!IO) :-
  list.foldl(processSentence,sentences.sentences,multi_map.init,ArgMap),
  io.print(ArgMap,!IO).
