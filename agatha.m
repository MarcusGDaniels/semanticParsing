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
:- import_module string.
:- import_module set.
:- import_module multi_map.
:- import_module pair.
:- import_module require.
:- import_module unsafe.

:- import_module sentence_vars_inst0.

:- pred expandInstances(mrs_rel_handle,
                        multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                        multi_map(mrs_types, mrs_rel_handle),list(mrs_inst),
			set(string),
			set(string)).
:- mode expandInstances(in,in,in,in,in,out).
expandInstances(RelHandle,RelMap,ArgMap,IL,OutputsIn,OutputsOut) :-
  list.foldl(pred(Inst::in,OutputsIn0::in,OutputsOut0::out) is det :- 
    (multi_map.lookup(ArgMap,wrap_inst(Inst),Rels),
     list.foldl(pred(RelHandle0::in,OutputsIn1::in,OutputsOut1::out) is det :- 
       (if RelHandle0 = RelHandle then
         OutputsOut1 = OutputsIn1
        else
          multi_map.lookup(RelMap,RelHandle0,Rels0),
	   list.foldl(pred({RelHandle0Ref,_,_,Pred0}::in,OutputsIn2::in,OutputsOut2::out) is det :- 
                           unpackRelation(RelMap,ArgMap,RelHandle0Ref,Pred0,OutputsIn2,OutputsOut2),
	              Rels0, OutputsIn1, OutputsOut1)),
       Rels,OutputsIn0,OutputsOut0)),IL,OutputsIn,OutputsOut).

:- pred expandEvents(mrs_rel_handle,
                     multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                     multi_map(mrs_types, mrs_rel_handle),list(mrs_event),
                     set(string),
                     set(string)).
:- mode expandEvents(in,in,in,in,in,out).
expandEvents(RelHandle,RelMap,ArgMap,EL,OutputsIn,OutputsOut) :-
  list.foldl(pred(Event::in,OutputsIn0::in,OutputsOut0::out) is det :- 
    (multi_map.lookup(ArgMap,wrap_event(Event),Rels),
     list.foldl(pred(RelHandle0::in,OutputsIn1::in,OutputsOut1::out) is det :- 
       (if RelHandle0 = RelHandle then
         OutputsOut1 = OutputsIn1
        else
          multi_map.lookup(RelMap,RelHandle0,Rels0),
	   list.foldl(pred({RelHandle0Ref,_,_,Pred0}::in,OutputsIn2::in,OutputsOut2::out) is det :- 
                           unpackRelation(RelMap,ArgMap,RelHandle0Ref,Pred0,OutputsIn2,OutputsOut2),
                      Rels0, OutputsIn1, OutputsOut1)),
       Rels,OutputsIn0,OutputsOut0)),EL,OutputsIn,OutputsOut).

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

:- pragma promise_pure(unpackRelation/6).
:- pred unpackRelation(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                       multi_map(mrs_types,mrs_rel_handle),
                       mrs_rel_handle,preds,
		       set(string),set(string)).
:- mode unpackRelation(in,in,in,in,in,out) is det.
unpackRelation(RelMap,ArgMap,RelHandle,Pred,OutputsIn,OutputsOut) :-
  if pred_therein_p_dir(_) = Pred then
    solutions(pred(E1::out) is nondet :- therein_p_dir(RelHandle,E1,_), E1L),
    solutions(pred(E2::out) is nondet :- therein_p_dir(RelHandle,_,E2), E2L),
    E1Str = "{" ++ string.join_list(",",list.map(to_string,E1L)) ++ "}",
    E2Str = "{" ++ string.join_list(",",list.map(to_string,E2L)) ++ "}",
    Cmd = "therein_p_dir(" ++ string.join_list(",",[E1Str,E2Str]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_live_v_1(_) = Pred then
    solutions(pred(E::out) is nondet :- live_v_1(RelHandle,E,_), EL),
    solutions(pred(Inst::out) is nondet :- live_v_1(RelHandle,_,Inst), IL),
    EStr = "{" ++ string.join_list(",",list.map(to_string,EL)) ++ "}",
    IStr = "{" ++ string.join_list(",",list.map(to_string,IL)) ++ "}",
    Cmd = "live_v_1(" ++ string.join_list(",",[EStr,IStr]) ++ ")",
    (if set.member(Cmd,OutputsIn) then
      OutputsOut = OutputsIn
    else
      Outputs0 = set.insert(OutputsIn,Cmd),
      expandEvents(RelHandle,RelMap,ArgMap,EL,Outputs0,Outputs1),
      expandInstances(RelHandle,RelMap,ArgMap,IL,Outputs1,OutputsOut))
  else if pred_people_n_of(_) = Pred then
    solutions(pred(Inst::out) is nondet :- people_n_of(RelHandle,Inst,_), InstL),
    solutions(pred(Indiv::out) is nondet :- people_n_of(RelHandle,_,Indiv), IndivL),
    InstStr = "{" ++ string.join_list(",",list.map(to_string,InstL)) ++ "}",
    IndivStr = "{" ++ string.join_list(",",list.map(to_string,IndivL)) ++ "}",
    Cmd = "people_n_of(" ++ string.join_list(",",[InstStr,IndivStr]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_only_a_1(_) = Pred then
    solutions(pred(E::out) is nondet :- only_a_1(RelHandle,E,_), EL),
    solutions(pred(Inst::out) is nondet :- only_a_1(RelHandle,_,Inst), IL),
    EStr = "{" ++ string.join_list(",",list.map(to_string,EL)) ++ "}",
    IStr = "{" ++ string.join_list(",",list.map(to_string,IL)) ++ "}",
    Cmd = "only_a_1(" ++ string.join_list(",",[EStr,IStr]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_kill_v_1(_) = Pred then
    solutions(pred(E::out) is nondet :- kill_v_1(RelHandle,E,_,_), EL),
    solutions(pred(I1::out) is nondet :- kill_v_1(RelHandle,_,I1,_), I1L),
    solutions(pred(I2::out) is nondet :- kill_v_1(RelHandle,_,_,I2), I2L),
    ELStr = "{" ++ string.join_list(",",list.map(to_string,EL)) ++ "}",
    I1Str = "{" ++ string.join_list(",",list.map(to_string,I1L)) ++ "}",
    I2Str = "{" ++ string.join_list(",",list.map(to_string,I2L)) ++ "}",
    Cmd = "kill_v_1(" ++ string.join_list(",",[ELStr,I1Str,I2Str]) ++ ")",
    (if set.member(Cmd,OutputsIn) then
      OutputsOut = OutputsIn
    else
      Outputs0 = set.insert(OutputsIn,Cmd),
      expandEvents(RelHandle,RelMap,ArgMap,EL,Outputs0,Outputs1),
      expandInstances(RelHandle,RelMap,ArgMap,I1L,Outputs1,Outputs2),
      expandInstances(RelHandle,RelMap,ArgMap,I2L,Outputs2,OutputsOut))
  else if pred_in_p_loc(_) = Pred then
    solutions(pred(E1::out) is nondet :- in_p_loc(RelHandle,E1,_,_), E1L),
    solutions(pred(E2::out) is nondet :- in_p_loc(RelHandle,_,E2,_), E2L),
    solutions(pred(Inst::out) is nondet :- in_p_loc(RelHandle,_,_,Inst), IL),
    E1Str = "{" ++ string.join_list(",",list.map(to_string,E1L)) ++ "}",
    E2Str = "{" ++ string.join_list(",",list.map(to_string,E2L)) ++ "}",
    IStr = "{" ++ string.join_list(",",list.map(to_string,IL)) ++ "}",
    Cmd = "in_p_loc(" ++ string.join_list(",",[E1Str,E2Str,IStr]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_and_c_e(_) = Pred then
    solutions(pred(E1::out) is nondet :- and_c_e(RelHandle,E1,_,_), E1L),
    solutions(pred(E2::out) is nondet :- and_c_e(RelHandle,_,E2,_), E2L),
    solutions(pred(E3::out) is nondet :- and_c_e(RelHandle,_,_,E3), E3L),
    solutions(pred(Inst::out) is nondet :- in_p_loc(RelHandle,_,_,Inst), IL),
    E1Str = "{" ++ string.join_list(",",list.map(to_string,E1L)) ++ "}",
    E2Str = "{" ++ string.join_list(",",list.map(to_string,E2L)) ++ "}",
    E3Str = "{" ++ string.join_list(",",list.map(to_string,E3L)) ++ "}",
    IStr = "{" ++ string.join_list(",",list.map(to_string,IL)) ++ "}",
    Cmd = "and_c_e(" ++ string.join_list(",",[E1Str,E2Str,E3Str,IStr]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_be_v_id(_) = Pred then
    solutions(pred(E::out) is nondet :- be_v_id(RelHandle,E,_,_), EL),
    solutions(pred(I1::out) is nondet :- be_v_id(RelHandle,_,I1,_), I1L),
    solutions(pred(I2::out) is nondet :- be_v_id(RelHandle,_,_,I2), I2L),
    E1Str = "{" ++ string.join_list(",",list.map(to_string,EL)) ++ "}",
    I1Str = "{" ++ string.join_list(",",list.map(to_string,I1L)) ++ "}",
    I2Str = "{" ++ string.join_list(",",list.map(to_string,I2L)) ++ "}",
    Cmd = "be_v_id(" ++ string.join_list(",",[E1Str,I1Str,I2Str]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_always_a_1(_) = Pred then
    solutions(pred(Indiv::out) is nondet :- always_a_1(RelHandle,Indiv,_), IndivL),
    solutions(pred(Event::out) is nondet :- always_a_1(RelHandle,_,Event), EL),
    IndivStr = "{" ++ string.join_list(",",list.map(to_string,IndivL)) ++ "}",
    EStr = "{" ++ string.join_list(",",list.map(to_string,EL)) ++ "}",
    Cmd = "be_v_id(" ++ string.join_list(",",[IndivStr,EStr]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_hate_v_1(_) = Pred then
    solutions(pred(Event::out) is nondet :- hate_v_1(RelHandle,Event,_,_), EL),
    solutions(pred(I1::out) is nondet :- hate_v_1(RelHandle,_,I1,_), I1L),
    solutions(pred(I2::out) is nondet :- hate_v_1(RelHandle,_,I2,_), I2L),
    E1Str = "{" ++ string.join_list(",",list.map(to_string,EL)) ++ "}",
    I1Str = "{" ++ string.join_list(",",list.map(to_string,I1L)) ++ "}",
    I2Str = "{" ++ string.join_list(",",list.map(to_string,I2L)) ++ "}",
    Cmd = "hate_v_1(" ++ string.join_list(",",[E1Str,I1Str,I2Str]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_never_a_1(_) = Pred then
    solutions(pred(Indiv::out) is nondet :- never_a_1(RelHandle,Indiv,_), IndivL),
    solutions(pred(Ret::out) is nondet :-
       (never_a_1(RelHandle,_,RH),
        multi_map.lookup(RelMap,RH,Refs),
        Ret = list.map(func({RelHandle0,_,_,Preds}) = Val is det :- Val = RelHandle0, Refs)),
       RHL),
    % list.condense(RHL,RHLc),
    IndivStr = "{" ++ string.join_list(",",list.map(to_string,IndivL)) ++ "}",
    % RHStr = "{" ++ string.join_list(",",list.map(to_string,RHLc)) ++ "}",
    RHStr = "",
    Cmd = "never_a_1(" ++ string.join_list(",",[IndivStr,RHStr]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_neg(_) = Pred then
    solutions(pred(Event::out) is nondet :- neg(RelHandle,Event,_), EL),
    solutions(pred(Ret::out) is nondet :-
       (neg(RelHandle,_,RH),
        multi_map.lookup(RelMap,RH,Refs),
        Ret = list.map(func({RelHandle0,_,_,Preds}) = Val is det :- Val = RelHandle0, Refs)),
       RHL),
    % list.condense(RHL,RHLc),
    EStr = "{" ++ string.join_list(",",list.map(to_string,EL)) ++ "}",
    % RHStr = "{" ++ string.join_list(",",list.map(to_string,RHLc)) ++ "}",
    RHStr = "",
    Cmd = "neg(" ++ string.join_list(",",[EStr,RHStr]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_colon_p_namely(_) = Pred then
    solutions(pred(Event::out) is nondet :- colon_p_namely(RelHandle,Event,_,_), EL),
    solutions(pred(Ret::out) is nondet :-
       (colon_p_namely(RelHandle,_,RH1,_),
        multi_map.lookup(RelMap,RH1,Refs),
        Ret = list.map(func({RelHandle0,_,_,Preds}) = Val is det :- Val = {RelHandle0,Preds}, Refs)),
       RH1L),
    solutions(pred(Ret::out) is nondet :-
       (colon_p_namely(RelHandle,_,_,RH2),
        multi_map.lookup(RelMap,RH2,Refs),
        Ret = list.map(func({RelHandle0,_,_,Preds}) = Val is det :- Val = {RelHandle0,Preds}, Refs)),
       RH2L),
    % list.condense(RHL1,RHL1c),
    % list.condense(RHL2,RHL2c),
    EStr = "{" ++ string.join_list(",",list.map(to_string,EL)) ++ "}",
    % RH1Str = "{" ++ string.join_list(",",list.map(to_string,RHL1c)) ++ "}",
    % RH2Str = "{" ++ string.join_list(",",list.map(to_string,RHL2c)) ++ "}",
    RH1Str = "",
    RH2Str = "",
    Cmd = "colon_p_namely(" ++ string.join_list(",",[EStr,RH1Str,RH2Str]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_person(_) = Pred then
    solutions(pred(Inst::out) is nondet :- person(RelHandle,Inst), IL),
    IStr = "{" ++ string.join_list(",",list.map(to_string,IL)) ++ "}",
    Cmd = "person(" ++ string.join_list(",",[IStr]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_some_q(_) = Pred then
    solutions(pred(Inst::out) is nondet :- some_q(RelHandle,Inst,_,_), IL),
    solutions(pred(RstrHandle::out) is nondet :- some_q(RelHandle,_,RstrHandle,_), RSHL),
    solutions(pred(BodyHandle::out) is nondet :- some_q(RelHandle,_,_,BodyHandle), BHL),
    IStr = "{" ++ string.join_list(",",list.map(to_string,IL)) ++ "}",
    RSHLStr = "{" ++ string.join_list(",",list.map(to_string,RSHL)) ++ "}",
    BHStr = "{" ++ string.join_list(",",list.map(to_string,BHL)) ++ "}",
    Cmd = "some_q(" ++ string.join_list(",",[IStr,RSHLStr,BHStr]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_named(_) = Pred then
    solutions(pred(Inst::out) is nondet :- named(RelHandle,Inst,_), IL),
    solutions(pred(Carg::out) is nondet :- named(RelHandle,_,Carg), CargL),
    IStr = "{" ++ string.join_list(",",list.map(to_string,IL)) ++ "}",
    CStr = "{" ++ string.join_list(",",list.map(to_string,CargL)) ++ "}",
    Cmd = "named(" ++ string.join_list(",",[IStr,CStr]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else if pred_compound(_) = Pred then
    solutions(pred(Event::out) is nondet :- compound(RelHandle,Event,_,_), EL),
    solutions(pred(Inst::out) is nondet :- compound(RelHandle,_,Inst,_), IL1),
    solutions(pred(Inst::out) is nondet :- compound(RelHandle,_,_,Inst), IL2),
    EStr = "{" ++ string.join_list(",",list.map(to_string,EL)) ++ "}",
    I1Str = "{" ++ string.join_list(",",list.map(to_string,IL1)) ++ "}",
    I2Str = "{" ++ string.join_list(",",list.map(to_string,IL2)) ++ "}",
    Cmd = "compound(" ++ string.join_list(",",[EStr,I1Str,I2Str]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else	 if pred_proper_q(_) = Pred then
    solutions(pred(Inst::out) is nondet :- proper_q(RelHandle,Inst,_,_), IL),
    solutions(pred(RstrHandle::out) is nondet :- proper_q(RelHandle,_,RstrHandle,_), RSHL),
    solutions(pred(BodyHandle::out) is nondet :- proper_q(RelHandle,_,_,BodyHandle), BHL),
    IStr = "{" ++ string.join_list(",",list.map(to_string,IL)) ++ "}",
    RSHLStr = "{" ++ string.join_list(",",list.map(to_string,RSHL)) ++ "}",
    BHStr = "{" ++ string.join_list(",",list.map(to_string,BHL)) ++ "}",
    Cmd = "proper_q(" ++ string.join_list(",",[IStr,RSHLStr,BHStr]) ++ ")",
    OutputsOut = set.insert(OutputsIn,Cmd)
  else
    impure unsafe_perform_io(print(Pred)),
    error("unknown predicate").

:- pred loadArgMapForSentence(mrs_psoa_post,
                              multi_map(mrs_types, mrs_rel_handle),
		              multi_map(mrs_types, mrs_rel_handle)).
:- mode loadArgMapForSentence(in,in,out) is det.
loadArgMapForSentence(Sentence,ArgMapIn,ArgMapOut) :-
  psoa_post(TopHandle,Event,RelMap) = Sentence,
  expandArgMap(RelMap,ArgMapIn,ArgMapOut).

:- func loadArgMap = multi_map(mrs_types, mrs_rel_handle).
loadArgMap = ArgMap :-
  list.foldl(loadArgMapForSentence,sentences.sentences,multi_map.init,ArgMap).

main(!IO) :-
  ArgMap = loadArgMap,
  psoa_post(TopHandle,Event,RelMap) = det_head(sentences.sentences),
  multi_map.lookup(RelMap,TopHandle,L),
  {RelHandle,_,_,Pred} = det_head(L),
  unpackRelation(RelMap,ArgMap,RelHandle,Pred,set.init,Outputs),
  io.print(Outputs,!IO).
