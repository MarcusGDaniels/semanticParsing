:- module mrs.
:- interface.
:- import_module string.
:- import_module list.

:- type mrs_carg ---> mrs_carg(string).

:- type mrs_event ---> mrs_event(string).

:- type mrs_inst ---> mrs_inst(string).

:- type mrs_indiv ---> mrs_indiv(string).

:- type mrs_unknown ---> mrs_unknown(string).

:- type mrs_handle ---> mrs_handle(string).

:- type mrs_body_handle ---> mrs_body_handle(mrs_handle).

:- type mrs_rstr_handle ---> mrs_rstr_handle(mrs_handle).

:- type mrs_rel_handle ---> mrs_rel_handle(mrs_handle).

:- type mrs_top_handle ---> mrs_top_handle(mrs_handle).

:- type mrs_rel_t --->  rel_unknown(mrs_rel_handle, mrs_unknown, mrs_event) 
                        ; rel_person(mrs_rel_handle, mrs_inst)
                        ; rel_pron(mrs_rel_handle, mrs_inst)
                        ; rel_generic_entity(mrs_rel_handle, mrs_inst)
                        ; rel_proper_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle)
                        ; rel_some_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle)
                        ; rel_every_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle)
                        ; rel_udef_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle)
                        ; rel_the_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle)
                        ; rel_a_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle)
                        ; rel_def_explicit_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle)
                        ; rel_pronoun_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle)
                        ; rel_no_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle)
                        ; rel_live_v_1(mrs_rel_handle, mrs_event, mrs_inst)
                        ; rel_only_a_1(mrs_rel_handle, mrs_event, mrs_inst)
                        ; rel_neg(mrs_rel_handle, mrs_event, mrs_rel_handle)
                        ; rel_always_a_1(mrs_rel_handle, mrs_indiv, mrs_event)
                        ; rel_never_a_1(mrs_rel_handle, mrs_indiv, mrs_rel_handle)
                        ; rel_therefore_a_1(mrs_rel_handle, mrs_indiv, mrs_rel_handle)
                        ; rel_rich_a_in(mrs_rel_handle, mrs_event, mrs_inst, mrs_indiv)
                        ; rel_more_comp(mrs_rel_handle, mrs_event, mrs_event, mrs_inst)
                        ; rel_named(mrs_rel_handle, mrs_inst, mrs_carg)
                        ; rel_card(mrs_rel_handle, mrs_event, mrs_inst, mrs_carg)
                        ; rel_chase_v_1(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst)
                        ; rel_hate_v_1(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst)
                        ; rel_be_v_id(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst)
                        ; rel_kill_v_1(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst)
                        ; rel_poss(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst)
                        ; rel_in_p_loc(mrs_rel_handle, mrs_event, mrs_event, mrs_inst)
                        ; rel_compound(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst)
			; rel_implicit_conj(mrs_rel_handle, mrs_inst, mrs_inst, mrs_inst)
			; rel_and_c_x(mrs_rel_handle, mrs_inst, mrs_inst, mrs_inst)
			; rel_and_c_e(mrs_rel_handle, mrs_event, mrs_event, mrs_event)
			; rel_people_n_of(mrs_rel_handle, mrs_inst, mrs_indiv)
			; rel_victim_n_of(mrs_rel_handle, mrs_inst, mrs_indiv)
			; rel_aunt_n_of(mrs_rel_handle, mrs_inst, mrs_indiv)
			; rel_butler_n_1(mrs_rel_handle, mrs_inst)
			; rel_killer_n_1(mrs_rel_handle, mrs_inst)
			; rel_therein_p_dir(mrs_rel_handle, mrs_event, mrs_event)
			; rel_except_p(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst)
			; rel_colon_p_namely(mrs_rel_handle, mrs_event, mrs_rel_handle, mrs_rel_handle).

:- type mrs_rel_qeq_t ---> mrs_rel_qeq(h1 :: mrs_rel_handle,h2 :: mrs_rel_handle).
:- type mrs_hcons ---> hcons(list(mrs_rel_qeq_t)).
:- type mrs_psoa ---> psoa(mrs_handle,mrs_event,list(mrs_rel_t),mrs_hcons).

:- typeclass mrs_print(T) where [
  func to_string(T) = string,
  mode to_string(in) = out is det
].

:- type mrs_alg_attr ---> attr_carg(mrs_carg)
                      ; attr_inst(string,mrs_inst)
                      ; attr_rstr(mrs_rstr_handle)
                      ; attr_body(mrs_body_handle)
                      ; attr_event(string,mrs_event)
                      ; attr_indiv(string,mrs_indiv)
                      ; attr_handle(string,mrs_handle)
		      ; attr_unknown(string,mrs_unknown).

:- func rel(string,mrs_handle,list(mrs_alg_attr)) = mrs_rel_t.
:- mode rel(in, in, in) = out is det.

:- func qeq(mrs_handle,mrs_handle) = mrs_rel_qeq_t.
:- mode qeq(in, in) = out is det.

:- typeclass mrs_attr(T) where [
  func attrval(string,T) = mrs_alg_attr
].
:- instance mrs_attr(string).
:- instance mrs_attr(mrs_inst).
:- instance mrs_attr(mrs_indiv).
:- instance mrs_attr(mrs_handle).
:- instance mrs_attr(mrs_event).
:- instance mrs_attr(mrs_unknown).

:- instance mrs_print(mrs_inst).
:- instance mrs_print(mrs_event).
:- instance mrs_print(mrs_indiv).
:- instance mrs_print(mrs_carg).
:- instance mrs_print(mrs_rel_t).
:- instance mrs_print(mrs_rel_qeq_t).
:- instance mrs_print(mrs_hcons).
:- instance mrs_print(mrs_psoa).
:- instance mrs_print(mrs_rel_handle).
:- instance mrs_print(mrs_rstr_handle).
:- instance mrs_print(mrs_body_handle).
:- instance mrs_print(mrs_unknown).

:- func relationDeclarations(list(mrs_rel_t)) = string.

:- implementation.
:- import_module require.
:- import_module set.
:- import_module io.
:- import_module unsafe.

:- instance mrs_attr(string) where [
  attrval(_,Val) = attr_carg(mrs_carg(Val))
].

:- instance mrs_attr(mrs_inst) where [
  func(attrval/2) is attr_inst
].

:- instance mrs_attr(mrs_indiv) where [
  func(attrval/2) is attr_indiv
].

:- instance mrs_attr(mrs_unknown) where [
  func(attrval/2) is attr_unknown
].

:- func extract_handle(string,mrs_handle) = mrs_alg_attr.
extract_handle(Key,Val) = Ret :-
  (Key = "RSTR", Ret = attr_rstr(mrs_rstr_handle(Val))
  ;Key = "BODY", Ret = attr_body(mrs_body_handle(Val))
  ;Key = "ARG1", Ret = attr_handle(Key,Val)
  ;Key = "ARG2", Ret = attr_handle(Key,Val)
  ; error(string.join_list(",",["bad key:",Key,to_string(Val)]))).

:- instance mrs_attr(mrs_handle) where [
  func(attrval/2) is extract_handle
].

:- instance mrs_attr(mrs_event) where [
  func(attrval/2) is attr_event
].

:- instance mrs_print(mrs_carg) where [
  to_string(mrs_carg(Val)) = string.append_list(["mrs_carg(","\"",Val,"\"",")"])
].

:- instance mrs_print(mrs_event) where [
  to_string(mrs_event(Val)) = Val
].

:- instance mrs_print(mrs_inst) where [
  to_string(mrs_inst(Val)) = Val
].

:- instance mrs_print(mrs_indiv) where [
  to_string(mrs_indiv(Val)) = Val
]
	.
:- instance mrs_print(mrs_unknown) where [
  to_string(mrs_unknown(Val)) = Val
].

:- instance mrs_print(mrs_body_handle) where [
  to_string(mrs_body_handle(mrs_handle(Val))) = string.append_list(["mrs_body_handle(",Val,")"])
].

:- instance mrs_print(mrs_rstr_handle) where [
  to_string(mrs_rstr_handle(mrs_handle(Val))) = string.append_list(["mrs_rstr_handle(",Val,")"])
].

:- instance mrs_print(mrs_rel_handle) where [
  to_string(mrs_rel_handle(mrs_handle(Val))) = string.append_list(["mrs_rel_handle(",Val,")"])
].

:- instance mrs_print(mrs_top_handle) where [
  to_string(mrs_top_handle(mrs_handle(Val))) = Val
].

:- instance mrs_print(mrs_handle) where [
  to_string(mrs_handle(Val)) = Val
].

% :- pragma promise_pure(unpack_and_c/2). 
:- func unpack_and_c(mrs_handle,list(mrs_alg_attr)) = mrs_rel_t.
:- mode unpack_and_c(in,in) = out is det.
unpack_and_c(Handle,Args) = Ret :-
  RH = mrs_rel_handle(Handle),
  (if (attr_event(_,Arg0) = det_index0(Args,0)) then
    (if attr_event(_,Arg1) = det_index0(Args,1) then
      (if attr_event(_,Arg2) = det_index0(Args,2) then
         Ret = rel_and_c_e(RH,Arg0,Arg1,Arg2)
       else
         error("no2event"))
     else
      error("no1event"))
  else
   (if (attr_inst(_,Arg0) = det_index0(Args,0)) then
     (if attr_inst(_,Arg1) = det_index0(Args,1) then
       (if attr_inst(_,Arg2) = det_index0(Args,2) then
         Ret = rel_and_c_x(RH,Arg0,Arg1,Arg2)
        else
          error("no2inst"))
      else 
        error("no1inst"))
    else
      error("no0inst"))).

% :- pragma promise_pure(rel/3). 
rel(Key,Handle,Args) = Ret :-
  (Key = "unknown", 
      attr_unknown(_,Arg0) = det_index0(Args,0),
      attr_event(_,Arg1) = det_index0(Args,1),
      Ret = rel_unknown(mrs_rel_handle(Handle),Arg0,Arg1)
  ; Key = "person", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      Ret = rel_person(mrs_rel_handle(Handle),Arg0)
 ; Key = "pron", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      Ret = rel_pron(mrs_rel_handle(Handle),Arg0)
 ; Key = "generic_entity", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      Ret = rel_generic_entity(mrs_rel_handle(Handle),Arg0)
 ; Key = "proper_q",
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_rstr(Rstr) = det_index0(Args,1),
      attr_body(Body) = det_index0(Args,2),
      Ret = rel_proper_q(mrs_rel_handle(Handle),Arg0,Rstr,Body)
 ; Key = "_some_q", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_rstr(Rstr) = det_index0(Args,1),
      attr_body(Body) = det_index0(Args,2),
      Ret = rel_some_q(mrs_rel_handle(Handle),Arg0,Rstr,Body)
 ; Key = "every_q", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_rstr(Rstr) = det_index0(Args,1),
      attr_body(Body) = det_index0(Args,2),
      Ret = rel_every_q(mrs_rel_handle(Handle),Arg0,Rstr,Body)
 ; Key = "udef_q", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_rstr(Rstr) = det_index0(Args,1),
      attr_body(Body) = det_index0(Args,2),
      Ret = rel_udef_q(mrs_rel_handle(Handle),Arg0,Rstr,Body)
 ; Key = "_the_q", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_rstr(Rstr) = det_index0(Args,1),
      attr_body(Body) = det_index0(Args,2),
      Ret = rel_the_q(mrs_rel_handle(Handle),Arg0,Rstr,Body)
 ; Key = "_a_q", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_rstr(Rstr) = det_index0(Args,1),
      attr_body(Body) = det_index0(Args,2),
      Ret = rel_a_q(mrs_rel_handle(Handle),Arg0,Rstr,Body)
 ; Key = "def_explicit_q", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_rstr(Rstr) = det_index0(Args,1),
      attr_body(Body) = det_index0(Args,2),
      Ret = rel_def_explicit_q(mrs_rel_handle(Handle),Arg0,Rstr,Body)
 ; Key = "pronoun_q", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_rstr(Rstr) = det_index0(Args,1),
      attr_body(Body) = det_index0(Args,2),
      Ret = rel_pronoun_q(mrs_rel_handle(Handle),Arg0,Rstr,Body)
 ; Key = "_no_q", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_rstr(Rstr) = det_index0(Args,1),
      attr_body(Body) = det_index0(Args,2),
      Ret = rel_no_q(mrs_rel_handle(Handle),Arg0,Rstr,Body)
 ; Key = "named", 
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_carg(Arg1) = det_index0(Args,1),
      Ret = rel_named(mrs_rel_handle(Handle),Arg0,Arg1)
 ; Key = "card", 
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      attr_carg(Arg2) = det_index0(Args,2),
      Ret = rel_card(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "_live_v_1",
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      Ret = rel_live_v_1(mrs_rel_handle(Handle),Arg0,Arg1)
 ; Key = "_only_a_1",
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      Ret = rel_only_a_1(mrs_rel_handle(Handle),Arg0,Arg1)
 ; Key = "neg",
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_handle(_,Arg1) = det_index0(Args,1),
      Ret = rel_neg(mrs_rel_handle(Handle),Arg0,mrs_rel_handle(Arg1))
 ; Key = "_always_a_1",
      attr_indiv(_,Arg0) = det_index0(Args,0),
      attr_event(_,Arg1) = det_index0(Args,1),
      Ret = rel_always_a_1(mrs_rel_handle(Handle),Arg0,Arg1)
 ; Key = "_never_a_1",
      attr_indiv(_,Arg0) = det_index0(Args,0),
      attr_handle(_,Arg1) = det_index0(Args,1),
      Ret = rel_never_a_1(mrs_rel_handle(Handle),Arg0,mrs_rel_handle(Arg1))
 ; Key = "_therefore_a_1",
      attr_indiv(_,Arg0) = det_index0(Args,0),
      attr_handle(_,Arg1) = det_index0(Args,1),
      Ret = rel_therefore_a_1(mrs_rel_handle(Handle),Arg0,mrs_rel_handle(Arg1))
 ; Key = "_rich_a_in",
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      attr_indiv(_,Arg2) = det_index0(Args,2),
      Ret = rel_rich_a_in(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "more_comp",
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_event(_,Arg1) = det_index0(Args,1),
      attr_inst(_,Arg2) = det_index0(Args,2),
      Ret = rel_more_comp(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "_be_v_id", 
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      attr_inst(_,Arg2) = det_index0(Args,2),
      Ret = rel_be_v_id(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "_chase_v_1", 
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      attr_inst(_,Arg2) = det_index0(Args,2),
      Ret = rel_chase_v_1(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "_kill_v_1", 
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      attr_inst(_,Arg2) = det_index0(Args,2),
      Ret = rel_kill_v_1(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "_hate_v_1", 
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      attr_inst(_,Arg2) = det_index0(Args,2),
      Ret = rel_hate_v_1(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "poss", 
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      attr_inst(_,Arg2) = det_index0(Args,2),
      Ret = rel_poss(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "compound",
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      attr_inst(_,Arg2) = det_index0(Args,2),
      Ret = rel_compound(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "implicit_conj",
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      attr_inst(_,Arg2) = det_index0(Args,2),
      Ret = rel_implicit_conj(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "_and_c",
      Ret = unpack_and_c(Handle,Args)
 ; Key = "_in_p_loc",
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_event(_,Arg1) = det_index0(Args,1),
      attr_inst(_,Arg2) = det_index0(Args,2),
      Ret = rel_in_p_loc(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "_people_n_of",
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_indiv(_,Arg1) = det_index0(Args,1),
      Ret = rel_people_n_of(mrs_rel_handle(Handle),Arg0,Arg1)
 ; Key = "_victim_n_of",
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_indiv(_,Arg1) = det_index0(Args,1),
      Ret = rel_victim_n_of(mrs_rel_handle(Handle),Arg0,Arg1)
 ; Key = "_aunt_n_of",
      attr_inst(_,Arg0) = det_index0(Args,0),
      attr_indiv(_,Arg1) = det_index0(Args,1),
      Ret = rel_aunt_n_of(mrs_rel_handle(Handle),Arg0,Arg1)
 ; Key = "_butler_n_1",
      attr_inst(_,Arg0) = det_index0(Args,0),
      Ret = rel_butler_n_1(mrs_rel_handle(Handle),Arg0)
 ; Key = "_killer_n_1",
      attr_inst(_,Arg0) = det_index0(Args,0),
      Ret = rel_killer_n_1(mrs_rel_handle(Handle),Arg0)
 ; Key = "_therein_p_dir",
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_event(_,Arg1) = det_index0(Args,1),
      Ret = rel_therein_p_dir(mrs_rel_handle(Handle),Arg0,Arg1)
 ; Key = "_except_p",
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_inst(_,Arg1) = det_index0(Args,1),
      attr_inst(_,Arg2) = det_index0(Args,2),
      Ret = rel_except_p(mrs_rel_handle(Handle),Arg0,Arg1,Arg2)
 ; Key = "_colon_p_namely",
      attr_event(_,Arg0) = det_index0(Args,0),
      attr_handle(_,Arg1) = det_index0(Args,1),
      attr_handle(_,Arg2) = det_index0(Args,2),
      Ret = rel_colon_p_namely(mrs_rel_handle(Handle),Arg0,mrs_rel_handle(Arg1),mrs_rel_handle(Arg2))
 ; error(string.join_list(",",["impossible0",Key]))
 ).

qeq(Lhs,Rhs) = Ret :-
  Ret = mrs_rel_qeq(mrs_rel_handle(Lhs),mrs_rel_handle(Rhs)).

:- func combine_args(list(string)) = string.
:- mode combine_args(in) = out is det.
combine_args(L) = Ret :- Ret = list.foldl(func(Item,Acc) = string.append_list([Acc,",",Item]),det_tail(L),det_head(L)).

% :- pragma promise_pure(rel_to_string/1). 
:- func rel_to_string(mrs_rel_t) = string.
:- mode rel_to_string(in) = out is det.
rel_to_string(Val) = Ret :-
    (rel_unknown(RelHandle, Unknown, Event) = Val,
     Ret = string.append_list(["unknown(",to_string(RelHandle),",",to_string(Unknown),",",to_string(Event),").\n"])
   ; rel_person(RelHandle, Inst) = Val,
     Ret = string.append_list(["person(",to_string(RelHandle),",",to_string(Inst),").\n"])
   ; rel_pron(RelHandle, Inst) = Val,
     Ret = string.append_list(["pron(",to_string(RelHandle),",",to_string(Inst),").\n"])
   ; rel_generic_entity(RelHandle, Inst) = Val,
     Ret = string.append_list(["generic_entity(",to_string(RelHandle),",",to_string(Inst),").\n"])
   ; rel_proper_q(RelHandle, Inst, RstrHandle, BodyHandle) = Val,
     Ret = string.append_list(["proper_q(",to_string(RelHandle),",",to_string(Inst),",",to_string(RstrHandle),",",to_string(BodyHandle),").\n"])
   ; rel_some_q(RelHandle, Inst, RstrHandle, BodyHandle) = Val,
     Ret = string.append_list(["some_q(",to_string(RelHandle),",",to_string(Inst),",",to_string(RstrHandle),",",to_string(BodyHandle),").\n"])
   ; rel_every_q(RelHandle, Inst, RstrHandle, BodyHandle) = Val,
     Ret = string.append_list(["every_q(",to_string(RelHandle),",",to_string(Inst),",",to_string(RstrHandle),",",to_string(BodyHandle),").\n"])
   ; rel_udef_q(RelHandle, Inst, RstrHandle, BodyHandle) = Val,
     Ret = string.append_list(["udef_q(",to_string(RelHandle),",",to_string(Inst),",",to_string(RstrHandle),",",to_string(BodyHandle),").\n"])
   ; rel_the_q(RelHandle, Inst, RstrHandle, BodyHandle) = Val,
     Ret = string.append_list(["the_q(",to_string(RelHandle),",",to_string(Inst),",",to_string(RstrHandle),",",to_string(BodyHandle),").\n"])
   ; rel_a_q(RelHandle, Inst, RstrHandle, BodyHandle) = Val,
     Ret = string.append_list(["a_q(",to_string(RelHandle),",",to_string(Inst),",",to_string(RstrHandle),",",to_string(BodyHandle),").\n"])
   ; rel_def_explicit_q(RelHandle, Inst, RstrHandle, BodyHandle) = Val,
     Ret = string.append_list(["def_explicit_q(",to_string(RelHandle),",",to_string(Inst),",",to_string(RstrHandle),",",to_string(BodyHandle),").\n"])
   ; rel_pronoun_q(RelHandle, Inst, RstrHandle, BodyHandle) = Val,
     Ret = string.append_list(["pronoun_q(",to_string(RelHandle),",",to_string(Inst),",",to_string(RstrHandle),",",to_string(BodyHandle),").\n"])
   ; rel_no_q(RelHandle, Inst, RstrHandle, BodyHandle) = Val,
     Ret = string.append_list(["no_q(",to_string(RelHandle),",",to_string(Inst),",",to_string(RstrHandle),",",to_string(BodyHandle),").\n"])
   ; rel_live_v_1(RelHandle, Event, Inst) = Val,
     Ret = string.append_list(["live_v_1(",to_string(RelHandle),",",to_string(Event),",",to_string(Inst),").\n"])
   ; rel_only_a_1(RelHandle, Event, Inst) = Val,
     Ret = string.append_list(["only_a_1(",to_string(RelHandle),",",to_string(Event),",",to_string(Inst),").\n"])
   ; rel_neg(RelHandle, Event, RelHandle0) = Val,
     Ret = string.append_list(["neg(",to_string(RelHandle),",",to_string(Event),",",to_string(RelHandle0),").\n"])
   ; rel_always_a_1(RelHandle, Indiv, Event) = Val,
     Ret = string.append_list(["always_a_1(",to_string(RelHandle),",",to_string(Indiv),",",to_string(Event),").\n"])
   ; rel_never_a_1(RelHandle, Indiv, RelHandle0) = Val,
     Ret = string.append_list(["never_a_1(",to_string(RelHandle),",",to_string(Indiv),",",to_string(RelHandle0),").\n"])
   ; rel_therefore_a_1(RelHandle, Indiv, RelHandle0) = Val,
     Ret = string.append_list(["therefore_a_1(",to_string(RelHandle),",",to_string(Indiv),",",to_string(RelHandle0),").\n"])
   ; rel_rich_a_in(RelHandle, Event, Inst, Indiv) = Val,
     Ret = string.append_list(["rich_a_in(",to_string(RelHandle),",",to_string(Event),",",to_string(Inst),",",to_string(Indiv),").\n"])
   ; rel_more_comp(RelHandle, E1, E2, Inst) = Val,
     Ret = string.append_list(["more_comp(",to_string(RelHandle),",",to_string(E1),",",to_string(E2),",",to_string(Inst),").\n"])
   ; rel_named(RelHandle, Inst, Carg) = Val,
     Ret = string.append_list(["named(",to_string(RelHandle),",",to_string(Inst),",",to_string(Carg),").\n"])
   ; rel_card(RelHandle, Event, Inst, Carg) = Val,
     Ret = string.append_list(["card(",to_string(RelHandle),",",to_string(Event),",",to_string(Inst),",",to_string(Carg),").\n"])
   ; rel_be_v_id(RelHandle, Event, A, B) = Val,
     Ret = string.append_list(["be_v_id(",to_string(RelHandle),",",to_string(Event),",",to_string(A),",",to_string(B),").\n"])
   ; rel_chase_v_1(RelHandle, Event, A, B) = Val,
     Ret = string.append_list(["chase_v_1(",to_string(RelHandle),",",to_string(Event),",",to_string(A),",",to_string(B),").\n"])
   ; rel_kill_v_1(RelHandle, Event, A, B) = Val,
     Ret = string.append_list(["kill_v_1(",to_string(RelHandle),",",to_string(Event),",",to_string(A),",",to_string(B),").\n"])
   ; rel_hate_v_1(RelHandle, Event, A, B) = Val,
     Ret = string.append_list(["hate_v_1(",to_string(RelHandle),",",to_string(Event),",",to_string(A),",",to_string(B),").\n"])
   ; rel_poss(RelHandle, Event, A, B) = Val,
     Ret = string.append_list(["poss(",to_string(RelHandle),",",to_string(Event),",",to_string(A),",",to_string(B),").\n"])
   ; rel_in_p_loc(RelHandle, Event1, Event2, Inst) = Val,
     Ret = string.append_list(["in_p_loc(",to_string(RelHandle),",",to_string(Event1),",",to_string(Event2),",",to_string(Inst),").\n"])
   ; rel_compound(RelHandle, Event, A, B) = Val,
     Ret = string.append_list(["compound(",to_string(RelHandle),",",to_string(Event),",",to_string(A),",",to_string(B),").\n"])
   ; rel_implicit_conj(RelHandle, A, B, C) = Val,
     Ret = string.append_list(["implicit_conj(",to_string(RelHandle),",",to_string(A),",",to_string(B),",",to_string(C),").\n"])
   ; rel_and_c_e(RelHandle, E1, E2, E3) = Val,
     Ret = string.append_list(["and_c_e(",to_string(RelHandle),",",to_string(E1),",",to_string(E2),",",to_string(E3),").\n"])
   ; rel_and_c_x(RelHandle, X1, X2, X3) = Val,
     Ret = string.append_list(["and_c_x(",to_string(RelHandle),",",to_string(X1),",",to_string(X2),",",to_string(X3),").\n"])
   ; rel_people_n_of(RelHandle, Inst, Indiv) = Val,
     Ret = string.append_list(["people_n_of(",to_string(RelHandle),",",to_string(Inst),",",to_string(Indiv),").\n"])
   ; rel_victim_n_of(RelHandle, Inst, Indiv) = Val,
     Ret = string.append_list(["victim_n_of(",to_string(RelHandle),",",to_string(Inst),",",to_string(Indiv),").\n"])
   ; rel_aunt_n_of(RelHandle, Inst, Indiv) = Val,
     Ret = string.append_list(["aunt_n_of(",to_string(RelHandle),",",to_string(Inst),",",to_string(Indiv),").\n"])
   ; rel_butler_n_1(RelHandle, Inst) = Val,
     Ret = string.append_list(["butler_n_1(",to_string(RelHandle),",",to_string(Inst),").\n"])
   ; rel_killer_n_1(RelHandle, Inst) = Val,
     Ret = string.append_list(["killer_n_1(",to_string(RelHandle),",",to_string(Inst),").\n"])
   ; rel_therein_p_dir(RelHandle, E1, E2) = Val,
     Ret = string.append_list(["therein_p_dir(",to_string(RelHandle),",",to_string(E1),",",to_string(E2),").\n"])
   ; rel_except_p(RelHandle, Event, A, B) = Val,
     Ret = string.append_list(["except_p(",to_string(RelHandle),",",to_string(Event),",",to_string(A),",",to_string(B),").\n"])
   ; rel_colon_p_namely(RelHandle, Event, RelHandle0, RelHandle1) = Val,
     Ret = string.append_list(["colon_p_namely(",to_string(RelHandle),",",to_string(Event),",",to_string(RelHandle0),",",to_string(RelHandle1),").\n"])
   ; error("impossible1")).

:- func rel_to_call(mrs_rel_t) = string.
:- mode rel_to_call(in) = out is det.
rel_to_call(Val) = Ret :-
    (rel_unknown(_, _, _) = Val,
     Ret = string.append_list(["unknown(","RelHandle",",","Unknown",",","Event",")"])
   ; rel_person(_, _) = Val,
     Ret = string.append_list(["person(","RelHandle",",","Inst",")"])
   ; rel_pron(_, _) = Val,
     Ret = string.append_list(["pron(","RelHandle",",","Inst",")"])
   ; rel_generic_entity(_, _) = Val,
     Ret = string.append_list(["generic_entity(","RelHandle",",","Inst",")"])
   ; rel_proper_q(_, _, _, _) = Val,
     Ret = string.append_list(["proper_q(","RelHandle",",","Inst",",","RstrHandle",",","BodyHandle",")"])
   ; rel_some_q(_, _, _, _) = Val,
     Ret = string.append_list(["some_q(","RelHandle",",","Inst",",","RstrHandle",",","BodyHandle",")"])
   ; rel_every_q(_, _, _, _) = Val,
     Ret = string.append_list(["every_q(","RelHandle",",","Inst",",","RstrHandle",",","BodyHandle",")"])
   ; rel_udef_q(_, _, _, _) = Val,
     Ret = string.append_list(["udef_q(","RelHandle",",","Inst",",","RstrHandle",",","BodyHandle",")"])
   ; rel_the_q(_, _, _, _) = Val,
     Ret = string.append_list(["the_q(","RelHandle",",","Inst",",","RstrHandle",",","BodyHandle",")"])
   ; rel_a_q(_, _, _, _) = Val,
     Ret = string.append_list(["a_q(","RelHandle",",","Inst",",","RstrHandle",",","BodyHandle",")"])
   ; rel_def_explicit_q(_, _, _, _) = Val,
     Ret = string.append_list(["def_explicit_q(","RelHandle",",","Inst",",","RstrHandle",",","BodyHandle",")"])
   ; rel_pronoun_q(_, _, _, _) = Val,
     Ret = string.append_list(["pronoun_q(","RelHandle",",","Inst",",","RstrHandle",",","BodyHandle",")"])
   ; rel_no_q(_, _, _, _) = Val,
     Ret = string.append_list(["no_q(","RelHandle",",","Inst",",","RstrHandle",",","BodyHandle",")"])
   ; rel_live_v_1(_, _, _) = Val,
     Ret = string.append_list(["live_v_1(","RelHandle",",","Event",",","Inst",")"])
   ; rel_only_a_1(_, _, _) = Val,
     Ret = string.append_list(["only_a_1(","RelHandle",",","Event",",","Inst",")"])
   ; rel_neg(_, _, _) = Val,
     Ret = string.append_list(["neg(","RelHandle",",","Event",",","RelHandle0",")"])
   ; rel_always_a_1(_, _, _) = Val,
     Ret = string.append_list(["always_a_1(","RelHandle",",","Indiv",",","Event",")"])
   ; rel_never_a_1(_, _, _) = Val,
     Ret = string.append_list(["never_a_1(","RelHandle",",","Indiv",",","RelHandle0",")"])
   ; rel_therefore_a_1(_, _, _) = Val,
     Ret = string.append_list(["therefore_a_1(","RelHandle",",","Indiv",",","RelHandle0",")"])
   ; rel_rich_a_in(_, _, _, _) = Val,
     Ret = string.append_list(["rich_a_in(","RelHandle",",","Event",",","Inst",",","Indiv",")"])
   ; rel_more_comp(_, _, _, _) = Val,
     Ret = string.append_list(["more_comp(","RelHandle",",","E1",",","E2",",","Inst",")"])
   ; rel_named(_, _, _) = Val,
     Ret = string.append_list(["named(","RelHandle",",","Inst",",","Carg",")"])
   ; rel_card(_, _, _, _) = Val,
     Ret = string.append_list(["card(","RelHandle",",","Event",",","Inst",",","Carg",")"])
   ; rel_be_v_id(_, _, _, _) = Val,
     Ret = string.append_list(["be_v_id(","RelHandle",",","Event",",","A",",","B",")"])
   ; rel_chase_v_1(_, _, _, _) = Val,
     Ret = string.append_list(["chase_v_1(","RelHandle",",","Event",",","A",",","B",")"])
   ; rel_kill_v_1(_, _, _, _) = Val,
     Ret = string.append_list(["kill_v_1(","RelHandle",",","Event",",","A",",","B",")"])
   ; rel_hate_v_1(_, _, _, _) = Val,
     Ret = string.append_list(["hate_v_1(","RelHandle",",","Event",",","A",",","B",")"])
   ; rel_poss(_, _, _, _) = Val,
     Ret = string.append_list(["poss(","RelHandle",",","Event",",","A",",","B",")"])
   ; rel_in_p_loc(_, _, _, _) = Val,
     Ret = string.append_list(["in_p_loc(","RelHandle",",","Event1",",","Event2",",","Inst",")"])
   ; rel_compound(_, _, _, _) = Val,
     Ret = string.append_list(["compound(","RelHandle",",","Event",",","A",",","B",")"])
   ; rel_implicit_conj(_, _, _, _) = Val,
     Ret = string.append_list(["implicit_conj(","RelHandle",",","A",",","B",",","C",")"])
   ; rel_and_c_e(_, _, _, _) = Val,
     Ret = string.append_list(["and_c_e(","RelHandle",",","E1",",","E2",",","E3",")"])
   ; rel_and_c_x(_, _, _, _) = Val,
     Ret = string.append_list(["and_c_x(","RelHandle",",","X1",",","X2",",","X3",")"])
   ; rel_people_n_of(_, _, _) = Val,
     Ret = string.append_list(["people_n_of(","RelHandle",",","Inst",",","Indiv",")"])
   ; rel_victim_n_of(_, _, _) = Val,
     Ret = string.append_list(["victim_n_of(","RelHandle",",","Inst",",","Indiv",")"])
   ; rel_aunt_n_of(_, _, _) = Val,
     Ret = string.append_list(["aunt_n_of(","RelHandle",",","Inst",",","Indiv",")"])
   ; rel_butler_n_1(_, _) = Val,
     Ret = string.append_list(["butler_n_1(","RelHandle",",","Inst",")"])
   ; rel_killer_n_1(_, _) = Val,
     Ret = string.append_list(["killer_n_1(","RelHandle",",","Inst",")"])
   ; rel_therein_p_dir(_, _, _) = Val,
     Ret = string.append_list(["therein_p_dir(","RelHandle",",","E1",",","E2",")"])
   ; rel_except_p(_, _, _, _) = Val,
     Ret = string.append_list(["except_p(","RelHandle",",","Event",",","A",",","B",")"])
   ; rel_colon_p_namely(_, _, _, _) = Val,
     Ret = string.append_list(["colon_p_namely(","RelHandle",",","Event",",","RelHandle0",",","RelHandle1",")"])
   ; error("impossible1")).

:- func rel_handle(mrs_rel_t) = mrs_rel_handle.
:- mode rel_handle(in) = out is det.
rel_handle(Val) = Ret :-
   (rel_unknown(RelHandle,_,_) = Val,
    Ret = RelHandle
  ; rel_person(RelHandle,_) = Val,
    Ret = RelHandle
  ; rel_pron(RelHandle,_) = Val,
    Ret = RelHandle
  ; rel_generic_entity(RelHandle,_) = Val,
    Ret = RelHandle
  ; rel_proper_q(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_some_q(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_every_q(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_udef_q(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_the_q(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_a_q(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_def_explicit_q(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_pronoun_q(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_no_q(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_named(RelHandle, _, _) = Val,
    Ret = RelHandle
  ; rel_card(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_be_v_id(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_chase_v_1(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_kill_v_1(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_hate_v_1(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_poss(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_live_v_1(RelHandle, _, _) = Val,
    Ret = RelHandle
  ; rel_only_a_1(RelHandle, _, _) = Val,
    Ret = RelHandle
  ; rel_neg(RelHandle, _, _) = Val,
    Ret = RelHandle
  ; rel_always_a_1(RelHandle, _, _) = Val,
    Ret = RelHandle
  ; rel_never_a_1(RelHandle, _, _) = Val,
    Ret = RelHandle
  ; rel_therefore_a_1(RelHandle, _, _) = Val,
    Ret = RelHandle
  ; rel_rich_a_in(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_more_comp(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_in_p_loc(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_compound(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_implicit_conj(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_and_c_e(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_and_c_x(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_people_n_of(RelHandle, _, _) = Val,
    Ret = RelHandle
  ; rel_victim_n_of(RelHandle, _, _) = Val,
    Ret = RelHandle
  ; rel_aunt_n_of(RelHandle, _, _) = Val,
    Ret = RelHandle
  ; rel_butler_n_1(RelHandle, _) = Val,
    Ret = RelHandle
  ; rel_killer_n_1(RelHandle, _) = Val,
    Ret = RelHandle
  ; rel_therein_p_dir(RelHandle, _, _) = Val,
    Ret = RelHandle
  ; rel_except_p(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; rel_colon_p_namely(RelHandle, _, _, _) = Val,
    Ret = RelHandle
  ; error("impossible2")).

:- func rel_handle_name(mrs_rel_t) = string.
:- mode rel_handle_name(in) = out is det.
rel_handle_name(Val) = Ret :- Ret = to_string(rel_handle(Val)).

:- func rel_handle_lhs_name(mrs_rel_handle) = string.
:- mode rel_handle_lhs_name(in) = out is det.
rel_handle_lhs_name(Val) = Ret :-
   mrs_rel_handle(H) = Val,
   Ret = to_string(H).

:- func rel_handle_rhs_name(mrs_rel_handle) = string.
:- mode rel_handle_rhs_name(in) = out is det.
rel_handle_rhs_name(Val) = Ret :- 
   Ret = string.append_list(["pred_",rel_handle_lhs_name(Val)]).

:- func rel_pred_orig_name(mrs_rel_t) = string.
:- mode rel_pred_orig_name(in) = out is det.
rel_pred_orig_name(Val) = Ret :- 
   (rel_unknown(_, _, _) = Val,
    Ret = string.append_list(["pred_unknown(unknown)"])
  ; rel_person(_, _) = Val,
    Ret = string.append_list(["pred_person(person)"])
  ; rel_pron(_, _) = Val,
    Ret = string.append_list(["pred_pron(pron)"])
  ; rel_generic_entity(_, _) = Val,
    Ret = string.append_list(["pred_generic_entity(generic_entity)"])
  ; rel_proper_q(_, _, _, _) = Val,
    Ret = string.append_list(["pred_proper_q(proper_q)"])
  ; rel_some_q(_, _, _, _) = Val,
    Ret = string.append_list(["pred_some_q(some_q)"])
  ; rel_every_q(_, _, _, _) = Val,
    Ret = string.append_list(["pred_every_q(every_q)"])
  ; rel_udef_q(_, _, _, _) = Val,
    Ret = string.append_list(["pred_udef_q(udef_q)"])
  ; rel_the_q(_, _, _, _) = Val,
    Ret = string.append_list(["pred_the_q(the_q)"])
  ; rel_a_q(_, _, _, _) = Val,
    Ret = string.append_list(["pred_a_q(a_q)"])
  ; rel_def_explicit_q(_, _, _, _) = Val,
    Ret = string.append_list(["pred_def_explicit_q(def_explicit_q)"])
  ; rel_pronoun_q(_, _, _, _) = Val,
    Ret = string.append_list(["pred_pronoun_q(pronoun_q)"])
  ; rel_no_q(_, _, _, _) = Val,
    Ret = string.append_list(["pred_no_q(no_q)"])
  ; rel_live_v_1(_, _, _) = Val,
    Ret = string.append_list(["pred_live_v_1(live_v_1)"])
  ; rel_only_a_1(_, _, _) = Val,
    Ret = string.append_list(["pred_only_a_1(only_a_1)"])
  ; rel_neg(_, _, _) = Val,
    Ret = string.append_list(["pred_neg(neg)"])
  ; rel_always_a_1(_, _, _) = Val,
    Ret = string.append_list(["pred_always_a_1(always_a_1)"])
  ; rel_never_a_1(_, _, _) = Val,
    Ret = string.append_list(["pred_never_a_1(never_a_1)"])
  ; rel_therefore_a_1(_, _, _) = Val,
    Ret = string.append_list(["pred_therefore_a_1(therefore_a_1)"])
  ; rel_rich_a_in(_, _, _, _) = Val,
    Ret = string.append_list(["pred_rich_a_in(rich_a_in)"])
  ; rel_more_comp(_, _, _, _) = Val,
    Ret = string.append_list(["pred_more_comp(more_comp)"])
  ; rel_named(_, _, _) = Val,
    Ret = string.append_list(["pred_named(named)"])
  ; rel_card(_, _, _, _) = Val,
    Ret = string.append_list(["pred_card(card)"])
  ; rel_be_v_id(_, _, _, _) = Val,
    Ret = string.append_list(["pred_be_v_id(be_v_id)"])
  ; rel_chase_v_1(_, _, _, _) = Val,
    Ret = string.append_list(["pred_chase_v_1(chase_v_1)"])
  ; rel_kill_v_1(_, _, _, _) = Val,
    Ret = string.append_list(["pred_kill_v_1(kill_v_1)"])
  ; rel_hate_v_1(_, _, _, _) = Val,
    Ret = string.append_list(["pred_hate_v_1(hate_v_1)"])
  ; rel_poss(_, _, _, _) = Val,
    Ret = string.append_list(["pred_poss(poss)"])
  ; rel_in_p_loc(_, _, _, _) = Val,
    Ret = string.append_list(["pred_in_p_loc(in_p_loc)"])
  ; rel_compound(_, _, _, _) = Val,
    Ret = string.append_list(["pred_compound(compound)"])
  ; rel_implicit_conj(_, _, _, _) = Val,
    Ret = string.append_list(["pred_implicit_conj(implicit_conj)"])
  ; rel_and_c_e(_, _, _, _) = Val,
    Ret = string.append_list(["pred_and_c_e(and_c_e)"])
  ; rel_and_c_x(_, _, _, _) = Val,
    Ret = string.append_list(["pred_and_c_x(and_c_x)"])
  ; rel_people_n_of(_, _, _) = Val,
    Ret = string.append_list(["pred_people_n_of(people_n_of)"])
  ; rel_victim_n_of(_, _, _) = Val,
    Ret = string.append_list(["pred_victim_n_of(victim_n_of)"])
  ; rel_aunt_n_of(_, _, _) = Val,
    Ret = string.append_list(["pred_aunt_n_of(aunt_n_of)"])
  ; rel_butler_n_1(_, _) = Val,
    Ret = string.append_list(["pred_butler_n_1(butler_n_1)"])
  ; rel_killer_n_1(_, _) = Val,
    Ret = string.append_list(["pred_killer_n_1(killer_n_1)"])
  ; rel_therein_p_dir(_, _, _) = Val,
    Ret = string.append_list(["pred_therein_p_dir(therein_p_dir)"])
  ; rel_except_p(_, _, _, _) = Val,
    Ret = string.append_list(["pred_except_p(except_p)"])
  ; rel_colon_p_namely(_, _, _, _) = Val,
    Ret = string.append_list(["pred_colon_p_namely(colon_p_namely)"])
  ; error("impossible3")).

:- func rel_to_decl_string(mrs_rel_t) = string.
:- mode rel_to_decl_string(in) = out is det.
rel_to_decl_string(Val) = Ret :-
    (rel_unknown(_, _, _) = Val,
     Ret = string.append_list([":- pred unknown(mrs_rel_handle, mrs_unknown, mrs_event).\n",
                               ":- mode unknown(out, out, out) is nondet.\n"])
   ; rel_person(_, _) = Val,
     Ret = string.append_list([":- pred person(mrs_rel_handle, mrs_inst).\n",
                               ":- mode person(out, out) is nondet.\n"])
   ; rel_pron(_, _) = Val,
     Ret = string.append_list([":- pred pron(mrs_rel_handle, mrs_inst).\n",
                               ":- mode pron(out, out) is nondet.\n"])
   ; rel_generic_entity(_, _) = Val,
     Ret = string.append_list([":- pred generic_entity(mrs_rel_handle, mrs_inst).\n",
                               ":- mode generic_entity(out, out) is nondet.\n"])
   ; rel_proper_q(_, _, _, _) = Val,
     Ret = string.append_list([":- pred proper_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle).\n",
                               ":- mode proper_q(out, out, out, out) is nondet.\n"])
   ; rel_some_q(_, _, _, _) = Val,
     Ret = string.append_list([":- pred some_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle).\n",
                               ":- mode some_q(out, out, out, out) is nondet.\n"])
   ; rel_every_q(_, _, _, _) = Val,
     Ret = string.append_list([":- pred every_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle).\n",
                               ":- mode every_q(out, out, out, out) is nondet.\n"])
   ; rel_udef_q(_, _, _, _) = Val,
     Ret = string.append_list([":- pred udef_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle).\n",
                               ":- mode udef_q(out, out, out, out) is nondet.\n"])
   ; rel_the_q(_, _, _, _) = Val,
     Ret = string.append_list([":- pred the_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle).\n",
                               ":- mode the_q(out, out, out, out) is nondet.\n"])
   ; rel_a_q(_, _, _, _) = Val,
     Ret = string.append_list([":- pred a_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle).\n",
                               ":- mode a_q(out, out, out, out) is nondet.\n"])
   ; rel_def_explicit_q(_, _, _, _) = Val,
     Ret = string.append_list([":- pred def_explicit_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle).\n",
                               ":- mode def_explicit_q(out, out, out, out) is nondet.\n"])
   ; rel_pronoun_q(_, _, _, _) = Val,
     Ret = string.append_list([":- pred pronoun_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle).\n",
                               ":- mode pronoun_q(out, out, out, out) is nondet.\n"])
   ; rel_no_q(_, _, _, _) = Val,
     Ret = string.append_list([":- pred no_q(mrs_rel_handle, mrs_inst, mrs_rstr_handle, mrs_body_handle).\n",
                               ":- mode no_q(out, out, out, out) is nondet.\n"])
   ; rel_live_v_1(_, _, _) = Val,
     Ret = string.append_list([":- pred live_v_1(mrs_rel_handle, mrs_event, mrs_inst).\n",
                               ":- mode live_v_1(out,out,out) is nondet.\n"])
   ; rel_only_a_1(_, _, _) = Val,
     Ret = string.append_list([":- pred only_a_1(mrs_rel_handle, mrs_event, mrs_inst).\n",
                               ":- mode only_a_1(out,out,out) is nondet.\n"])
   ; rel_neg(_, _, _) = Val,
     Ret = string.append_list([":- pred neg(mrs_rel_handle, mrs_event, mrs_rel_handle).\n",
                               ":- mode neg(out,out,out) is nondet.\n"])
   ; rel_always_a_1(_, _, _) = Val,
     Ret = string.append_list([":- pred always_a_1(mrs_rel_handle, mrs_indiv, mrs_event).\n",
                               ":- mode always_a_1(out,out,out) is nondet.\n"])
   ; rel_never_a_1(_, _, _) = Val,
     Ret = string.append_list([":- pred never_a_1(mrs_rel_handle, mrs_indiv, mrs_rel_handle).\n",
                               ":- mode never_a_1(out,out,out) is nondet.\n"])
   ; rel_therefore_a_1(_, _, _) = Val,
     Ret = string.append_list([":- pred therefore_a_1(mrs_rel_handle, mrs_indiv, mrs_rel_handle).\n",
                               ":- mode therefore_a_1(out,out,out) is nondet.\n"])
   ; rel_rich_a_in(_, _, _, _) = Val,
     Ret = string.append_list([":- pred rich_a_in(mrs_rel_handle, mrs_event, mrs_inst, mrs_indiv).\n",
                               ":- mode rich_a_in(out,out,out,out) is nondet.\n"])
   ; rel_more_comp(_, _, _, _) = Val,
     Ret = string.append_list([":- pred more_comp(mrs_rel_handle, mrs_event, mrs_event, mrs_inst).\n",
                               ":- mode more_comp(out,out,out,out) is nondet.\n"])
   ; rel_named(_, _, _) = Val,
     Ret = string.append_list([":- pred named(mrs_rel_handle, mrs_inst, mrs_carg).\n",
                               ":- mode named(out,out,out) is nondet.\n"])
   ; rel_card(_, _, _, _) = Val,
     Ret = string.append_list([":- pred card(mrs_rel_handle, mrs_event, mrs_inst, mrs_carg).\n",
                               ":- mode card(out,out,out,out) is nondet.\n"])
   ; rel_be_v_id(_, _, _, _) = Val,
     Ret = string.append_list([":- pred be_v_id(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst).\n",
                               ":- mode be_v_id(out,out,out,out) is nondet.\n"])
   ; rel_chase_v_1(_, _, _, _) = Val,
     Ret = string.append_list([":- pred chase_v_1(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst).\n",
                               ":- mode chase_v_1(out,out,out,out) is nondet.\n"])
   ; rel_kill_v_1(_, _, _, _) = Val,
     Ret = string.append_list([":- pred kill_v_1(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst).\n",
                               ":- mode kill_v_1(out,out,out,out) is nondet.\n"])
   ; rel_hate_v_1(_, _, _, _) = Val,
     Ret = string.append_list([":- pred hate_v_1(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst).\n",
                               ":- mode hate_v_1(out,out,out,out) is nondet.\n"])
   ; rel_poss(_, _, _, _) = Val,
     Ret = string.append_list([":- pred poss(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst).\n",
                               ":- mode poss(out,out,out,out) is nondet.\n"])
   ; rel_in_p_loc(_, _, _, _) = Val,
     Ret = string.append_list([":- pred in_p_loc(mrs_rel_handle, mrs_event, mrs_event, mrs_inst).\n",
                               ":- mode in_p_loc(out,out,out,out) is nondet.\n"])
   ; rel_compound(_, _, _, _) = Val,
     Ret = string.append_list([":- pred compound(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst).\n",
                               ":- mode compound(out,out,out,out) is nondet.\n"])
   ; rel_implicit_conj(_, _, _, _) = Val,
     Ret = string.append_list([":- pred implicit_conj(mrs_rel_handle, mrs_inst, mrs_inst, mrs_inst).\n",
                               ":- mode implicit_conj(out,out,out,out) is nondet.\n"])
   ; rel_and_c_e(_, _, _, _) = Val,
     Ret = string.append_list([":- pred and_c_e(mrs_rel_handle, mrs_event, mrs_event, mrs_event).\n",
                               ":- mode and_c_e(out,out,out,out) is nondet.\n"])
   ; rel_and_c_x(_, _, _, _) = Val,
     Ret = string.append_list([":- pred and_c_x(mrs_rel_handle, mrs_inst, mrs_inst, mrs_inst).\n",
                               ":- mode and_c_x(out,out,out,out) is nondet.\n"])
   ; rel_people_n_of(_, _, _) = Val,
     Ret = string.append_list([":- pred people_n_of(mrs_rel_handle, mrs_inst, mrs_indiv).\n",
                               ":- mode people_n_of(out,out,out) is nondet.\n"])
   ; rel_victim_n_of(_, _, _) = Val,
     Ret = string.append_list([":- pred victim_n_of(mrs_rel_handle, mrs_inst, mrs_indiv).\n",
                               ":- mode victim_n_of(out,out,out) is nondet.\n"])
   ; rel_aunt_n_of(_, _, _) = Val,
     Ret = string.append_list([":- pred aunt_n_of(mrs_rel_handle, mrs_inst, mrs_indiv).\n",
                               ":- mode aunt_n_of(out,out,out) is nondet.\n"])
   ; rel_butler_n_1(_, _) = Val,
     Ret = string.append_list([":- pred butler_n_1(mrs_rel_handle, mrs_inst).\n",
                               ":- mode butler_n_1(out,out) is nondet.\n"])
   ; rel_killer_n_1(_, _) = Val,
     Ret = string.append_list([":- pred killer_n_1(mrs_rel_handle, mrs_inst).\n",
                               ":- mode killer_n_1(out,out) is nondet.\n"])
   ; rel_therein_p_dir(_, _, _) = Val,
     Ret = string.append_list([":- pred therein_p_dir(mrs_rel_handle, mrs_event, mrs_event).\n",
                               ":- mode therein_p_dir(out,out,out) is nondet.\n"])
   ; rel_except_p(_, _, _, _) = Val,
     Ret = string.append_list([":- pred except_p(mrs_rel_handle, mrs_event, mrs_inst, mrs_inst).\n",
                               ":- mode except_p(out,out,out,out) is nondet.\n"])
   ; rel_colon_p_namely(_, _, _, _) = Val,
     Ret = string.append_list([":- pred colon_p_namely(mrs_rel_handle, mrs_event, mrs_rel_handle, mrs_rel_handle).\n",
                               ":- mode colon_p_namely(out,out,out,out) is nondet.\n"])
   ; error("impossible4")).


:- instance mrs_print(mrs_rel_t) where [
  func(to_string/1) is rel_to_string
].

:- instance mrs_print(mrs_rel_qeq_t) where [
  to_string(mrs_rel_qeq(A,B)) = string.append_list(["pair(",to_string(A),",",to_string(B)])
].                                               

:- instance mrs_print(mrs_hcons) where [
  to_string(hcons(L)) = string.append_list(["[",string.join_list(",",list.map(to_string,L)),"]"])
].

:- func qeq_lhs(mrs_rel_qeq_t) = string.
:- mode qeq_lhs(in) = out is det.
qeq_lhs(Qeq) = Ret :-
  mrs_rel_qeq(Lhs,_) = Qeq,
  Ret = to_string(Lhs).

:- func qeq_rhs(mrs_rel_qeq_t) = string.
:- mode qeq_rhs(in) = out is det.
qeq_rhs(Qeq) = Ret :-
  mrs_rel_qeq(_,Rhs) = Qeq,
  Ret = string.append_list(["multi_map.lookup(handleMapBase,",to_string(Rhs),")"]).

:- func mkTuple(mrs_rel_t) = string.
:- mode mkTuple(in) = out is det.
mkTuple(Rel) = Ret :- Ret = string.append_list(["{",rel_handle_name(Rel),",\"",rel_to_call(Rel),"\"",",\"",rel_to_decl_string(Rel),"\",",rel_pred_orig_name(Rel),"}"]).

:- func mkHandleMap(list(mrs_rel_t),mrs_hcons) = string.
:- mode mkHandleMap(in,in) = out is det.
mkHandleMap(Rels,Hcons) = Ret :- 
  hcons(Qlist) = Hcons,
  L1 = list.map(to_string, Rels),
  Args1 = string.join_list(",",list.map(rel_handle_name,Rels)),
  Args2 = string.join_list(",",list.map(mkTuple,Rels)),
  L2decl = [":- func handleMapBase = multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}).\n"],
  L2 = ["handleMapBase = list.foldl_corresponding(func(A,B,Cin) = Cout is det :- Cout = multi_map.add(Cin,A,B),[",Args1,"],[",Args2,"], multi_map.init).\n"],
  Args1extra = string.join_list(",",list.map(qeq_lhs,Qlist)),
  Args2extra = string.join_list(",",list.map(qeq_rhs,Qlist)),
  L3 = ["handleMap = list.foldl_corresponding(func(A,B,Cin) = Cout is det :- Cout = list.foldl(func(BB,Cin0) = Cout0 is det :- Cout0 = multi_map.add(Cin0,A,BB),B,Cin),[",Args1extra,"],[",Args2extra,"], handleMapBase).\n"],
  Ret = string.append_list(list.condense([L1,L2decl,L2,L3])).

:- instance mrs_print(mrs_psoa) where [
  to_string(psoa(H,E,Rels,Hcons)) = 
    string.append_list([mkHandleMap(Rels,Hcons),
	                "root = psoa_post(mrs_rel_handle(",
		        to_string(H),
		        "),",
		        to_string(E),
		        ",handleMap).\n"
			])
].                        

relationDeclarations(Rels) = Ret :-
    L1p = set.to_sorted_list(set.list_to_set(list.map(rel_to_decl_string, Rels))),
    Ret = string.join_list("\n",L1p).
