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
:- import_module set.
:- import_module string.
:- import_module multi_map.
:- import_module map.
:- import_module assoc_list.
:- import_module pair.
:- import_module require.
:- import_module unsafe.
:- import_module pretty_printer.
:- import_module int.
:- import_module term.
:- import_module varset.
:- import_module term_io.
:- import_module var_utils.

:- import_module sentence_collectArguments.
:- import_module sentence_collectArgRefs.
:- import_module sentence_unpackRelation.

:- import_module sentence_vars_event0.

:- pred invertArgMap(multi_map(mrs_types, mrs_rel_handle),
                     multi_map(mrs_rel_handle, mrs_types)).
:- mode invertArgMap(in, out).
invertArgMap(ArgRefMap, ArgRevMap) :-
  map.foldl(pred(K::in,L::in,RevMapIn::in,RevMapOut::out) is det :-
              list.foldl(pred(V::in,RevMapIn0::in,RevMapOut0::out) is det :- 
	                   multi_map.add(V,K,RevMapIn0,RevMapOut0),
			 L, RevMapIn,RevMapOut),
            ArgRefMap,multi_map.init,ArgRevMap).

:- pred createMaps(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                   multi_map(mrs_types, mrs_rel_handle),
                   multi_map(mrs_types, mrs_rel_handle),
		   multi_map(mrs_rel_handle, mrs_types)).
:- mode createMaps(in,out,out,out) is det.
createMaps(RelMap,ArgMap,ArgRefMap,ArgRevMap) :-
  multi_map.values(RelMap,RelMapValues0),
  RelMapValuesSet = set.from_list(RelMapValues0),
  RelMapValues = set.to_sorted_list(RelMapValuesSet),
  list.foldl(pred({RelHandle0,_,_,Pred0}::in,ArgMapIn0::in,ArgMapOut0::out) is det :-
              collectArguments(RelMap,RelHandle0,Pred0,ArgMapIn0,ArgMapOut0),
             RelMapValues,multi_map.init,ArgMap),
  list.foldl(pred({RelHandle0,_,_,Pred0}::in,ArgRefMapIn0::in,ArgRefMapOut0::out) is det :- collectArgRefs(RelMap,RelHandle0,Pred0,ArgRefMapIn0,ArgRefMapOut0),
             RelMapValues,multi_map.init,ArgRefMap),
  invertArgMap(ArgRefMap,ArgRevMap).

:- pred rstr_keys(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}), multi_map(mrs_types, mrs_rel_handle), int, set(mrs_rel_handle)).
:- mode rstr_keys(in, in, in, out) is det.
rstr_keys(RelMap, ArgRefMap, SentencePos, RstrSet) :-
  KL = multi_map.keys(ArgRefMap),
  list.foldl(pred(AT::in,SetIn::in,SetOut::out) is det :-
    (if (wrap_rstr_handle(Rstr) = AT,
         mrs_rstr_handle(Handle) = Rstr,
         mrs_handle(HandleStr) = Handle,
         multi_map.lookup(ArgRefMap,AT,VL),
         TargetStr = "s" ++ string.int_to_string(SentencePos),
         string.right(HandleStr,string.length(TargetStr)) = TargetStr,
         list.length(VL,Len),
         Len > 0) then
        RH = mrs_rel_handle(Handle),
         (if multi_map.contains(RelMap,RH) then
           multi_map.lookup(RelMap,mrs_rel_handle(Handle),L),
           LL = list.map(func({RelHandle0,_,_,_}) = Ret is det :- Ret = RelHandle0, L),
           list.foldl(set.insert,LL,SetIn,SetOut)
        else
           SetOut = SetIn)
     else
       SetOut = SetIn),
    KL,set.init,RstrSet).

:- pred body_keys(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}), multi_map(mrs_types, mrs_rel_handle), int, set(mrs_rel_handle)).
:- mode body_keys(in, in, in, out) is det.
body_keys(RelMap, ArgRefMap, SentencePos, BodySet) :-
  KL = multi_map.keys(ArgRefMap),
  list.foldl(pred(AT::in,SetIn::in,SetOut::out) is det :- 
    (if (wrap_body_handle(Body) = AT,
         mrs_body_handle(Handle) = Body,
         mrs_handle(HandleStr) = Handle,
         multi_map.lookup(ArgRefMap,AT,VL),
         TargetStr = "s" ++ string.int_to_string(SentencePos),
         string.right(HandleStr,string.length(TargetStr)) = TargetStr,
         list.length(VL,Len),
         Len > 0) then
	 RH = mrs_rel_handle(Handle),
         (if multi_map.contains(RelMap,RH) then
           multi_map.lookup(RelMap,mrs_rel_handle(Handle),L),
           LL = list.map(func({RelHandle0,_,_,_}) = Ret is det :- Ret = RelHandle0, L),
           list.foldl(set.insert,LL,SetIn,SetOut)
	 else
           SetOut = SetIn)
     else
       SetOut = SetIn),
    KL,set.init,BodySet).

:- pred write_rel(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                  multi_map(mrs_types, mrs_rel_handle),
                  map(mrs_rel_handle, list(string)),
		  set(mrs_rel_handle),
		  term.context,
		  mrs_rel_handle,
		  set(string),set(string),
                  varset(T),varset(T),
                  varset(T),varset(T),
		  io,io).
:- mode write_rel(in,in,in,in,in,in, in,out,in,out,in,out,di,uo).
write_rel(RelMap,ArgMap,VarMap,ExcludeSet,Context,RelHandle,
          SignaturesIn,SignaturesOut,
          VarSetLocalIn,VarSetLocalOut,
          VarSetIn,VarSetOut,
          !IO) :-
  (if multi_map.contains(RelMap,RelHandle) then
    (map.lookup(RelMap,RelHandle,LL),
     Set = set.from_list(LL),
     SL = set.to_sorted_list(Set),
     list.length(SL,Len),
     list.foldl5(pred({RelHandle0,_,_,Pred0}::in,
                      PosIn0::in,PosOut0::out,
		      SignaturesIn0::in,SignaturesOut0::out,
		      VarSetLocalIn0::in,VarSetLocalOut0::out,
		      VarSetIn0::in,VarSetOut0::out,
		      IoIn0::di,IoOut0::uo) is det :- 
       (sentence_unpackRelation.unpackRelation(RelMap,ArgMap,VarMap,ExcludeSet,RelHandle0,Pred0,SignaturesIn0,SignaturesOut0,[],Calls0,varset.init,VarSetLocalOut0,VarSetIn0,VarSetOut0),
        mrs_rel_handle(mrs_handle(TermName)) = RelHandle0,
	(if Len = 1 then
	  VarName = TermName
	else
	  VarName = TermName ++ "_" ++ string.int_to_string(PosIn0)),

        list.foldl(pred(Call0::in,IoIn1::di,IoOut1::uo) is det :- 
         (VarNames = var_utils.collectInstanceVarNames(VarSetLocalOut0),
	  VLX = var_utils.collectGlobalVars(VarSetOut0,VarNames),
	  var_list_to_term_list(VLX,ArgTerms),
	  term_io.write_term(VarSetOut0,term.functor(atom(":-"),[term.functor(term.atom(VarName),ArgTerms,Context),Call0],Context),IoIn1,Io0),
           io.print(".",Io0,Io1),
           io.nl(Io1,IoOut1)),
          Calls0,IoIn0,IoOut0),
	PosOut0 = PosIn0 + 1),
       SL,
         0, Count,
         SignaturesIn, SignaturesOut,
	 VarSetLocalIn, VarSetLocalOut,
	 VarSetIn, VarSetOut,
	 !IO))
  else
    VarSetLocalOut = VarSetLocalIn,
    SignaturesOut = SignaturesIn,
    VarSetOut = VarSetIn).

:- func expandList(list(term(T)),term.context) = term(T) is det.
expandList(L,Context) = Ret :- 
  list.length(L,Len),
  (if Len >= 2 then
     Ret = term.functor(term.atom(","),[det_head(L),expandList(det_tail(L),Context)],Context)
   else
     Ret = det_head(L)).

:- pred newVar(string,var(T),varset(T),varset(T)).
:- mode newVar(in,out,in,out) is det.
newVar(VarName,Var,VarSetIn,VarSetOut) :-
  if list.find_first_match(pred(VarTest::in) is semidet :- varset.search_name(VarSetIn,VarTest,VarName),varset.vars(VarSetIn),MatchedVar) then 
    Var = MatchedVar,
    VarSetOut = VarSetIn
  else
    varset.new_named_var(VarName,Var,VarSetIn,VarSetOut).

:- pred mkCall(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
               mrs_rel_handle,
	       preds,
	       int,
	       term.context,
	       varset,
	       varset,
	       varset,
	       varset,
	       term(generic)).
:- mode mkCall(in,in,in,in,in,in,out,in,out,out) is det.
:- pragma promise_pure(mkCall/10).
mkCall(RelMap,RelHandle,Pred,PosIn,Context,
       VarSetLocalIn,VarSetLocalOut,
       VarSetGlobalIn,VarSetGlobalOut,
       Term) :-
  collectArgRefs(RelMap,RelHandle,Pred,multi_map.init,TmpArgRefMap),
  invertArgMap(TmpArgRefMap,TmpArgRevMap),
  multi_map.lookup(TmpArgRevMap,RelHandle,Args),
  L = list.filter_map(func(Arg) = Inst is semidet :- wrap_inst(mrs_inst(Inst)) = Arg, Args),
  sort(L,LS),
  list.foldl3(pred(VarName::in,
                   VarSetLocalIn0::in,VarSetLocalOut0::out,
		   VarSetGlobalIn0::in,VarSetGlobalOut0::out,
		   Lin::in,Lout::out) is det :- 
    (SymName = string.capitalize_first(VarName),
     newVar(SymName,Var,VarSetLocalIn0,VarSetLocalOut0),
     newVar(SymName,GlobalVar,VarSetGlobalIn0,VarSetGlobalOut0),
     Lout = list.cons(Var,Lin)),
    LS, VarSetLocalIn,VarSetLocalOut,VarSetGlobalIn,VarSetGlobalOut,[],RVL),
  list.reverse(RVL,VL),
  mrs_rel_handle(mrs_handle(RelName)) = RelHandle,
  FuncName = RelName ++ "_" ++ string.int_to_string(PosIn),
  term.var_list_to_term_list(VL, ArgTerms),
  Term = term.functor(atom(FuncName),ArgTerms,Context).

:- pred quantifiers(mrs_rel_handle).
:- mode quantifiers(out) is nondet.
quantifiers(RelHandle) :- 
  proper_q(RelHandle,Inst0,mrs_rstr_handle(RstrHandle0),mrs_body_handle(BodyHandle0))
  ; udef_q(RelHandle,Inst0,mrs_rstr_handle(RstrHandle0),mrs_body_handle(BodyHandle0))
  ; some_q(RelHandle,Inst0,mrs_rstr_handle(RstrHandle0),mrs_body_handle(BodyHandle0))
  ; the_q(RelHandle,Inst0,mrs_rstr_handle(RstrHandle0),mrs_body_handle(BodyHandle0))
  ; def_explicit_q(RelHandle,Inst0,mrs_rstr_handle(RstrHandle0),mrs_body_handle(BodyHandle0))
  ; a_q(RelHandle,Inst0,mrs_rstr_handle(RstrHandle0),mrs_body_handle(BodyHandle0))
  ; pronoun_q(RelHandle,Inst0,mrs_rstr_handle(RstrHandle0),mrs_body_handle(BodyHandle0))
  ; no_q(RelHandle,Inst0,mrs_rstr_handle(RstrHandle0),mrs_body_handle(BodyHandle0))
  ; every_q(RelHandle,Inst0,mrs_rstr_handle(RstrHandle0),mrs_body_handle(BodyHandle0)).

:- pred misc(mrs_rel_handle).
:- mode misc(out) is nondet.
misc(RelHandle) :-
  be_v_id(RelHandle, Event, Inst0, Inst1)
  ; never_a_1(RelHandle, I, RelHandle0)
  ; more_comp(RelHandle, E1, E2, Inst)
  ; therefore_a_1(RelHandle, I, RelHandle0)
  ; unknown(RelHandle, U, E)
  ; kill_v_1(RelHandle, E, I1, I2).

main(!IO) :-
  SentencePos = 0,
  Sentence = det_index0(sentences.sentences,SentencePos),
  psoa_post(TopHandle,Event,RelMap) = Sentence,
  % map.foldl(pred(K::in, V::in, MapIn::in, MapOut::out) is det :- 
  %  (list.map(pred({RelHandle0,_,_,Pred0}::in,Ret::out) is det :- Ret = {RelHandle0,"","",Pred0},V,L),
  %   map.det_insert(K,L,MapIn,MapOut)),RelMap0,map.init,RelMap),
  createMaps(RelMap,ArgMap,ArgRefMap,ArgRevMap),
  rstr_keys(RelMap, ArgRefMap, SentencePos, RstrSet),
  body_keys(RelMap, ArgRefMap, SentencePos, BodySet),

  solutions(quantifiers, QRHL),
  QSet = set.from_list(QRHL),

  solutions(misc, MRHL),
  MSet = set.from_list(MRHL),

  ExcludeSet0 = set.union(RstrSet,BodySet),
  ExcludeSet1 = set.union(ExcludeSet0, MSet),
  ExcludeSet = set.union(ExcludeSet1,QSet),
  TopExcludeSet = set.union(ExcludeSet,TopSetSingleton),
  RelVals = list.map(func({RelHandle0,_,_,_}) = Ret :- Ret = RelHandle0, multi_map.values(RelMap)),
  RelSet = set.from_list(RelVals),
  SimpleSet = set.difference(RelSet,TopExcludeSet),

  multi_map.lookup(RelMap,TopHandle,LL),
  {RelHandleTop,_,_,_} = det_head(LL),
  set.singleton_set(RelHandleTop,TopSetSingleton),

  Context = term.context_init,

  VarSetIn = varset.init,
  SignaturesIn = set.init,

  map.foldl4(pred(K::in,V::in,
                  SignaturesIn::in,SignaturesOut::out,
                  VarMapIn::in,VarMapOut::out,
		  VarSetIn::in,VarSetOut::out,
                  IoIn::di,IoOut::uo) is det :- 
     (mrs_rel_handle(mrs_handle(Name)) = K,
      varset.new_named_var(Name,GlobalVar,VarSetIn,VarSetTmp),
      VarSetLocal0 = varset.init,
      varset.new_named_var(Name,Var,VarSetLocal0,_),
      VarSetArgs0 = varset.init,
      ValuesSet = set.from_list(V),
      ValuesList = set.to_sorted_list(ValuesSet),
      list.length(ValuesList,Len),
      (if Len > 1 then
        (list.foldl4(pred({RelHandle1,_,_,Pred1}::in,
	                  PosIn1::in,PosOut1::out,
			  TermsIn1::in,TermsOut1::out,
			  VarSetLocalIn1::in,VarSetLocalOut1::out,
			  VarSetGlobalIn1::in,VarSetGlobalOut1::out) is det :-  
		       (mkCall(RelMap,RelHandle1,Pred1,PosIn1,Context,VarSetLocalIn1,VarSetLocalOut1,VarSetGlobalIn1,VarSetGlobalOut1,Term1),
		        TermsOut1 = list.cons(Term1,TermsIn1),
	                PosOut1 = PosIn1 + 1),
                     ValuesList,
		     0, PosCount,
		     [], TermsOut, 
		     VarSetArgs0,VarSetArgs1,
		     VarSetTmp,VarSetOut),
         Term = expandList(reverse(TermsOut),Context),
	 (if det_head(V) = {K,_,_,_} then
           IoOut = IoIn
         else
	   Io0 = IoIn,
	   varset.vars(VarSetArgs1,Vars),
	   var_list_to_term_list(Vars,VarTerms),
	   TermFunc = term.functor(atom(":-"),[term.functor(atom(Name),VarTerms,Context),Term],Context),
           term_io.write_term(VarSetArgs1,TermFunc,Io0,Io1),
	   %Io0 = IoIn,
	   %pretty_printer.write_doc(pretty_printer.format(Term),Io0,Io1),
	   io.print(".",Io1,Io2),
	   io.nl(Io2,IoOut)
	 ),
	 VarMapOut = map.det_insert(VarMapIn,K,var_utils.collectInstanceVarNames(VarSetArgs1)),
	 SignaturesOut = SignaturesIn)
       else 
	({RelHandleTarget,_,_,PredTarget} = det_head(ValuesList),
         write_rel(RelMap,ArgMap,map.init,RelSet,Context,RelHandleTarget,SignaturesIn,SignaturesOut,varset.init,VarSetLocalOut,VarSetIn,VarSetOut,IoIn,IoOut),
	 (if map.contains(VarMapIn,RelHandleTarget) then
	   VarMapOut = VarMapIn
	 else
	   VarMapOut = map.det_insert(VarMapIn,RelHandleTarget,var_utils.collectInstanceVarNames(VarSetLocalOut)))))),
     RelMap,set.init,Signatures0,map.init,VarMap,VarSetIn,VarSet0,!IO),

  list.foldl3(pred(RelHandle::in,
                   SignaturesIn0::in,SignaturesOut0::out,
		   VarSetIn0::in,VarSetOut0::out,
		   IoIn0::di,IoOut0::uo) is det :-
      write_rel(RelMap,ArgMap,VarMap,TopExcludeSet,Context,RelHandle,SignaturesIn0,SignaturesOut0,varset.init,VarSetLocalOut0,VarSetIn0,VarSetOut0,IoIn0,IoOut0),
    set.to_sorted_list(ExcludeSet),
    Signatures0,Signatures1,
    VarSet0,VarSet1,
    !IO),
  write_rel(RelMap,ArgMap,VarMap,ExcludeSet,Context,RelHandleTop,Signatures1,Signatures2,varset.init,VarSetLocal1,VarSet1,VarSet2,!IO),

  map.foldl(pred(K::in,V::in,TermsIn::in,TermsOut::out) is det :- 
     (ValuesSet = set.from_list(V),
      ValuesList = set.to_sorted_list(ValuesSet),
      list.length(ValuesList,Len),
      {RelTarget,_,_,_} = det_head(V),
      (if K = RelTarget, Len > 1 then
         TermsOut = TermsIn
       else
	 if map.contains(VarMap,K) then
           map.lookup(VarMap,K,VarNames),
           mrs_rel_handle(mrs_handle(Name)) = K,
           var_list_to_term_list(var_utils.collectGlobalVars(VarSet2,VarNames),Terms),
           Term = term.functor(term.atom(Name),Terms,Context),
           (if set.contains(TermsIn,Term) then
             TermsOut = TermsIn
            else
             TermsOut = set.insert(TermsIn,Term))
	 else
           TermsOut = TermsIn)),
     RelMap,set.init,TermsAll),
  var_list_to_term_list(var_utils.collectGlobalVars(VarSet2,var_utils.collectInstanceVarNames(VarSet2)),VarTerms2),
  term_io.write_term(VarSet0,term.functor(atom(":-"),[term.functor(term.atom("combined"),VarTerms2,Context),expandList(set.to_sorted_list(TermsAll),Context)],Context),!IO),
  io.print(".",!IO),
  io.nl(!IO).


