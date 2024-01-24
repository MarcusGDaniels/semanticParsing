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
:- import_module pair.
:- import_module require.
:- import_module unsafe.
:- import_module pretty_printer.
:- import_module int.
:- import_module term.
:- import_module varset.
:- import_module term_io.

:- import_module sentence_collectArguments.
:- import_module sentence_collectArgRefs.
:- import_module sentence_unpackRelation.

:- pred createMaps(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                   multi_map(mrs_types, mrs_rel_handle),
                   multi_map(mrs_types, mrs_rel_handle)).
:- mode createMaps(in,out,out) is det.
createMaps(RelMap,ArgMap,ArgRefMap) :-
  multi_map.values(RelMap,RelMapValues),
  list.foldl(pred({RelHandle0,_,_,Pred0}::in,ArgMapIn0::in,ArgMapOut0::out) is det :-
              collectArguments(RelMap,RelHandle0,Pred0,ArgMapIn0,ArgMapOut0),
             RelMapValues,multi_map.init,ArgMap),
  list.foldl(pred({RelHandle0,_,_,Pred0}::in,ArgRefMapIn0::in,ArgRefMapOut0::out) is det :- collectArgRefs(RelMap,RelHandle0,Pred0,ArgRefMapIn0,ArgRefMapOut0),
             RelMapValues,multi_map.init,ArgRefMap).

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
		  set(mrs_rel_handle),
		  term.context,
		  mrs_rel_handle,
		  set(string),set(string),
                  varset(T),varset(T),
		  io,io).
:- mode write_rel(in,in,in,in,in,in,out,in,out,di,uo).
write_rel(RelMap,ArgMap,ExcludeSet,Context,RelHandle,SignaturesIn,SignaturesOut,VarSetIn,VarSetOut,!IO) :-
  if multi_map.contains(RelMap,RelHandle) then
    (multi_map.lookup(RelMap,RelHandle,LL),
     list.foldl4(pred({RelHandle0,_,_,Pred0}::in,PosIn0::in,PosOut0::out,SignaturesIn0::in,SignaturesOut0::out,VarSetIn0::in,VarSetOut0::out,IoIn0::di,IoOut0::uo) is det :- 
       (sentence_unpackRelation.unpackRelation(RelMap,ArgMap,ExcludeSet,RelHandle0,Pred0,SignaturesIn0,SignaturesOut0,[],Calls0,VarSetIn0,VarSet0),
        mrs_rel_handle(mrs_handle(TermName)) = RelHandle0,
        varset.new_named_var(TermName ++ "_" ++ string.int_to_string(PosIn0),Lhs,VarSet0,VarSetOut0),
        list.foldl(pred(Call0::in,IoIn1::di,IoOut1::uo) is det :- 
          (term_io.write_term(VarSetOut0,term.functor(atom(":-"),[term.variable(Lhs,Context),Call0],Context),IoIn1,Io0),
           io.print(".",Io0,Io1),
           io.nl(Io1,IoOut1)),
          Calls0,IoIn0,IoOut0),
	PosOut0 = PosIn0 + 1),
       LL, 0, Count, SignaturesIn, SignaturesOut, VarSetIn, VarSetOut, !IO))
  else
    SignaturesOut = SignaturesIn,
    VarSetOut = VarSetIn.

:- func expandList(list(term(T)),term.context) = term(T) is det.
expandList(L,Context) = Ret :- 
  list.length(L,Len),
  (if Len >= 2 then
     Ret = term.functor(term.atom(","),[det_head(L),expandList(det_tail(L),Context)],Context)
   else
     Ret = det_head(L)).

main(!IO) :-
  SentencePos = 0,
  Sentence = det_index0(sentences.sentences,SentencePos),
  psoa_post(TopHandle,Event,RelMap) = Sentence,
  % map.foldl(pred(K::in, V::in, MapIn::in, MapOut::out) is det :- 
  %  (list.map(pred({RelHandle0,_,_,Pred0}::in,Ret::out) is det :- Ret = {RelHandle0,"","",Pred0},V,L),
  %   map.det_insert(K,L,MapIn,MapOut)),RelMap0,map.init,RelMap),
  createMaps(RelMap,ArgMap,ArgRefMap),
  rstr_keys(RelMap, ArgRefMap, SentencePos, RstrSet),
  body_keys(RelMap, ArgRefMap, SentencePos, BodySet),
  ExcludeSet = set.union(RstrSet,BodySet),

  multi_map.lookup(RelMap,TopHandle,LL),
  {RelHandleTop,_,_,_} = det_head(LL),
  set.singleton_set(RelHandleTop,TopSetSingleton),
  TopExcludeSet = set.union(ExcludeSet,TopSetSingleton),

  Context = term.context_init,
 
  list.foldl3(pred(RelHandle::in,SignaturesIn0::in,SignaturesOut0::out,VarSetIn0::in,VarSetOut0::out,IoIn0::di,IoOut0::uo) is det :-
    write_rel(RelMap,ArgMap,TopExcludeSet,Context,RelHandle,SignaturesIn0,SignaturesOut0,VarSetIn0,VarSetOut0,IoIn0,IoOut0),
    set.to_sorted_list(ExcludeSet),set.init,Signatures0,varset.init,VarSet0,!IO),

  write_rel(RelMap,ArgMap,ExcludeSet,Context,RelHandleTop,Signatures0,Signatures1,VarSet0,VarSet1,!IO),
  
  map.foldl2(pred(K::in,V::in,VarSetIn0::in,VarSetOut0::out,IoIn::di,IoOut::uo) is det :- 
     (mrs_rel_handle(mrs_handle(Name)) = K,
      varset.new_named_var(Name,Var,VarSetIn0,VarSetTmp0),
      L = list.map(func({RelHandle1,_,_,_}) = Ret is det :- Ret = RelHandle1,V),
      list.length(L,Len),
      (if Len > 1 then
        (list.foldl3(pred(RelHandle1::in,PosIn1::in,PosOut1::out,TermIn1::in,TermOut1::out,VarSetIn1::in,VarSetOut1::out) is det :-  
                       (mrs_rel_handle(mrs_handle(SubNameN)) = RelHandle1,
                        varset.new_named_var(SubNameN ++ "_" ++ string.int_to_string(PosIn1),VarSub1,VarSetIn1,VarSetOut1),
			list.append(TermIn1,[term.variable(VarSub1,Context)],TermOut1),
	                PosOut1 = PosIn1 + 1),
                     L,
		     0, PosCount,
		     [], TermsOut, 
		     VarSetTmp0, VarSetOut0),
         Term = expandList(TermsOut,Context),
	 (if det_head(L) = K then
           IoOut = IoIn
         else
	   TermFunc = term.functor(atom(":-"),[term.variable(Var,Context),Term],Context),
           term_io.write_term(VarSetOut0,TermFunc,IoIn,Io0),
	   %Io0 = IoIn,
	   %pretty_printer.write_doc(pretty_printer.format(Term),Io0,Io1),
	   io.print(".",Io0,Io1),
	   io.nl(Io1,IoOut))
	 )
       else
	VarSetOut0 = VarSetTmp0,
        IoOut = IoIn)),
     RelMap,VarSet1,VarSetOut,!IO).

