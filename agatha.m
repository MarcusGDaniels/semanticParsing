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
:- import_module varset.
:- import_module term_io.
:- import_module int.

:- import_module sentence_collectArguments.
:- import_module sentence_collectArgRefs.
:- import_module sentence_unpackRelation.

main(!IO) :-
  SentencePos = 0,
  Sentence = det_index0(sentences.sentences,SentencePos),
  psoa_post(TopHandle,Event,RelMap0) = Sentence,
  map.foldl(pred(K::in, V::in, MapIn::in, MapOut::out) is det :- 
    (list.map(pred({RelHandle0,_,_,Pred0}::in,Ret::out) is det :- Ret = {RelHandle0,"","",Pred0},V,L),
     map.det_insert(K,L,MapIn,MapOut)),RelMap0,map.init,RelMap),
  multi_map.values(RelMap,RelMapValuesTrim),
  list.foldl(pred({RelHandle0,_,_,Pred0}::in,ArgMapIn0::in,ArgMapOut0::out) is det :-
              collectArguments(RelMap0,RelHandle0,Pred0,ArgMapIn0,ArgMapOut0),
             RelMapValuesTrim,multi_map.init,ArgMap),
  list.foldl(pred({RelHandle0,_,_,Pred0}::in,ArgRefMapIn0::in,ArgRefMapOut0::out) is det :- collectArgRefs(RelMap,RelHandle0,Pred0,ArgRefMapIn0,ArgRefMapOut0),
             RelMapValuesTrim,multi_map.init,ArgRefMap),
  multi_map.lookup(RelMap,TopHandle,LL),
  {RelHandle,_,_,Pred} = det_head(LL),
  KL = multi_map.keys(ArgRefMap),
  list.filter_map(pred(AT::in,Ret::out) is semidet :- 
    (wrap_rstr_handle(Rstr) = AT,
     mrs_rstr_handle(Handle) = Rstr,
     mrs_handle(HandleStr) = Handle,
     multi_map.lookup(ArgRefMap,AT,VL),
     TargetStr = "s" ++ string.int_to_string(SentencePos),
     string.right(HandleStr,string.length(TargetStr)) = TargetStr,
     list.length(VL,Len),
     Len > 1,
     Ret = mrs_rel_handle(Handle)),
    KL,RstrL),
  RstrSet = set.from_list(RstrL),
  io.print(RstrSet,!IO),
  io.nl(!IO),
  io.print(RelHandle,!IO),
  io.nl(!IO),
  sentence_unpackRelation.unpackRelation(RelMap,ArgMap,RstrSet,RelHandle,Pred,set.init,Signatures0,[],Calls0,varset.init,VarSet0),
  term_io.write_term(VarSet0,det_index0(Calls0,0),!IO),
  io.nl(!IO).


