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
:- import_module pair.
:- import_module require.
:- import_module unsafe.
:- import_module pretty_printer.
:- import_module varset.
:- import_module term_io.

:- import_module sentence_collectArguments.
:- import_module sentence_collectArgRefs.
:- import_module sentence_unpackRelation.

:- pred expandArgMap(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                     multi_map(mrs_types, mrs_rel_handle),
	             multi_map(mrs_types, mrs_rel_handle)).
:- mode expandArgMap(in,in,out) is det.
expandArgMap(RelMap,ArgMapIn,ArgMapOut) :-
    list.foldl(pred({RelHandle0,_,_,Pred}::in,ArgMapIn0::in,ArgMapOut0::out) is det :- collectArguments(RelMap,RelHandle0,Pred,ArgMapIn0,ArgMapOut0),
               multi_map.values(RelMap),ArgMapIn,ArgMapOut).

:- pred loadArgMapForSentence(mrs_psoa_post,
                              multi_map(mrs_types, mrs_rel_handle),
		              multi_map(mrs_types, mrs_rel_handle)).
:- mode loadArgMapForSentence(in,in,out) is det.
loadArgMapForSentence(Sentence,ArgMapIn,ArgMapOut) :-
  psoa_post(TopHandle,Event,RelMap) = Sentence,
  expandArgMap(RelMap,ArgMapIn,ArgMapOut).

:- pred expandArgRefMap(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                     multi_map(mrs_types, mrs_rel_handle),
	             multi_map(mrs_types, mrs_rel_handle)).
:- mode expandArgRefMap(in,in,out) is det.
expandArgRefMap(RelMap,ArgRefMapIn,ArgRefMapOut) :-
    list.foldl(pred({RelHandle0,_,_,Pred}::in,ArgRefMapIn0::in,ArgRefMapOut0::out) is det :- collectArgRefs(RelMap,RelHandle0,Pred,ArgRefMapIn0,ArgRefMapOut0),
               multi_map.values(RelMap),ArgRefMapIn,ArgRefMapOut).

:- pred loadArgRefMapForSentence(mrs_psoa_post,
                              multi_map(mrs_types, mrs_rel_handle),
		              multi_map(mrs_types, mrs_rel_handle)).
:- mode loadArgRefMapForSentence(in,in,out) is det.
loadArgRefMapForSentence(Sentence,ArgRefMapIn,ArgRefMapOut) :-
  psoa_post(TopHandle,Event,RelMap) = Sentence,
  expandArgRefMap(RelMap,ArgRefMapIn,ArgRefMapOut).

main(!IO) :-
  Sentence = det_index0(sentences.sentences,8),
  loadArgMapForSentence(Sentence,multi_map.init,ArgMap),
  loadArgRefMapForSentence(Sentence,multi_map.init,ArgRefMap),
  psoa_post(TopHandle,Event,RelMap) = Sentence,
  multi_map.lookup(RelMap,TopHandle,L),
  {RelHandle,_,_,Pred} = det_head(L),
  KL = multi_map.keys(ArgRefMap),
  list.filter(pred(Obj::in) is semidet :- wrap_rstr_handle(_) = Obj,KL,RstrL),
  % io.print(RstrL,!IO),
  sentence_unpackRelation.unpackRelation(RelMap,ArgMap,RelHandle,Pred,set.init,Signatures,[],Calls,varset.init,VarSet,[],Dependencies),
  pretty_printer.write_doc(pretty_printer.format(Calls),!IO),
  io.nl(!IO),
  pretty_printer.write_doc(pretty_printer.format(VarSet),!IO),
  io.nl(!IO),
  term_io.write_term(VarSet,list.det_index0(Calls,0),!IO),
  io.nl(!IO).

