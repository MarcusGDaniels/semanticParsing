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

:- import_module sentence_collectArguments.
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

main(!IO) :-
  Sentence = det_index0(sentences.sentences,8),
  loadArgMapForSentence(Sentence,multi_map.init,ArgMap),
  psoa_post(TopHandle,Event,RelMap) = Sentence,
  multi_map.lookup(RelMap,TopHandle,L),
  {RelHandle,_,_,Pred} = det_head(L),
  sentence_unpackRelation.unpackRelation(RelMap,ArgMap,RelHandle,Pred,set.init,Signatures,[],Outputs),
  pretty_printer.write_doc(pretty_printer.format(Outputs),!IO),
  io.nl(!IO).

