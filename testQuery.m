:- module testQuery.
:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module mrs.
:- import_module list.
:- import_module sentences.
:- import_module sentence_predicates.

main(!IO) :-
  io.print(det_head(sentences.sentences),!IO),
  io.nl(!IO). 
