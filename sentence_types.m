:- module sentence_types.
:- interface.
:- import_module mrs.
:- import_module multi_map.
:- import_module sentence_predicates.

:- type mrs_psoa_post ---> psoa_post(mrs_handle,mrs_event,multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds})).

:- implementation.

