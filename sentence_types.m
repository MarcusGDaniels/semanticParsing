:- module sentence_types.
:- interface.
:- import_module mrs.
:- import_module multi_map.
:- import_module list.
:- import_module sentence_predicates.

:- type mrs_psoa_post ---> psoa_post(mrs_rel_handle,mrs_event,multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds})).

:- type mrs_types ---> wrap_rel_handle(mrs_rel_handle)
                       ; wrap_rstr_handle(mrs_rstr_handle)
                       ; wrap_body_handle(mrs_body_handle)
                       ; wrap_inst(mrs_inst)
		       ; wrap_event(mrs_event)
		       ; wrap_indiv(mrs_indiv) 
		       ; wrap_unknown(mrs_unknown)
		       ; wrap_carg(mrs_carg). 

:- type sentence_dependency == list(sentence_item).

:- type sentence_item ---> predicate(string) ; argument(string) ; dependency(mrs_rel_handle,sentence_dependency).

:- implementation.

