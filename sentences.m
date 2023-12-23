:- module sentences.
:- interface.
:- import_module sentence_accessors.
:- import_module list.
:- func sentence_list = list(mrs_psoa_post).
:- implementation.
:- import_module sentence0.
:- import_module sentence1.
:- import_module sentence2.
:- import_module sentence3.
:- import_module sentence4.
:- import_module sentence5.
:- import_module sentence6.
:- import_module sentence7.
:- import_module sentence8.
:- import_module sentence9.
sentence_list = [sentence0.root,sentence1.root,sentence2.root,sentence3.root,sentence4.root,sentence5.root,sentence6.root,sentence7.root,sentence8.root,sentence9.root].
