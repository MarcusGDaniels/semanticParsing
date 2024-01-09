:- module sentence_boilerplate.
:- interface.
:- import_module io.
:- pred print_boilerplate_interface(int, io, io).
:- mode print_boilerplate_interface(in, di,uo) is det.
:- pred print_boilerplate_implementation(int, io, io).
:- mode print_boilerplate_implementation(in, di, uo) is det.

:- implementation.

print_boilerplate_interface(SentenceNumber,!IO) :- 
   io.print(":- module sentence",!IO),
   io.print(SentenceNumber,!IO),
   io.print(".\n",!IO),
   io.print(":- interface.\n",!IO),
   io.print(":- import_module multi_map.\n",!IO),
   io.print(":- import_module sentence_accessors.\n",!IO),
   io.print(":- import_module mrs.\n",!IO),
   io.print(":- func handleMap = multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}).\n",!IO),
   io.print(":- mode handleMap = out is det.\n",!IO),
   io.print(":- func root = mrs_psoa_post.\n",!IO).

print_boilerplate_implementation(SentenceNumber,!IO) :- 
   io.print(":- implementation.\n",!IO),
   io.print(":- import_module sentence_vars_event",!IO),
   io.print(SentenceNumber,!IO),
   io.print(".\n",!IO),
   io.print(":- import_module sentence_vars_handle",!IO),
   io.print(SentenceNumber,!IO),
   io.print(".\n",!IO),
   io.print(":- import_module sentence_vars_inst",!IO),
   io.print(SentenceNumber,!IO),
   io.print(".\n",!IO),
   io.print(":- import_module sentence_vars_indiv",!IO),
   io.print(SentenceNumber,!IO),
   io.print(".\n",!IO),
   io.print(":- import_module sentence_vars_unknown",!IO),
   io.print(SentenceNumber,!IO),
   io.print(".\n",!IO),
   io.print(":- import_module map.\n",!IO),
   io.print(":- import_module list.\n",!IO).
