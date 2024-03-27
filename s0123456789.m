:- module s0123456789.
:- interface.

:- import_module bool.
:- import_module list.
:- import_module set.
:- import_module io.

:- type mrs_instance ---> mrs_instance(mrs_carg) ; mrs_conj(set(mrs_instance)).
:- type mrs_carg ---> mrs_carg(string).
:- type mrs_event ---> mrs_event(int,int).
:- type mrs_unknown ---> mrs_unknown(int,int).

:- pred main(io::di, io::uo) is det.

:- pred proper_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode proper_q(out, in, in) is nondet.

:- pred some_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode some_q(out, in, in) is nondet.

:- pred udef_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode udef_q(out, in, in) is nondet.

:- pred the_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode the_q(out, in, in) is nondet.

:- pred def_explicit_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode def_explicit_q(out, in, in) is nondet.

:- pred pronoun_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode pronoun_q(out, in, in) is nondet.

:- pred a_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode a_q(out, in, in) is nondet.

:- pred no_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode no_q(out, in, in) is nondet.

:- pred every_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode every_q(out, in, in) is nondet.


:- pred named(mrs_instance, mrs_carg).
:- mode named(out, in) is det.

:- pred therefore_a_1(mrs_instance, (func) = bool).
:- mode therefore_a_1(in, in) is semidet.

:- pred colon_p_namely(mrs_event, (func) = bool, (func) = bool).
:- mode colon_p_namely(in, in,in) is semidet.

:- pred in_p_loc(mrs_event, mrs_event, mrs_instance).
:- mode in_p_loc(in, in, in) is det.

:- pred compound(mrs_event, mrs_instance, mrs_instance).
:- mode compound(in, in, in) is det.

:- pred kill_v_1(mrs_event, mrs_instance, mrs_instance).
:- mode kill_v_1(in, in, in) is semidet.

:- pred implicit_conj(mrs_instance, mrs_instance, mrs_instance).
:- mode implicit_conj(out, in, in) is semidet.

:- pred live_v_1(mrs_event, mrs_instance).
:- mode live_v_1(in, in) is det.

:- pred only_a_1(mrs_event, mrs_instance).
:- mode only_a_1(in, in) is det.

:- pred be_v_id(mrs_event, mrs_instance, mrs_instance).
:- mode be_v_id(in, in, out) is det.

:- pred person(mrs_instance).
:- mode person(out) is nondet.

:- pred and_c_e(mrs_event, mrs_event, mrs_event).
:- mode and_c_e(in,in,in) is det.

:- pred and_c_x(mrs_instance, mrs_instance, mrs_instance).
:- mode and_c_x(out,in,in) is nondet.

:- pred butler_n_1(mrs_instance).
:- mode butler_n_1(out) is nondet.

:- pred killer_n_1(mrs_instance).
:- mode killer_n_1(out) is nondet.

:- pred people_n_of(mrs_instance,mrs_instance).
:- mode people_n_of(in,in) is det.

:- pred therein_p_dir(mrs_event,mrs_event).
:- mode therein_p_dir(in,in) is det.

:- pred poss(mrs_event, mrs_instance, mrs_instance).
:- mode poss(in, in, in) is det.

:- pred victim_n_of(mrs_instance, mrs_instance).
:- mode victim_n_of(out, in) is nondet.

:- pred always_a_1(mrs_instance, mrs_event).
:- mode always_a_1(in, in) is det.

:- pred hate_v_1(mrs_event, mrs_instance, mrs_instance).
:- mode hate_v_1(in, in, in) is semidet.

:- pred never_a_1(mrs_instance, (func) = bool).
:- mode never_a_1(in, in) is semidet.

:- pred pron(mrs_instance).
:- mode pron(in) is det.

:- pred more_comp(mrs_event, mrs_event, mrs_instance).
:- mode more_comp(in, in, in) is semidet.

:- pred rich_a_in(mrs_event, mrs_instance, mrs_instance).
:- mode rich_a_in(in, in, in) is semidet. 

:- pred card(mrs_event, mrs_instance, mrs_carg).
:- mode card(in,in,in) is det.

:- pred generic_entity(mrs_instance).
:- mode generic_entity(out) is det.

:- pred aunt_n_of(mrs_instance,mrs_instance).
:- mode aunt_n_of(out,in) is nondet.

:- pred except_p(mrs_event, mrs_instance, mrs_instance).
:- mode except_p(in, in, in) is semidet.

:- pred neg(mrs_event, (func) = bool).
:- mode neg(in, in) is semidet.

:- pred unknown(mrs_unknown, mrs_event).
:- mode unknown(in, in) is det.

:- pred coref(mrs_instance, mrs_instance).
:- mode coref(in,in) is semidet.

:- implementation.
:- import_module solutions.
:- import_module string.
:- import_module unsafe.
:- import_module pretty_printer.

% ERG predicate definitions
named(Inst, Carg) :- Inst = mrs_instance(Carg).

:- pred namedPeople(mrs_instance).
:- mode namedPeople(out) is nondet.
namedPeople(Person) :- Person = mrs_instance(mrs_carg("Agatha")); Person = mrs_instance(mrs_carg("Charles")).

butler_n_1(Person) :- Person = mrs_instance(mrs_carg("The Butler")) ; namedPeople(Person).

killer_n_1(Person) :- 
  Person = mrs_instance(mrs_carg("The Killer")) ;
  Person = mrs_instance(mrs_carg("The Butler")) ;
  namedPeople(Person).

person(Person) :- butler_n_1(Person); namedPeople(Person).

generic_entity(I) :- I = mrs_instance(mrs_carg("generic")).

the_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).
proper_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).
udef_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).
some_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).
def_explicit_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).
pronoun_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).
a_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).
no_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).
every_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).

:- pragma promise_pure(in_p_loc/3).
in_p_loc(E0, E1, Inst) :- 
  impure unsafe_perform_io(io.print({"in_p_loc",E0,E1,Inst})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(compound/3).
compound(E, Inst0, Inst1) :-
  impure unsafe_perform_io(io.print({"compound",E,Inst0,Inst1})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(live_v_1/2).
live_v_1(E, Inst0) :- 
  impure unsafe_perform_io(io.print({"live_v_1",E,Inst0})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(only_a_1/2).
only_a_1(E, Inst0) :-
  impure unsafe_perform_io(io.print({"only_a_1",E,Inst0})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(be_v_id/3).
be_v_id(E, Inst0, Inst1) :- 
  impure unsafe_perform_io(io.print({"be_v_id",E,"Inst1 = ",Inst0})),
  impure unsafe_perform_io(io.nl),
  Inst1 = Inst0.

:- pragma promise_pure(kill_v_1/3).
kill_v_1(E, Inst0, Inst1) :-
  impure unsafe_perform_io(io.print({"kill_v_1",E,Inst0,Inst1})),
  impure unsafe_perform_io(io.nl),
  true.

:- pred mkConj(mrs_instance,mrs_instance,mrs_instance).
:- mode mkConj(out,in,in).
:- pragma promise_pure(mkConj/3).
mkConj(I0,I1,I2) :- 
  (if mrs_conj(I1s) = I1 then
    (if mrs_conj(I2s) = I2 then
      set.is_empty(set.intersect(I1s,I2s))
     else
      not set.member(I2,I1s))
   else
    (if mrs_conj(I2s) = I2 then
      not set.member(I1,I2s)
     else
      not I1 = I2)),
  I0set = (if mrs_conj(I1sL) = I1 then
             (if mrs_conj(I2sL) = I2 then
               set.intersect(I1sL,I2sL)   
              else
               set.insert(I1sL,I2))
           else
             (if mrs_conj(I2sL) = I2 then
               set.insert(I2sL,I1)
              else
               set.list_to_set([I1,I2]))),
  I0 = mrs_conj(I0set).

:- pragma promise_pure(implicit_conj/3).
implicit_conj(I0,I1,I2) :- mkConj(I0,I1,I2).

:- pragma promise_pure(and_c_x/3).
and_c_x(I0, I1, I2) :- mkConj(I0,I1,I2).

:- pragma promise_pure(and_c_e/3).
and_c_e(E0, E1, E2) :- 
  true.

:- pragma promise_pure(therein_p_dir/2).
therein_p_dir(E0, E1) :- 
  impure unsafe_perform_io(io.print({"therein_p_dir",E0,E1})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(poss/3).
poss(E, I0, I1) :-
  impure unsafe_perform_io(io.print({"poss",E,I0,I1})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(always_a_1/2).
always_a_1(I, E) :- 
  impure unsafe_perform_io(io.print({"always_a_1",I,E})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(hate_v_1/3).
hate_v_1(E, I0, I1) :- 
  impure unsafe_perform_io(io.print({"hate_v_1",I0,I1})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(never_a_1/2).
never_a_1(I23s2, Func) :-
  impure unsafe_perform_io(io.print({"never_a_1",I23s2,Func})),
  impure unsafe_perform_io(io.nl),
  apply(Func) = no.

:- pragma promise_pure(neg/2).
neg(E, Func) :-
  impure unsafe_perform_io(io.print({"neg",E,Func})),
  impure unsafe_perform_io(io.nl),
  apply(Func) = no.

:- pragma promise_pure(pron/1).
pron(X16s2) :- 
  impure unsafe_perform_io(io.print({"pron",X16s2})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(more_comp/3).
more_comp(E0, E1, X0) :- 
  impure unsafe_perform_io(io.print({"more_comp",E0,E1,X0})),
  impure unsafe_perform_io(io.nl),
  false.

:- pragma promise_pure(rich_a_in/3).
rich_a_in(E0, I0, I1) :-
  impure unsafe_perform_io(io.print({"rich_a_in",E0,I0,I1})),
  impure unsafe_perform_io(io.nl),
  false.

:- pragma promise_pure(card/3).
card(E, I, C) :- 
  impure unsafe_perform_io(io.print({"card",E,I,C})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(aunt_n_of/2).
aunt_n_of(I0,I1) :- 
  impure unsafe_perform_io(io.print({"Testing aunt_n_of",I1})),
  impure unsafe_perform_io(io.nl),
  person(I0),
  impure unsafe_perform_io(io.print({"OK: aunt_n_of",I0,I1})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(victim_n_of/2).
victim_n_of(I0, I1) :- 
  impure unsafe_perform_io(io.print({"Testing victim_n_of",I1})),
  impure unsafe_perform_io(io.nl),
  person(I0),
  impure unsafe_perform_io(io.print({"OK: victim_n_of",I0,I1})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(people_n_of/2).
people_n_of(I0, I1) :-
  impure unsafe_perform_io(io.print({"people_n_of",I1})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(except_p/3).
except_p(E0, I0, I1) :-
  impure unsafe_perform_io(io.print({"except_p",E0,I0,I1})),
  impure unsafe_perform_io(io.nl),
  not I0 = I1.

:- pragma promise_pure(unknown/2).
unknown(U, E) :- 
  impure unsafe_perform_io(io.print({"unknown",U,E})),
  impure unsafe_perform_io(io.nl),
  true.

:- pragma promise_pure(therefore_a_1/2).
therefore_a_1(I, Func) :-
  impure unsafe_perform_io(io.print({"therefore_a_1",I,Func})),
  impure unsafe_perform_io(io.nl),
  apply(Func) = yes.

:- pragma promise_pure(colon_p_namely/3).
colon_p_namely(E, FuncA, FuncB) :-
  impure unsafe_perform_io(io.print({"colon_p_namely",E,FuncA,FuncB})),
  impure unsafe_perform_io(io.nl),
  apply(FuncA) = yes, apply(FuncB) = yes.

:- pragma promise_pure(coref/2).
coref(A,B) :- 
  impure unsafe_perform_io(io.print({"coref",A,B})),
  impure unsafe_perform_io(io.nl),
  A = B.

% Sentence 0
% "Someone who lives in Dreadbury Mansion killed Aunt Agatha." 0

:- pred h20s0(mrs_instance). % Dreadbury
:- mode h20s0(out) is det.
:- pred h14s0_1(mrs_instance). % Mansion
:- mode h14s0_1(out) is det.
:- pred h33s0(mrs_instance). % Aunt
:- mode h33s0(out) is det.
:- pred h27s0_1(mrs_instance). % Agatha
:- mode h27s0_1(out) is det.

:- pred h17s0(mrs_instance). % proper Dreadbury
:- mode h17s0(out) is nondet. 
:- pred h30s0(mrs_instance).
:- mode h30s0(out) is nondet. % proper Agatha

:- pred h25s0(mrs_instance, mrs_instance). % Agatha predicates
:- mode h25s0(out,in) is nondet.
:- pred h12s0(mrs_instance, mrs_instance). % Dreadbury predicates
:- mode h12s0(out,in) is nondet.
:- pred h6s0(mrs_instance, mrs_instance). % in_p_loc, live_v_1, person
:- mode h6s0(in,out) is nondet.
:- pred h11s0(mrs_instance, mrs_instance). % proper Dreadbury Mansion
:- mode h11s0(out,in) is nondet.
:- pred h24s0(mrs_instance, mrs_instance). % proper Aunt Agatha
:- mode h24s0(out,in) is nondet.

:- pred h14s0_0(mrs_instance, mrs_instance). % Dreadbury Mansion compound
:- mode h14s0_0(in,in) is det. 

:- pred h27s0_0(mrs_instance, mrs_instance). % Aunt Agatha compound
:- mode h27s0_0(in,in) is det.

:- pred h4s0_0(mrs_instance). % in_p_loc
:- mode h4s0_0(in) is det.
:- pred h4s0_1(mrs_instance). % live_v_1
:- mode h4s0_1(in) is det.

:- pred h4s0_2(mrs_instance). % person
:- mode h4s0_2(out) is nondet.

:- pred h5s0(mrs_instance, mrs_instance). % find persons in Mansion
:- mode h5s0(in,out) is nondet.

:- pred h1s0(mrs_instance, mrs_instance). % kill_v_1
:- mode h1s0(in,in) is semidet.

:- pred h13s0.
:- mode h13s0 is det.

:- pred h19s0.
:- mode h19s0 is det.

:- pred h26s0.
:- mode h26s0 is det.

:- pred h32s0.
:- mode h32s0 is det.

:- pred h7s0.
:- mode h7s0 is det.

:- func e15s0 = mrs_event.
:- func e2s0 = mrs_event.
:- func e28s0 = mrs_event.
:- func e8s0 = mrs_event.
:- func e9s0 = mrs_event.

:- pred combined0(mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance).
:- mode combined0(out,out,out,out,out) is nondet.

e15s0 = mrs_event(0,15).
e2s0 = mrs_event(0,2).
e28s0 = mrs_event(0,28).
e8s0 = mrs_event(0,8).
e9s0 = mrs_event(0,9).

h12s0(X10s0, X16s0) :- h14s0_0(X10s0, X16s0), h14s0_1(X10s0).
h20s0(X16s0) :- named(X16s0, mrs_carg("Dreadbury")).
h25s0(X23s0, X29s0) :- h27s0_0(X23s0, X29s0), h27s0_1(X23s0).
h33s0(X29s0) :- named(X29s0, mrs_carg("Aunt")).
h6s0(X10s0, X3s0) :- h4s0_0(X10s0), h4s0_1(X3s0), h4s0_2(X3s0).
h11s0(X10s0, X16s0) :- proper_q(X10s0, 
                                (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h12s0(Val,X16s0)),
                                (func) = Ret :- Ret = (if h13s0 then yes else no)).
h14s0_0(X10s0, X16s0) :- compound(e15s0, X10s0, X16s0).
h14s0_1(X10s0) :- named(X10s0, mrs_carg("Mansion")).
h17s0(X16s0) :- proper_q(X16s0,
                         (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h20s0(Val)),
                         (func) = Ret :- Ret = (if h19s0 then yes else no)).
h1s0(X23s0, X3s0) :- kill_v_1(e2s0, X3s0, X23s0).
h24s0(X23s0, X29s0) :- proper_q(X23s0, 
                               (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h25s0(Val,X29s0)),
                               (func) = Ret :- Ret = (if h26s0 then yes else no)).
h27s0_0(X23s0, X29s0) :- compound(e28s0, X23s0, X29s0).
h27s0_1(X23s0) :- named(X23s0, mrs_carg("Agatha")).
h30s0(X29s0) :- proper_q(X29s0, 
                         (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h33s0(Val)),
                         (func) = Ret :- Ret = (if h32s0 then yes else no)).
h4s0_0(X10s0) :- in_p_loc(e9s0, e8s0, X10s0).
h4s0_1(X3s0) :- live_v_1(e8s0, X3s0).
h4s0_2(X3s0) :- person(X3s0).

h5s0(X10s0, X3s0) :- 
  some_q(X3s0, (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h6s0(X10s0,Val)),
               (func) = Ret :- Ret = (if h7s0 then yes else no)).

h13s0 :- true.
h19s0 :- true.
h26s0 :- true.
h32s0 :- true.
h7s0 :- true.

combined0(X10s0, X16s0, X23s0, X29s0, X3s0) :- 
  h1s0(X23s0, X3s0),
  h11s0(X10s0, X16s0),
  h17s0(X16s0), 
  h24s0(X23s0, X29s0),
  h30s0(X29s0), 
  h5s0(X10s0, X3s0).

% Sentence 1
% "Agatha, the butler, and Charles live in Dreadbury Mansion, and are the only people who live therein." 1

:- pred h0s1(mrs_instance,mrs_instance,mrs_instance).
:- mode h0s1(in,out,in).

:- pred h11s1(mrs_instance).
:- mode h11s1(out) is semidet.

:- pred h28s1(mrs_instance).
:- mode h28s1(out) is semidet.

:- pred h34s1(mrs_instance,mrs_instance).
:- mode h34s1(out,in) is semidet.

:- pred h42s1(mrs_instance).
:- mode h42s1(out) is semidet.

:- pred h48s1(mrs_instance,mrs_instance).
:- mode h48s1(in,in) is nondet.

:- pred h13s1(mrs_instance,mrs_instance,mrs_instance).
:- mode h13s1(out,in,in) is nondet.

:- pred h17s1(mrs_instance,mrs_instance,mrs_instance).
:- mode h17s1(in,out,in) is semidet.

:- pred h18s1(mrs_instance).
:- mode h18s1(out) is nondet.

:- pred h1s1_0.
:- mode h1s1_0 is det. 

:- pred h1s1_1(mrs_instance,mrs_instance).
:- mode h1s1_1(in,out) is det.

:- pred h1s1_2(mrs_instance).
:- mode h1s1_2(in) is det.

:- pred h1s1_3(mrs_instance).
:- mode h1s1_3(in) is det.

:- pred h22s1(mrs_instance).
:- mode h22s1(out) is nondet.

:- pred h23s1(mrs_instance, mrs_instance, mrs_instance).
:- mode h23s1(out, in, in) is nondet.

:- pred h25s1(mrs_instance).
:- mode h25s1(out).

:- pred h33s1(mrs_instance, mrs_instance).
:- mode h33s1(out,in).

:- pred h36s1_0(mrs_instance, mrs_instance).
:- mode h36s1_0(in,in).

:- pred h36s1_1(mrs_instance).
:- mode h36s1_1(out).

:- pred h39s1(mrs_instance).
:- mode h39s1(out).

:- pred h47s1(mrs_instance,mrs_instance).
:- mode h47s1(in,in).

:- pred h4s1(mrs_instance,mrs_instance,mrs_instance).
:- mode h4s1(in,in,in).

:- pred h50s1_0(mrs_instance).
:- mode h50s1_0(in).

:- pred h50s1_1(mrs_instance).
:- mode h50s1_1(in) is semidet.

:- pred h50s1_2(mrs_instance,mrs_instance).
:- mode h50s1_2(in,in) is nondet.

:- pred h50s1_3.
:- mode h50s1_3 is det.

:- pred h7s1(mrs_instance).
:- mode h7s1(out).

:- pred h16s1.
:- mode h16s1 is det.

:- pred h12s1.
:- mode h12s1 is det.

:- pred h27s1.
:- mode h27s1 is det.

:- pred h35s1.
:- mode h35s1 is det.

:- pred h41s1.
:- mode h41s1 is det.

:- pred h49s1.
:- mode h49s1 is det.

:- pred h6s1.
:- mode h6s1 is det.

:- pred h10s1.
:- mode h10s1 is det.

:- pred combined1(mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance).
:- mode combined1(out,out,out,out,out,out,out,out,out) is nondet.

:- func e2s1 = mrs_event.
:- func e30s1 = mrs_event.
:- func e31s1 = mrs_event.
:- func e37s1 = mrs_event.
:- func e45s1 = mrs_event.
:- func e51s1 = mrs_event.
:- func e53s1 = mrs_event.
:- func e54s1 = mrs_event.

e2s1 = mrs_event(1,2).
e30s1 = mrs_event(1,30).
e31s1 = mrs_event(1,31).
e37s1 = mrs_event(1,37).
e45s1 = mrs_event(1,45).
e51s1 = mrs_event(1,51).
e53s1 = mrs_event(1,53).
e54s1 = mrs_event(1,54).

h0s1(X3s1, X46s1, X32s1) :- h1s1_0, h1s1_1(X3s1, X46s1), h1s1_2(X32s1), h1s1_3(X3s1).

h11s1(X8s1) :- named(X8s1, mrs_carg("Agatha")).
h28s1(X24s1) :- named(X24s1, mrs_carg("Charles")).
h34s1(X32s1, X38s1) :- h36s1_0(X32s1, X38s1), h36s1_1(X32s1).
h42s1(X38s1) :- named(X38s1, mrs_carg("Dreadbury")).
h48s1(X46s1,I52s1) :- h50s1_0(X46s1), h50s1_1(X46s1), h50s1_2(X46s1,I52s1), h50s1_3.

h13s1(X14s1,X19s1,X24s1) :- udef_q(X14s1, 
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h23s1(Val, X19s1, X24s1)),
                       (func) = Ret :- Ret = (if h16s1 then yes else no)).

h17s1(X14s1, X3s1, X8s1) :- implicit_conj(X3s1, X8s1, X14s1).
h18s1(X19s1) :- the_q(X19s1, 
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h22s1(Val)),
                       (func) = Ret :- Ret = (if h12s1 then yes else no)).

h1s1_0 :- and_c_e(e2s1, e30s1, e45s1).
h1s1_1(X3s1, X46s1) :- be_v_id(e45s1, X3s1, X46s1).
h1s1_2(X32s1) :- in_p_loc(e31s1, e30s1, X32s1).
h1s1_3(X3s1) :- live_v_1(e30s1, X3s1).
h22s1(X19s1) :- butler_n_1(X19s1).
h23s1(X14s1, X19s1, X24s1) :- and_c_x(X14s1, X19s1, X24s1).
h25s1(X24s1) :- proper_q(X24s1,
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h28s1(Val)),
                       (func) = Ret :- Ret = (if h27s1 then yes else no)).
h33s1(X32s1, X38s1) :- proper_q(X32s1,
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h34s1(Val,X38s1)),
                       (func) = Ret :- Ret = (if h35s1 then yes else no)).
h36s1_0(X32s1, X38s1) :- compound(e37s1, X32s1, X38s1).
h36s1_1(X32s1) :- named(X32s1, mrs_carg("Mansion")).
h39s1(X38s1) :- proper_q(X38s1, 
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h42s1(Val)),
                       (func) = Ret :- Ret = (if h41s1 then yes else no)).
h47s1(X46s1,I52s1) :- the_q(X46s1, 
                       (func) = Ret :- Ret = [X46s1],
                       (func) = Ret :- Ret = (if h49s1 then yes else no)).
h4s1(X14s1, X3s1, X8s1) :- udef_q(X3s1,
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h17s1(X14s1,Val,X8s1)),
                       (func) = Ret :- Ret = (if h6s1 then yes else no)).
h50s1_0(X46s1) :- live_v_1(e53s1, X46s1).
h50s1_1(X46s1) :- only_a_1(e51s1, X46s1).
h50s1_2(X46s1,I52s1) :- people_n_of(X46s1, I52s1).
h50s1_3 :- therein_p_dir(e54s1, e53s1).
h7s1(X8s1) :- proper_q(X8s1, 
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h11s1(Val)),
                       (func) = Ret :- Ret = (if h10s1 then yes else no)).

h16s1 :- true.
h12s1 :- true.
h27s1 :- true.
h35s1 :- true.
h41s1 :- true.
h49s1 :- true.
h6s1 :- true.
h10s1 :- true.

person(mrs_instance(mrs_carg("Charles"))).

combined1(X14s1, X19s1, X24s1, X32s1, X38s1, X3s1, X46s1, X8s1, I52s1) :- 
   h7s1(X8s1),
   h39s1(X38s1),
   h33s1(X32s1, X38s1),
   h0s1(X3s1, X46s1, X32s1),
   h25s1(X24s1),
   h22s1(X19s1),
   h18s1(X19s1),
   h13s1(X14s1, X19s1, X24s1),

   h13s1(X14s1,X19s1,X24s1),
   h17s1(X14s1, X3s1, X8s1),
   I52s1 = mrs_instance(mrs_carg("1")),
   h47s1(X46s1,I52s1),
   h4s1(X14s1, X3s1, X8s1).

% Sentence 2
% "A killer always hates his victim, and is never richer than his victim." 
:- pred h0s2(mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance).
:- mode h0s2(in,in,in,in,in,in) is semidet.

:- pred h12s2(mrs_instance,mrs_instance,mrs_instance).
:- mode h12s2(in,out,in) is nondet.

:- pred h24s2(mrs_instance, mrs_instance,mrs_instance).
:- mode h24s2(in,in,in) is semidet.

:- pred h30s2(mrs_instance, mrs_instance, mrs_instance).
:- mode h30s2(out,in,in) is nondet.

:- pred h11s2(mrs_instance, mrs_instance, mrs_instance).
:- mode h11s2(in,out,in) is nondet.

:- pred h14s2_0(mrs_instance, mrs_instance).
:- mode h14s2_0(in, in) is det.

:- pred h14s2_1(mrs_instance,mrs_instance).
:- mode h14s2_1(out,in) is nondet.

:- pred h17s2(mrs_instance). 
:- mode h17s2(in) is nondet.

:- pred h1s2_0(mrs_instance).
:- mode h1s2_0(in) is det.

:- pred h1s2_1.
:- mode h1s2_1 is det.

:- pred h1s2_2(mrs_instance, mrs_instance).
:- mode h1s2_2(in,in) is semidet.

:- pred h1s2_3(mrs_instance,mrs_instance,mrs_instance, mrs_instance).
:- mode h1s2_3(in,in,in,in) is semidet.

:- pred h20s2(mrs_instance).
:- mode h20s2(in) is nondet.

:- pred h25s2_0(mrs_instance).
:- mode h25s2_0(in) is semidet.

:- pred h25s2_1(mrs_instance,mrs_instance).
:- mode h25s2_1(in,in) is semidet.

:- pred h29s2(mrs_instance, mrs_instance, mrs_instance).
:- mode h29s2(out,in,in) is nondet.

:- pred h32s2_0(mrs_instance,mrs_instance).
:- mode h32s2_0(in,in) is det.

:- pred h32s2_1(mrs_instance,mrs_instance).
:- mode h32s2_1(out,in) is nondet.

:- pred h35s2(mrs_instance).
:- mode h35s2(in) is semidet.

:- pred h38s2(mrs_instance).
:- mode h38s2(in) is det.

:- pred h4s2(mrs_instance).
:- mode h4s2(out) is nondet.

:- pred h7s2(mrs_instance).
:- mode h7s2(out) is nondet.

:- pred combined2(mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance).
:- mode combined2(out,out,out,out,out,out,out,out,out) is nondet.

:- pred h13s2.
:- mode h13s2 is det.

:- pred h19s2.
:- mode h19s2 is det.

:- pred h31s2.
:- mode h31s2 is det.

:- pred h37s2.
:- mode h37s2 is det.

:- pred h6s2.
:- mode h6s2 is det.

:- func e2s2 = mrs_event.
:- func e9s2 = mrs_event.
:- func e15s2 = mrs_event.
:- func e22s2 = mrs_event.
:- func e27s2 = mrs_event.
:- func e33s2 = mrs_event.

e2s2 = mrs_event(2,2).
e9s2 = mrs_event(9,2).
e15s2 = mrs_event(15,2).
e22s2 = mrs_event(22,2).
e27s2 = mrs_event(27,2).
e33s2 = mrs_event(33,2).

h0s2(I8s2, I23s2, I26s2, X10s2, X3s2, X28s2) :- h1s2_0(I8s2), h1s2_1, h1s2_2(X10s2, X3s2), h1s2_3(I23s2,I26s2,X28s2,X3s2).
h12s2(I21s2, X10s2, X16s2) :- 
  h14s2_1(X10s2,I21s2),
  h14s2_0(X10s2, X16s2).
h24s2(X28s2, X3s2, I26s2) :- h25s2_0(X28s2), h25s2_1(X3s2,I26s2).
h30s2(X28s2, X34s2, I39s2) :- h32s2_1(X28s2,I39s2), h32s2_0(X28s2, X34s2).
h11s2(I21s2, X10s2, X16s2) :- def_explicit_q(X10s2,
                                      (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h12s2(I21s2,Val,X16s2)),
                                      (func) = Ret :- Ret = (if h13s2 then yes else no)).
h14s2_0(X10s2, X16s2) :- poss(e15s2, X10s2, X16s2).
h14s2_1(X10s2,I21s2) :- victim_n_of(X10s2, I21s2).
h17s2(X16s2) :- pronoun_q(X16s2, 
                         (func) = Ret :- Ret = (if h20s2(X16s2) then [X16s2] else []),
                         (func) = Ret :- Ret = (if h19s2 then yes else no)).
h1s2_0(I8s2) :- always_a_1(I8s2, e9s2).
h1s2_1 :- and_c_e(e2s2, e9s2, e22s2).
h1s2_2(X10s2, X3s2) :- hate_v_1(e9s2, X3s2, X10s2).
h1s2_3(I23s2, I26s2, X28s2, X3s2) :- X28s2 = X3s2, never_a_1(I23s2, (func) = Ret :- Ret = (if h24s2(I26s2, X28s2, X3s2) then yes else no)).
h20s2(X16s2) :- pron(X16s2).
h25s2_0(X28s2) :- more_comp(e27s2, e22s2, X28s2).
h25s2_1(X3s2,I26s2) :- rich_a_in(e22s2, X3s2, I26s2).
h29s2(X28s2, X34s2, I39s2) :- def_explicit_q(X28s2,
                                      (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h30s2(Val,X34s2,I39s2)),
                                      (func) = Ret :- Ret = (if h31s2 then yes else no)).
h32s2_0(X28s2, X34s2) :- poss(e33s2, X28s2, X34s2).
h32s2_1(X28s2,I39s2) :- victim_n_of(X28s2, I39s2).
h35s2(X34s2) :- pronoun_q(X34s2, 
                         (func) = Ret :- Ret = (if h38s2(X34s2) then [X34s2] else []),
                         (func) = Ret :- Ret = (if h37s2 then yes else no)).
h38s2(X34s2) :- pron(X34s2).
h4s2(X3s2) :- a_q(X3s2, 
                         (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h7s2(Val)),
                         (func) = Ret :- Ret = (if h6s2 then yes else no)).
h7s2(X3s2) :- killer_n_1(X3s2).

combined2(I8s2, I23s2, I26s2, I39s2, X10s2, X16s2, X28s2, X34s2, X3s2) :- 
   I8s2 = mrs_instance(mrs_carg("I8s2")),
   I21s2 = mrs_instance(mrs_carg("I21s2")),
   I23s2 = mrs_instance(mrs_carg("I23s2")),
   I26s2 = mrs_instance(mrs_carg("I26s2")),
   I39s2 = mrs_instance(mrs_carg("I39s2")),
   h4s2(X3s2),
   X16s2 = X3s2,
   X34s2 = X3s2,
   h11s2(I21s2, X10s2, X16s2),
   h0s2(I8s2, I23s2, I26s2, X10s2, X3s2, X28s2),
   h17s2(X16s2),
   h20s2(X16s2),
   h29s2(X28s2, X34s2, I39s2),
   h35s2(X34s2),
   h38s2(X34s2),
   h7s2(X3s2).

h13s2 :- true.
h19s2 :- true.
h31s2 :- true.
h37s2 :- true.
h6s2 :- true.

% Sentence 3
% "Charles hates no one that Aunt Agatha hates."

:- pred h11s3(mrs_instance, mrs_instance).
:- mode h11s3(out,in) is nondet.

:- pred h18s3(mrs_instance, mrs_instance).
:- mode h18s3(out, in) is nondet.

:- pred h7s3(mrs_instance).
:- mode h7s3(out) is det.

:- pred h10s3(mrs_instance, mrs_instance).
:- mode h10s3(in, out) is nondet.

:- pred h13s3_0(mrs_instance).
:- mode h13s3_0(in) is det.

:- pred h13s3_1(mrs_instance).
:- mode h13s3_1(out) is det.

:- pred h13s3_2(mrs_instance, mrs_instance).
:- mode h13s3_2(in, in) is semidet.

:- pred h16s3(mrs_instance, mrs_instance).
:- mode h16s3(out, in) is nondet.

:- pred h20s3_0(mrs_instance, mrs_instance).
:- mode h20s3_0(in, in) is semidet.

:- pred h20s3_1(mrs_instance).
:- mode h20s3_1(out) is det.

:- pred h23s3(mrs_instance,mrs_instance).
:- mode h23s3(out,in) is nondet.

:- pred h26s3(mrs_instance,mrs_instance).
:- mode h26s3(out,in) is nondet.

:- pred h4s3(mrs_instance).
:- mode h4s3(out) is nondet.

:- pred h1s3(mrs_instance, mrs_instance).
:- mode h1s3(in,in) is semidet.   

:- pred combined3(mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance).
:- mode combined3(out, out, out, out, out) is nondet.

:- pred h6s3.
:- mode h6s3 is det.

:- pred h12s3.
:- mode h12s3 is det.

:- pred h19s3.
:- mode h19s3 is det.

:- pred h25s3.
:- mode h25s3 is det.

:- func e2s3 = mrs_event.
:- func e15s3 = mrs_event.
:- func e21s3 = mrs_event.
:- func e29s3 = mrs_event.

e2s3 = mrs_event(2,3).
e15s3 = mrs_event(15,3).
e21s3 = mrs_event(21,3).
e29s3 = mrs_event(29,3).

h11s3(X9s3, X17s3) :- h13s3_1(X9s3), h13s3_0(X9s3), h13s3_2(X17s3, X9s3).
h18s3(X17s3, X22s3) :- h20s3_0(X17s3, X22s3), h20s3_1(X17s3).
h7s3(X3s3) :- named(X3s3, mrs_carg("Charles")).
h10s3(X17s3, X9s3) :- no_q(X9s3, 
                           (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h11s3(Val,X17s3)),
                           (func) = Ret :- Ret = (if h12s3 then yes else no)).
h13s3_0(X9s3) :- card(e15s3, X9s3, mrs_carg("1")).
h13s3_1(X9s3) :- generic_entity(X9s3).
h13s3_2(X17s3, X9s3) :- hate_v_1(e29s3, X17s3, X9s3).
h16s3(X17s3, X22s3) :- proper_q(X17s3,
                               (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h18s3(Val,X22s3)),
                               (func) = Ret :- Ret = (if h19s3 then yes else no)).

h20s3_0(X17s3, X22s3) :- compound(e21s3, X17s3, X22s3).
h20s3_1(X17s3) :- named(X17s3, mrs_carg("Agatha")).
h23s3(X22s3,I27s3) :- udef_q(X22s3,
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h26s3(Val,I27s3)),
                       (func) = Ret :- Ret = (if h25s3 then yes else no)).
h26s3(X22s3,I27s3) :- aunt_n_of(X22s3, I27s3).
h4s3(X3s3) :- proper_q(X3s3,
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h7s3(Val)),
                       (func) = Ret :- Ret = (if h6s3 then yes else no)).

h1s3(X3s3, X9s3) :- hate_v_1(e2s3, X3s3, X9s3).

combined3(X17s3, X22s3, X3s3, X9s3, I27s3) :-
  I27s3 = mrs_instance(mrs_carg("i27s3")),
  h23s3(X22s3,I27s3),
  h16s3(X17s3,X22s3),
  h10s3(X17s3,X9s3),
  h26s3(X22s3,I27s3),
  h4s3(X3s3),
  h1s3(X3s3, X9s3),
  X22s3 = X17s3. % aunt_n_of should always be Agatha

h6s3 :- true.
h12s3 :- true.
h19s3 :- true.
h25s3 :- true.

% Sentence 4
% "Agatha hates everyone except the butler."

:- pred h12s4(mrs_instance, mrs_instance).
:- mode h12s4(in,out) is nondet.

:- pred h7s4(mrs_instance).
:- mode h7s4(out) is det.

:- pred h10s4_0(mrs_instance, mrs_instance).
:- mode h10s4_0(in, in) is semidet.

:- pred h10s4_1(mrs_instance).
:- mode h10s4_1(out) is nondet.

:- pred h11s4(mrs_instance, mrs_instance).
:- mode h11s4(in, out) is nondet.

:- pred h16s4(mrs_instance).
:- mode h16s4(out) is nondet.

:- pred h19s4(mrs_instance).
:- mode h19s4(out) is nondet.

:- pred h4s4(mrs_instance).
:- mode h4s4(out) is nondet.

:- pred h1s4(mrs_instance, mrs_instance).
:- mode h1s4(in, in) is semidet.

:- pred combined4(mrs_instance, mrs_instance, mrs_instance).
:- mode combined4(out, out, out) is nondet.

:- pred h6s4.
:- mode h6s4 is det.

:- pred h13s4.
:- mode h13s4 is det.

:- pred h18s4.
:- mode h18s4 is det.

:- func e2s4 = mrs_event.
:- func e14s4 = mrs_event.

e2s4 = mrs_event(2,4).
e14s4 = mrs_event(14,4).

h12s4(X15s4, X9s4) :- h10s4_0(X15s4, X9s4), h10s4_1(X9s4).
h7s4(X3s4) :- named(X3s4, mrs_carg("Agatha")).
h10s4_0(X15s4, X9s4) :- except_p(e14s4, X9s4, X15s4).
h10s4_1(X9s4) :- person(X9s4).
h11s4(X15s4, X9s4) :- every_q(X9s4,
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h12s4(X15s4,Val)),
                       (func) = Ret :- Ret = (if h13s4 then yes else no)).
h16s4(X15s4) :- the_q(X15s4,
                      (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h19s4(Val)),
                      (func) = Ret :- Ret = (if h18s4 then yes else no)).
h19s4(X15s4) :- butler_n_1(X15s4).
h4s4(X3s4) :- proper_q(X3s4,
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h7s4(Val)),
                       (func) = Ret :- Ret = (if h6s4 then yes else no)).
h1s4(X3s4, X9s4) :- hate_v_1(e2s4, X3s4, X9s4).
combined4(X15s4, X3s4, X9s4) :- h11s4(X15s4, X9s4), h16s4(X15s4), h19s4(X15s4), h4s4(X3s4), h1s4(X3s4, X9s4).

h6s4 :- true.
h13s4 :- true.
h18s4 :- true.

% Sentence 5
% "The butler hates everyone not richer than Aunt Agatha."
:- pred h11s5(mrs_instance,mrs_instance,mrs_instance).
:- mode h11s5(out,in,in) is nondet.

:- pred h14s5(mrs_instance, mrs_instance, mrs_instance).
:- mode h14s5(in, in, in) is semidet.

:- pred h21s5(mrs_instance, mrs_instance).
:- mode h21s5(out, in) is nondet.

:- pred h29s5(mrs_instance).
:- mode h29s5(out) is det.

:- pred h10s5(mrs_instance,mrs_instance,mrs_instance).
:- mode h10s5(out,in,in) is nondet.

:- pred h15s5_0(mrs_instance).
:- mode h15s5_0(in) is semidet.

:- pred h15s5_1(mrs_instance,mrs_instance).
:- mode h15s5_1(in,in) is semidet.

:- pred h20s5(mrs_instance, mrs_instance).
:- mode h20s5(out, in) is nondet.

:- pred h23s5_0(mrs_instance, mrs_instance).
:- mode h23s5_0(in, in) is det.

:- pred h23s5_1(mrs_instance).
:- mode h23s5_1(out) is nondet.

:- pred h26s5(mrs_instance).
:- mode h26s5(out) is nondet.

:- pred h4s5(mrs_instance).
:- mode h4s5(out) is nondet.

:- pred h7s5(mrs_instance).
:- mode h7s5(out) is nondet.

:- pred h9s5_0(mrs_instance, mrs_instance, mrs_instance).
:- mode h9s5_0(in, in, in) is semidet.

:- pred h9s5_1(mrs_instance).
:- mode h9s5_1(out) is nondet.

:- pred h1s5(mrs_instance, mrs_instance).
:- mode h1s5(in, in) is semidet.

:- pred combined5(mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance).
:- mode combined5(out, out, out, out, out) is nondet.

:- pred h6s5.
:- mode h6s5 is det.

:- pred h12s5.
:- mode h12s5 is det.

:- pred h22s5.
:- mode h22s5 is det.

:- pred h28s5.
:- mode h28s5 is det.

:- func e2s5 = mrs_event.
:- func e13s5 = mrs_event.
:- func e16s5 = mrs_event.
:- func e18s5 = mrs_event.
:- func e24s5 = mrs_event.

e2s5 = mrs_event(2,5).
e13s5 = mrs_event(13,5).
e16s5 = mrs_event(16,5).
e18s5 = mrs_event(18,5).
e24s5 = mrs_event(24,5).

h11s5(X8s5,X19s5,I17s5) :- h9s5_0(X19s5, X8s5, I17s5), h9s5_1(X8s5).
h14s5(X19s5, X8s5, I17s5) :- h15s5_0(X19s5), h15s5_1(X8s5, I17s5).
h21s5(X19s5, X25s5) :- h23s5_0(X19s5, X25s5), h23s5_1(X19s5).
h29s5(X25s5) :- named(X25s5, mrs_carg("Aunt")).
h10s5(X8s5,X19s5,I17s5) :- every_q(X8s5,
                                   (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h11s5(Val,X19s5,I17s5)),
                                   (func) = Ret :- Ret = (if h12s5 then yes else no)).
h15s5_0(X19s5) :- more_comp(e18s5, e16s5, X19s5).
h15s5_1(X8s5,I17s5) :- rich_a_in(e16s5, X8s5, I17s5).
h20s5(X19s5, X25s5) :- proper_q(X19s5,
                                (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h21s5(Val,X25s5)),
                                (func) = Ret :- Ret = (if h22s5 then yes else no)).
h23s5_0(X19s5, X25s5) :- compound(e24s5, X19s5, X25s5).
h23s5_1(X19s5) :- named(X19s5, mrs_carg("Agatha")).
h26s5(X25s5) :- proper_q(X25s5,
                         (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h29s5(Val)),
                         (func) = Ret :- Ret = (if h28s5 then yes else no)).
h4s5(X3s5) :- the_q(X3s5,
                   (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h7s5(Val)),
                   (func) = Ret :- Ret = (if h6s5 then yes else no)).
h7s5(X3s5) :- butler_n_1(X3s5).
h9s5_0(X19s5, X8s5, I17s5) :- X8s5 = X19s5, neg(e13s5, (func) = Ret :- Ret = (if h14s5(X19s5, X8s5, I17s5) then yes else no)). 
h9s5_1(X8s5) :- person(X8s5).
h1s5(X3s5, X8s5) :- hate_v_1(e2s5, X3s5, X8s5).
combined5(X19s5, X25s5, X3s5, X8s5, I17s5) :-
  I17s5 = mrs_instance(mrs_carg("i17s5")),
  h26s5(X25s5),
  h20s5(X19s5, X25s5),
  h10s5(X8s5, X19s5, I17s5),
  h4s5(X3s5),
  h7s5(X3s5).

h6s5 :- true.
h12s5 :- true.
h22s5 :- true.
h28s5 :- true.

% Sentence 6
% "The butler hates everyone Aunt Agatha hates."

:- pred h11s6(mrs_instance, mrs_instance).
:- mode h11s6(in,out) is nondet.

:- pred h15s6(mrs_instance, mrs_instance).
:- mode h15s6(out, in) is nondet.

:- pred h10s6(mrs_instance, mrs_instance).
:- mode h10s6(in,out) is nondet.

:- pred h13s6(mrs_instance, mrs_instance).
:- mode h13s6(out, in) is nondet.

:- pred h17s6_0(mrs_instance,mrs_instance).
:- mode h17s6_0(in,in) is det.

:- pred h17s6_1(mrs_instance).
:- mode h17s6_1(out) is nondet.

:- pred h20s6(mrs_instance,mrs_instance).
:- mode h20s6(out,in) is nondet.

:- pred h23s6(mrs_instance,mrs_instance).
:- mode h23s6(out,in) is nondet.

:- pred h4s6(mrs_instance).
:- mode h4s6(out) is nondet.

:- pred h7s6(mrs_instance).
:- mode h7s6(out) is nondet.

:- pred h9s6_0(mrs_instance, mrs_instance).
:- mode h9s6_0(in, in) is semidet.

:- pred h9s6_1(mrs_instance).
:- mode h9s6_1(out) is nondet.

:- pred h1s6(mrs_instance, mrs_instance).
:- mode h1s6(in, in).

:- pred combined6(mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance).
:- mode combined6(out, out, out, out, out) is nondet.

:- pred h6s6.
:- mode h6s6 is det.

:- pred h12s6.
:- mode h12s6 is det.

:- pred h16s6.
:- mode h16s6 is det.

:- pred h22s6.
:- mode h22s6 is det.

:- func e2s6 = mrs_event.
:- func e18s6 = mrs_event.
:- func e26s6 = mrs_event.

e2s6 = mrs_event(2,6).
e18s6 = mrs_event(18,6).
e26s6 = mrs_event(26,6).

h11s6(X14s6, X8s6) :- h9s6_0(X14s6, X8s6), h9s6_1(X8s6).
h15s6(X14s6, X19s6) :- h17s6_0(X14s6, X19s6), h17s6_1(X14s6).
h10s6(X14s6, X8s6) :- every_q(X8s6,
                              (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h11s6(X14s6,Val)),
                              (func) = Ret :- Ret = (if h12s6 then yes else no)).
h13s6(X14s6, X19s6) :- proper_q(X14s6,
                                (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h15s6(Val,X19s6)),
                                (func) = Ret :- Ret = (if h16s6 then yes else no)).
h17s6_0(X14s6, X19s6) :- compound(e18s6, X14s6, X19s6).
h17s6_1(X14s6) :- named(X14s6, mrs_carg("Agatha")).
h20s6(X19s6,I24s6) :- udef_q(X19s6,
                             (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h23s6(Val,I24s6)),
                             (func) = Ret :- Ret = (if h22s6 then yes else no)).
h23s6(X19s6,I24s6) :- aunt_n_of(X19s6, I24s6).
h4s6(X3s6) :- the_q(X3s6,
                   (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h7s6(Val)),
                   (func) = Ret :- Ret = (if h6s6 then yes else no)).
h7s6(X3s6) :- butler_n_1(X3s6).
h9s6_0(X14s6, X8s6) :- hate_v_1(e26s6, X14s6, X8s6).
h9s6_1(X8s6) :- person(X8s6).
h1s6(X3s6, X8s6) :- hate_v_1(e2s6, X3s6, X8s6).
combined6(X14s6, X19s6, X3s6, X8s6, I24s6) :-
  I24s6 = mrs_instance(mrs_carg("i24s6")),
  h20s6(X19s6, I24s6),
  h13s6(X14s6, X19s6),
  h10s6(X14s6, X8s6),
  h4s6(X3s6),
  X19s6 = X14s6. % aunt_n_of(Agatha)

h6s6 :- true.
h12s6 :- true.
h16s6 :- true.
h22s6 :- true.

% Sentence 7
% "No one hates everyone."
:- pred h10s7(mrs_instance).
:- mode h10s7(out) is nondet.

:- pred h4s7(mrs_instance).
:- mode h4s7(out) is nondet.

:- pred h5s7(mrs_instance).
:- mode h5s7(out) is nondet.

:- pred h9s7(mrs_instance).
:- mode h9s7(out) is nondet.

:- pred h1s7(mrs_instance, mrs_instance).
:- mode h1s7(in, in) is semidet.

:- pred combined7(mrs_instance, mrs_instance).
:- mode combined7(out, out) is nondet.

:- pred h7s7.
:- mode h7s7 is det.

:- pred h12s7. 
:- mode h12s7 is det.

:- func e2s7 = mrs_event.
e2s7 = mrs_event(2,7).

h10s7(X8s7) :- every_q(X8s7, 
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h9s7(Val)),
                       (func) = Ret :- Ret = (if h12s7 then yes else no)).
h4s7(X3s7) :- person(X3s7).
h5s7(X3s7) :- no_q(X3s7,
                   (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h4s7(Val)),
                   (func) = Ret :- Ret = (if h7s7 then yes else no)).
h9s7(X8s7) :- person(X8s7).
h1s7(X3s7, X8s7) :- hate_v_1(e2s7, X3s7, X8s7).
combined7(X3s7, X8s7) :- h10s7(X8s7), h4s7(X3s7), h5s7(X3s7), h9s7(X8s7).

h7s7 :- true.
h12s7 :- true.

% Sentence 8
% "Agatha is not the butler."
:- pred h7s8(mrs_instance).
:- mode h7s8(out).

:- pred h13s8(mrs_instance).
:- mode h13s8(out) is nondet.

:- pred h16s8(mrs_instance).
:- mode h16s8(out) is nondet.

:- pred h4s8(mrs_instance).
:- mode h4s8(out) is nondet.

:- pred h9s8(mrs_instance, mrs_instance).
:- mode h9s8(in,in) is semidet.

:- pred h1s8(mrs_instance, mrs_instance).
:- mode h1s8(in,in) is semidet.

:- pred combined8(mrs_instance,mrs_instance).
:- mode combined8(out,out).

:- pred h15s8.
:- mode h15s8 is det.

:- pred h6s8.
:- mode h6s8 is det.

:- func e2s8 = mrs_event.
e2s8 = mrs_event(2,8).

:- func e11s8 = mrs_event.
e11s8 = mrs_event(11,8).

h7s8(X3s8) :- named(X3s8, mrs_carg("Agatha")).
h13s8(X10s8) :- the_q(X10s8, 
                      (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h16s8(Val)),
                      (func) = Ret :- Ret = (if h15s8 then yes else no)).
h16s8(X10s8) :- butler_n_1(X10s8).
h4s8(X3s8) :- proper_q(X3s8,
                      (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h7s8(Val)),
                      (func) = Ret :- Ret = (if h6s8 then yes else no)).
h9s8(X10s8, X3s8) :- be_v_id(e2s8, X3s8, X10s8).
h1s8(X10s8, X3s8) :- neg(e11s8, (func) = Ret :- Ret = (if h9s8(X10s8, X3s8) then yes else no)).
combined8(X10s8, X3s8) :- h13s8(X10s8), h16s8(X10s8), h4s8(X3s8), h1s8(X10s8, X3s8).

h15s8 :- true.
h6s8 :- true.

% Sentence 9
% "Therefore : Agatha killed herself."
:- pred h16s9(mrs_instance).
:- mode h16s9(out) is det.

:- pred h12s9(mrs_instance).
:- mode h12s9(out) is nondet.

:- pred h18s9(mrs_instance, mrs_instance).
:- mode h18s9(in,in) is semidet.

:- pred h21s9(mrs_instance).
:- mode h21s9(in) is det.

:- pred h22s9(mrs_instance).
:- mode h22s9(in) is semidet.

:- pred h4s9.
:- mode h4s9 is det.

:- pred h6s9(mrs_instance).
:- mode h6s9(in) is semidet.

:- pred h1s9(mrs_instance, mrs_instance,mrs_instance).
:- mode h1s9(in,in,in) is semidet.

:- pred combined9(mrs_instance, mrs_instance).
:- mode combined9(out, out).

:- pred h15s9.
:- mode h15s9 is det.

:- pred h24s9.
:- mode h24s9 is det.

:- func e2s9 = mrs_event.
e2s9 = mrs_event(2,9).

:- func e9s9 = mrs_event.
e9s9 = mrs_event(9,9).

:- func e19s9 = mrs_event.
e19s9 = mrs_event(19,9).

:- func u5s9 = mrs_unknown.
u5s9 = mrs_unknown(5,9).

h16s9(X13s9) :- named(X13s9, mrs_carg("Agatha")).
h12s9(X13s9) :- proper_q(X13s9, 
                         (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h16s9(Val)),
                         (func) = Ret :- Ret = (if h15s9 then yes else no)).

h18s9(X13s9, X20s9) :- kill_v_1(e19s9, X13s9, X20s9).
h21s9(X20s9) :- pron(X20s9).
h22s9(X20s9) :- pronoun_q(X20s9, 
                          (func) = Ret :- Ret = (if h21s9(X20s9) then [X20s9] else []),
                          (func) = Ret :- Ret = (if h24s9 then yes else no)).
h4s9 :- unknown(u5s9, e2s9).
h6s9(I7s9) :- therefore_a_1(I7s9, (func) = Ret :- Ret = (if h4s9 then yes else no)).
h1s9(X13s9, X20s9, I7s9) :- colon_p_namely(e9s9,
                                           (func) = Ret :- Ret = (if h6s9(I7s9) then yes else no),
                                           (func) = Ret :- Ret = (if h18s9(X13s9, X20s9) then yes else no)).

combined9(X13s9, X20s9) :-
  I7s9 = mrs_instance(mrs_carg("i7s9")),
  h12s9(X13s9),
  X20s9 = X13s9,
  h22s9(X20s9),
  h4s9,
  h1s9(X13s9,X20s9,I7s9).

h15s9 :- true.

h24s9 :- true.


:- pred combined(mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance,
                 mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance,
                 mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance,
                 mrs_instance, mrs_instance, mrs_instance, mrs_instance,
                 mrs_instance, mrs_instance, mrs_instance,
                 mrs_instance, mrs_instance, mrs_instance, mrs_instance,
                 mrs_instance, mrs_instance, mrs_instance, mrs_instance,
                 mrs_instance, mrs_instance,
                 mrs_instance, mrs_instance,
                 mrs_instance, mrs_instance
                ).
:- mode combined(out, out, out, out, out, 
                 out, out, out, out, out, out, out, out, 
                 out, out, out, out, out,
                 out, out, out, out,
		 out, out, out,
                 out, out, out, out,
                 out, out, out, out,
		 out, out,
		 out, out,
		 out, out
		).
combined(X10s0, X16s0, X23s0, X29s0, X3s0, 
         X14s1, X19s1, X24s1, X32s1, X38s1, X3s1, X46s1, X8s1,
	 X10s2, X16s2, X28s2, X34s2, X3s2,
	 X17s3, X22s3, X3s3, X9s3,
         X15s4, X3s4, X9s4,
         X19s5, X25s5, X3s5, X8s5,
         X14s6, X19s6, X3s6, X8s6,
	 X3s7, X8s7,
         X10s8, X3s8,
         X13s9, X20s9
	) :-
   combined0(X10s0,X16s0,X23s0,X29s0,X3s0),
   combined1(X14s1, X19s1, X24s1, X32s1, X38s1, X3s1, X46s1, X8s1, I52s1),
   coref(X23s0,X8s1), % Agatha
   coref(X16s0,X38s1), % Dreadbury
   coref(X10s0,X32s1), % Mansion
   combined2(I8s2, I23s2, I26s2, I39s2, X10s2, X16s2, X28s2, X34s2, X3s2),
   X10s2 = X28s2, % victims refer to same people, for same killer
   combined3(X17s3, X22s3, X3s3, X9s3, I27s3),
   coref(X23s0,X17s3), % Agatha
   coref(X24s1,X3s3), % Charles
   combined4(X15s4, X3s4, X9s4),
   coref(X23s0,X3s4), % Agatha
   coref(X19s1,X15s4), % butler
   combined5(X19s5, X25s5, X3s5, X8s5, I17s5),
   coref(X29s0,X25s5), % Aunt
   coref(X23s0,X19s5), % Agatha
   coref(X19s1,X3s5), % butler
   combined6(X14s6, X19s6, X3s6, X8s6, I24s6),
   coref(X23s0,X14s6), % Agatha
   coref(X19s1,X3s6), % butler
   combined7(X3s7, X8s7),
   combined8(X10s8, X3s8),
   coref(X23s0,X3s8), % Agatha
   coref(X19s1,X10s8), % butler
   combined9(X13s9,X20s9),
   coref(X23s0,X13s9) % Agatha
   .

main(!IO) :- 
%   solutions(pred({X10s0,X16s0,X23s0,X29s0,X3s0,
%	           X14s1,X19s1,X24s1,X32s1,X38s1,X3s1,X46s1,X8s1,I52s1,
%                   I8s2, I23s2, I26s2, I39s2, X10s2, X16s2, X28s2, X34s2, X3s2,
%                   X17s3, X22s3, X3s3, X9s3, I27s3,
%                   X15s4, X3s4, X9s4,
%                   X19s5, X25s5, X3s5, X8s5, I17s5,
%                   X14s6, X19s6, X3s6, X8s6, I24s6,
%                   X3s7, X8s7,
%                   X10s8, X3s8,
%                   X13s9, X20s9
%		  }::out) is nondet :- 
%             combined(X10s0,X16s0,X23s0,X29s0,X3s0,
%                      X14s1,X19s1,X24s1,X32s1,X38s1,X3s1,X46s1,X8s1,I52s1,
%                      X10s2, X16s2, X28s2, X34s2, X3s2,
%                      X17s3, X22s3, X3s3, X9s3, I27s3,
%                      X15s4, X3s4, X9s4,
%                      X19s5, X25s5, X3s5, X8s5, I17s5,
%                      X14s6, X19s6, X3s6, X8s6, I24s6,
%                      X3s7, X8s7,
%                      X10s8, X3s8,
%                      X13s9, X20s9
%		     ), Ret),
%   length(Ret,Len),
%   io.print(Len,!IO),
%   io.nl(!IO).

  solutions(pred({X10s0,X16s0,X23s0,X29s0,X3s0,
                  X14s1, X19s1, X24s1, X32s1, X38s1, X3s1, X46s1, X8s1,
                  X10s2, X16s2, X28s2, X34s2, X3s2,
	          X17s3, X22s3, X3s3, X9s3,
                  X15s4, X3s4, X9s4,
                  X19s5, X25s5, X3s5, X8s5,
                  X14s6, X19s6, X3s6, X8s6,
                  X3s7, X8s7,
                  X10s8, X3s8,
                  X13s9, X20s9
	         }::out) is nondet :- 
	    combined(X10s0,X16s0,X23s0,X29s0,X3s0,
                     X14s1, X19s1, X24s1, X32s1, X38s1, X3s1, X46s1, X8s1,
                     X10s2, X16s2, X28s2, X34s2, X3s2,
	             X17s3, X22s3, X3s3, X9s3,
                     X15s4, X3s4, X9s4,
                     X19s5, X25s5, X3s5, X8s5,
                     X14s6, X19s6, X3s6, X8s6,
                     X3s7, X8s7,
                     X10s8, X3s8,
                     X13s9, X20s9
                    )
	   ,Ret0123456789),
  
  Out = list.filter_map(func({X10s0,X16s0,X23s0,X29s0,X3s0,
                         X14s1, X19s1, X24s1, X32s1, X38s1, X3s1, X46s1, X8s1,
                         X10s2, X16s2, X28s2, X34s2, X3s2,
                         X17s3, X22s3, X3s3, X9s3,
                         X15s4, X3s4, X9s4,
                         X19s5, X25s5, X3s5, X8s5,
                         X14s6, X19s6, X3s6, X8s6,
                         X3s7, X8s7,
                         X10s8, X3s8,
                         X13s9, X20s9
		        }) = Ret is semidet :- if X23s0 = X28s2 then Ret = {X13s9,X20s9} else false, Ret0123456789),
  % victim_n_of X10s2: {Agatha,Charles,TheButler}
  % X16s2: pron0
  % victim_n_of X28s2: {Agatha,Charles,TheButler}
  % X34s2: pron0
  % killer_n_of X3s2: {Agatha,Charles,TheButler,TheKiller}
  % pretty_printer.write_doc(pretty_printer.format(Ret012),!IO),
  % io.nl(!IO),
  set.list_to_set(Out,S),
  set.to_sorted_list(S,L),
  io.print(L,!IO),
  io.nl(!IO),
  length(L,Len),
  io.print(Len,!IO),
  io.nl(!IO).
%  {X10s0,X16s0,X23s0,X29s0,X3s0} = det_head(Ret0),
%  solutions(pred({X14s1, X19s1, X24s1, X32s1, X38s1, X3s1, X46s1, X8s1, I52s1}::out) is nondet :-
%            (combined1(X14s1,X19s1,X24s1,X32s1,X38s1,X3s1,X46s1,X8s1,I52s1),
%             coref(X23s0,X8s1), % Agatha
%             coref(X16s0,X38s1), % Dreadbury
%             coref(X10s0,X32s1) % Mansion
%            ),Ret1),
%  io.print(Ret1,!IO),
%  io.nl(!IO).
%  {X14s1, X19s1, X24s1, X32s1, X38s1, X3s1, X46s1, X8s1, I52s1} = det_head(Ret1),
%  solutions(pred({I8s2, I23s2, I26s2, I39s2, X10s2, X16s2, X28s2, X34s2, X3s2}::out) is nondet :- combined2(I8s2, I23s2, I26s2, I39s2, X10s2, X16s2, X28s2, X34s2, X3s2),Ret2),
%  io.print(Ret2,!IO),
%  io.nl(!IO),
%  solutions(pred({X17s3, X22s3, X3s3, X9s3, I27s3}::out) is nondet :-
%            (combined3(X17s3, X22s3, X3s3, X9s3, I27s3),
%             coref(X23s0,X17s3), % Agatha
%             coref(X24s1,X3s3) % Charles
%            ), Ret3),
%  io.print(Ret3,!IO),
%  io.nl(!IO),
%  solutions(pred({X15s4, X3s4, X9s4}::out) is nondet :-
%            (combined4(X15s4, X3s4, X9s4),
%             coref(X23s0,X3s4), % Agatha
%             coref(X19s1,X15s4) % butler
%            ), Ret4),
%  io.print(Ret4,!IO),
%  io.nl(!IO),
%  solutions(pred({X19s5, X25s5, X3s5, X8s5, I17s5}::out) is nondet :-
%            (combined5(X19s5, X25s5, X3s5, X8s5, I17s5),
%             coref(X29s0,X25s5), % Aunt
%             coref(X23s0,X19s5), % Agatha
%             coref(X19s1,X3s5) % butler
%            ), Ret5),
%  io.print(Ret5,!IO),
%  io.nl(!IO),
%  solutions(pred({X14s6, X19s6, X3s6, X8s6, I24s6}::out) is nondet :-
%            (combined6(X14s6, X19s6, X3s6, X8s6, I24s6),
%             coref(X23s0,X14s6), % Agatha
%             coref(X19s1,X3s6) % butler
%            ), Ret6),
%  io.print(Ret6,!IO),
%  io.nl(!IO),
%  solutions(pred({X3s7, X8s7}::out) is nondet :-
%            (combined7(X3s7, X8s7)
%            ), Ret7),
%  io.print(Ret7,!IO),
%  io.nl(!IO),
%  solutions(pred({X10s8, X3s8}::out) is nondet :-
%            (combined8(X10s8, X3s8),
%             coref(X23s0,X3s8), % Agatha
%             coref(X19s1,X10s8) % butler
%            ), Ret8),
%  io.print(Ret8,!IO),
%  io.nl(!IO),
%  solutions(pred({X13s9,X20s9}::out) is nondet :-
%            (combined9(X13s9,X20s9),
%             coref(X23s0,X13s9) % Agatha
%            ), Ret9),
%  io.print(Ret9,!IO),
%  io.nl(!IO).

