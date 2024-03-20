:- module s0.
:- interface.

:- import_module bool.
:- import_module list.
:- import_module io.

:- type mrs_instance ---> mrs_instance(mrs_carg).
:- type mrs_carg ---> mrs_carg(string).
:- type mrs_event ---> mrs_event(int).

:- pred main(io::di, io::uo) is det.

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

:- pred named(mrs_instance, mrs_carg).
:- mode named(out, in) is det.

:- pred proper_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode proper_q(out, in, in) is nondet.
:- pred some_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode some_q(out, in, in) is nondet.

:- pred in_p_loc(mrs_event, mrs_event, mrs_instance).
:- mode in_p_loc(in, in, in) is det.

:- pred compound(mrs_event, mrs_instance, mrs_instance).
:- mode compound(in, in, in) is det.

:- pred kill_v_1(mrs_event, mrs_instance, mrs_instance).
:- mode kill_v_1(in, in, in) is semidet.

:- pred live_v_1(mrs_event, mrs_instance).
:- mode live_v_1(in, in) is det.

:- pred person(mrs_instance).
:- mode person(out) is nondet.

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

:- pred combined(mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance).
:- mode combined(out,out,out,out,out) is nondet.

:- implementation.
:- import_module solutions.

e15s0 = mrs_event(1).
e2s0 = mrs_event(2).
e28s0 = mrs_event(3).
e8s0 = mrs_event(4).
e9s0 = mrs_event(5).

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

named(Inst, Carg) :- Inst = mrs_instance(Carg).

proper_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).

some_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).

in_p_loc(E0, E1, Inst) :- true.

compound(E, Inst0, Inst1) :- true.

live_v_1(E, Inst0) :- true.

kill_v_1(E, Inst0, Inst1) :- true.

person(mrs_instance(mrs_carg("Agatha"))).

h13s0 :- true.
h19s0 :- true.
h26s0 :- true.
h32s0 :- true.
h7s0 :- true.

combined(X10s0, X16s0, X23s0, X29s0, X3s0) :- h1s0(X23s0, X3s0), h11s0(X10s0, X16s0), h17s0(X16s0), h24s0(X23s0, X29s0), h30s0(X29s0), h5s0(X10s0, X3s0).

main(!IO) :- 
% should return (Mansion, Dreadybury, Agatha, Aunt, Agatha)
  solutions(pred({X10s0,X16s0,X23s0,X29s0,X3s0}::out) is nondet :- combined(X10s0,X16s0,X23s0,X29s0,X3s0),Ret),
  io.print(Ret,!IO),
  io.nl(!IO). 
  
