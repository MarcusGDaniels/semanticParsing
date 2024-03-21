:- module s01.
:- interface.

:- import_module bool.
:- import_module list.
:- import_module io.

:- type mrs_instance ---> mrs_instance(mrs_carg).
:- type mrs_carg ---> mrs_carg(string).
:- type mrs_event ---> mrs_event(int,int).

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
:- pred udef_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode udef_q(out, in, in) is nondet.
:- pred the_q(mrs_instance, (func) = list(mrs_instance), (func) = bool).
:- mode the_q(out, in, in) is nondet.

:- pred in_p_loc(mrs_event, mrs_event, mrs_instance).
:- mode in_p_loc(in, in, in) is det.

:- pred compound(mrs_event, mrs_instance, mrs_instance).
:- mode compound(in, in, in) is det.

:- pred kill_v_1(mrs_event, mrs_instance, mrs_instance).
:- mode kill_v_1(in, in, in) is semidet.

:- pred implicit_conj(mrs_instance, mrs_instance, mrs_instance).
:- mode implicit_conj(out, in, in) is det.

:- pred live_v_1(mrs_event, mrs_instance).
:- mode live_v_1(in, in) is det.

:- pred only_a_1(mrs_event, mrs_instance).
:- mode only_a_1(in, in) is det.

:- pred be_v_id(mrs_event, mrs_instance, mrs_instance).
:- mode be_v_id(in, in, in) is det.

:- pred person(mrs_instance).
:- mode person(out) is nondet.

:- pred and_c_e(mrs_event, mrs_event, mrs_event).
:- mode and_c_e(in,in,in) is det.

:- pred and_c_x(mrs_instance, mrs_instance, mrs_instance).
:- mode and_c_x(out,in,in) is nondet.

:- pred butler_n_1(mrs_instance).
:- mode butler_n_1(out) is det.

:- pred people_n_of(mrs_instance,mrs_instance).
:- mode people_n_of(out,in) is nondet.

:- pred therein_p_dir(mrs_event,mrs_event).
:- mode therein_p_dir(in,in) is det.

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

:- pred combined1(mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance, mrs_instance).
:- mode combined1(out,out,out,out,out,out,out,out,out,in,in,in) is nondet.

:- pred coref(mrs_instance, mrs_instance).
:- mode coref(in,in) is semidet.

:- implementation.
:- import_module solutions.
:- import_module string.

% ERG predicate definitions
named(Inst, Carg) :- Inst = mrs_instance(Carg).

the_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).
proper_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).
udef_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).
some_q(Inst, FuncR, FuncB) :- list.member(Inst,apply(FuncR)).

in_p_loc(E0, E1, Inst) :- true.

compound(E, Inst0, Inst1) :- true.

live_v_1(E, Inst0) :- true.

only_a_1(E, Inst0) :- true.

be_v_id(E, Inst0, Inst1) :- true.

kill_v_1(E, Inst0, Inst1) :- true.

implicit_conj(I0,I1,I2) :- 
  mrs_instance(mrs_carg(Name1)) = I1,
  mrs_instance(mrs_carg(Name2)) = I2,
  I0 = mrs_instance(mrs_carg("implicit_conj_" ++ Name1 ++ "_" ++ Name2)).

butler_n_1(Inst) :- Inst = mrs_instance(mrs_carg("TheButler")).

person(mrs_instance(mrs_carg("Agatha"))).

and_c_e(E0, E1, E2) :- true.

and_c_x(I0, I1, I2) :- 
  mrs_instance(mrs_carg(Name1)) = I1,
  mrs_instance(mrs_carg(Name2)) = I2,
  I0 = mrs_instance(mrs_carg("and_c_x_" ++ Name1 ++ "_" ++ Name2)).

people_n_of(Inst0, Inst1) :- person(Inst0).

therein_p_dir(E0, E1) :- true.

coref(A,B) :- A = B.

% -- Sentence 0
% "Someone who lives in Dreadbury Mansion killed Aunt Agatha." 0

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

combined0(X10s0, X16s0, X23s0, X29s0, X3s0) :- h1s0(X23s0, X3s0), h11s0(X10s0, X16s0), h17s0(X16s0), h24s0(X23s0, X29s0), h30s0(X29s0), h5s0(X10s0, X3s0).

% --- Sentence 1
% "Agatha, the butler, and Charles live in Dreadbury Mansion, and are the only people who live therein." 1
% X8s1,    X19s1,          X24s1

:- pred h0s1(mrs_instance,mrs_instance,mrs_instance).
:- mode h0s1(in,in,in).

:- pred h11s1(mrs_instance).
:- mode h11s1(out) is semidet.

:- pred h28s1(mrs_instance).
:- mode h28s1(out) is semidet.

:- pred h34s1(mrs_instance,mrs_instance).
:- mode h34s1(out,in) is semidet.

:- pred h42s1(mrs_instance).
:- mode h42s1(out) is semidet.

:- pred h48s1(mrs_instance,mrs_instance).
:- mode h48s1(out,in) is nondet.

:- pred h13s1(mrs_instance,mrs_instance,mrs_instance).
:- mode h13s1(out,in,in) is nondet.

:- pred h17s1(mrs_instance,mrs_instance,mrs_instance).
:- mode h17s1(in,out,in) is det.

:- pred h18s1(mrs_instance).
:- mode h18s1(out) is nondet.

:- pred h1s1_0.
:- mode h1s1_0 is det. 

:- pred h1s1_1(mrs_instance,mrs_instance).
:- mode h1s1_1(in,in) is det.

:- pred h1s1_2(mrs_instance).
:- mode h1s1_2(in) is det.

:- pred h1s1_3(mrs_instance).
:- mode h1s1_3(in) is det.

:- pred h22s1(mrs_instance).
:- mode h22s1(out) is det.

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
:- mode h47s1(out,in).

:- pred h4s1(mrs_instance,mrs_instance,mrs_instance).
:- mode h4s1(in,in,in).

:- pred h50s1_0(mrs_instance).
:- mode h50s1_0(in).

:- pred h50s1_1(mrs_instance).
:- mode h50s1_1(in) is semidet.

:- pred h50s1_2(mrs_instance,mrs_instance).
:- mode h50s1_2(out,in) is nondet.

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
                       (func) = Ret :- Ret = solutions(pred(Val::out) is nondet :- h48s1(Val,I52s1)),
                       (func) = Ret :- Ret = (if h49s1 then yes else no)).
h4s1(X14s1, X3s1, X8s1) :- udef_q(X3s1,
                       (func) = Ret :- Ret = (if h17s1(X14s1,X3s1,X8s1) then [X3s1] else []),
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

combined1(X14s1, X19s1, X24s1, X32s1, X38s1, X3s1, X46s1, X8s1, I52s1, X23s0, X16s0, X10s0) :- 
   h7s1(X8s1),
   coref(X23s0,X8s1), % Agatha
   h39s1(X38s1),
   coref(X16s0,X38s1), % Dreadbury
   h33s1(X32s1, X38s1),
   coref(X10s0,X32s1), % Mansion
   h25s1(X24s1),
   h22s1(X19s1),
   h18s1(X19s1),
   h13s1(X14s1, X19s1, X24s1),

   h13s1(X14s1,X19s1,X24s1),
   h17s1(X14s1, X3s1, X8s1),
   I52s1 = mrs_instance(mrs_carg("1")),
   h47s1(X46s1,I52s1),
   h4s1(X14s1, X3s1, X8s1).

main(!IO) :- 
% should return (Mansion, Dreadybury, Agatha, Aunt, Agatha)
  solutions(pred({X10s0,X16s0,X23s0,X29s0,X3s0}::out) is nondet :- combined0(X10s0,X16s0,X23s0,X29s0,X3s0),Ret0),
  {X10s0a,X16s0a,X23s0a,_,_} = list.det_head(Ret0),
  solutions(pred({X14s1, X19s1, X24s1, X32s1, X38s1, X3s1, X46s1, X8s1, I52s1}::out) is nondet :- combined1(X14s1,X19s1,X24s1,X32s1,X38s1,X3s1,X46s1,X8s1,I52s1,X23s0a,X16s0a,X10s0a),Ret1),
  io.print(Ret1,!IO),
  io.nl(!IO). 
  
