#!/bin/bash

cat << EOF
:- module sentence_unpackRelation.
:- interface.
:- import_module mrs.
:- import_module multi_map.
:- import_module sentence_predicates.
:- import_module sentence_types.
:- import_module set.

:- pred unpackRelation(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                       multi_map(mrs_types,mrs_rel_handle),
                       mrs_rel_handle,preds,
		       set(string),set(string),sentence_dependency,sentence_dependency).
:- mode unpackRelation(in,in,in,in,in,out,in,out) is det.

:- implementation.
:- import_module require.
:- import_module solutions.
:- import_module list.
:- import_module calls.
:- import_module string.
:- import_module io.
:- import_module unsafe.

:- pred expandHandle(mrs_rel_handle,
                     multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                     multi_map(mrs_types, mrs_rel_handle),
                     set(string),set(string),sentence_dependency,sentence_dependency).
:- mode expandHandle(in,in,in,in,out,in,out).
:- pragma promise_pure(expandHandle/7).
expandHandle(RelHandle0,RelMap,ArgMap,SignaturesIn0,SignaturesOut0,DependenciesIn0,DependenciesOut0) :-
   % impure unsafe_perform_io(print("expandHandle:")),
   % impure unsafe_perform_io(print(RelHandle0)),
   % impure unsafe_perform_io(print("\n")),
   (if multi_map.contains(RelMap,RelHandle0) then
     multi_map.lookup(RelMap,RelHandle0,Rels0),
     list.foldl2(pred({RelHandle0Ref,_,_,Pred0}::in,SignaturesIn1::in,SignaturesOut1::out,DependenciesIn1::in,DependenciesOut1::out) is det :- 
                  unpackRelation(RelMap,ArgMap,RelHandle0Ref,Pred0,SignaturesIn1,SignaturesOut1,DependenciesIn1,DependenciesOut1),
                Rels0,SignaturesIn0,SignaturesOut0,DependenciesIn0,DependenciesOut0)
    else
      SignaturesOut0 = SignaturesIn0,
      DependenciesOut0 = DependenciesIn0
      ).

:- pred expandArg(mrs_rel_handle,
                           multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                           multi_map(mrs_types, mrs_rel_handle),
                           mrs_types,
                           set(string),
                           set(string),
                           sentence_dependency,
                           sentence_dependency).
:- mode expandArg(in,in,in,in,in,out,in,out).
:- pragma promise_pure(expandArg/8).
expandArg(RelHandle,RelMap,ArgMap,AT,SignaturesIn,SignaturesOut,DependenciesIn,DependenciesOut) :-
  multi_map.lookup(ArgMap,AT,Rels),
  % impure unsafe_perform_io(print("expandArg:")),
  % impure unsafe_perform_io(print({AT,Rels})),
  % impure unsafe_perform_io(print("\n")),
  list.foldl2(pred(RelHandle0::in,SignaturesIn0::in,SignaturesOut0::out,DependenciesIn0::in,DependenciesOut0::out) is det :- 
    expandHandle(RelHandle0,RelMap,ArgMap,SignaturesIn0,SignaturesOut0,DependenciesIn0,DependenciesOut0),
    Rels,SignaturesIn,SignaturesOut,DependenciesIn,DependenciesOut).

:- pragma promise_pure(unpackRelation/8).
unpackRelation(RelMap,ArgMap,RelHandle,Pred,SignaturesIn,SignaturesOut,DependenciesIn,DependenciesOut) :-
EOF

sed -n '/mrs/s/.*pred_\([a-z0-9_]*\)(pred(\(mrs_rel_handle,[^)]*\)))/\1\,\2/p' sentence_predicates.m | tr -d ' ' | tr -d . > _predicate_table

declare -a ArgAry
declare -a WrapExprs

for line in `cat _predicate_table`; do
  set -- `echo $line | tr , ' '`
  pred=$1
  shift
  shift # skip the handle
  IndivPos=0
  InstPos=0
  RelHandlePos=0
  RstrHandlePos=0
  BodyHandlePos=0
  CargPos=0
  UnknownPos=0
  delim=""
  Args=""
  ArgPos=0
  EventPos=0
  echo "  ${lineDelim}if pred_${pred}(_) = Pred then"
  while test -n "$1"; do
    Types[${ArgPos}]=$1
    case $1 in
      mrs_indiv)
        Var=Indiv${IndivPos}
	Rhs=$Var
        IndivPos=$((${IndivPos} + 1))
        WrapExpr="wrap_indiv(${Var})"
        ;;
      mrs_inst)
        Var=Inst${InstPos}
	Rhs=$Var
        InstPos=$((${InstPos} + 1))
        WrapExpr="wrap_inst(${Var})"
        ;;
      mrs_event)
        Var=Event${EventPos}
	Rhs=$Var
        EventPos=$((${EventPos} + 1))
        WrapExpr="wrap_event(${Var})"
        ;;
      mrs_rel_handle)
	Var="mrs_rel_handle(RelHandle${RelHandlePos})"
	Rhs="mrs_rel_handle(RelHandle${RelHandlePos})"
        RelHandlePos=$((${RelHandlePos} + 1))
        WrapExpr="wrap_rel_handle(${Var})"
        ;;
      mrs_rstr_handle)
	Var="mrs_rstr_handle(RstrHandle${RstrHandlePos})"
	Types[${ArgPos}]=mrs_rel_handle
	Rhs="mrs_rel_handle(RstrHandle${RstrHandlePos})"
        RstrHandlePos=$((${RstrHandlePos} + 1))
        WrapExpr="wrap_rstr_handle(${Var})"
        ;;
      mrs_body_handle)
	Var="mrs_body_handle(BodyHandle${BodyHandlePos})"
	Types[${ArgPos}]=mrs_rel_handle
	Rhs="mrs_rel_handle(BodyHandle${BodyHandlePos})"
        BodyHandlePos=$((${BodyHandlePos} + 1))
        WrapExpr="wrap_body_handle(${Var})"
        ;;
      mrs_carg)
        Var=Carg${CargPos}
	Rhs=$Var
        CargPos=$((${CargPos} + 1))
        WrapExpr="wrap_carg(${Var})"
        ;;
      mrs_unknown)
        Var=Unk${UnknownPos}
	Rhs=$Var
        UnknownPos=$((${UnknownPos} + 1))
        WrapExpr="wrap_unknown(${Var})"
        ;;
      *)
        exit 1
        ;;
     esac
     Args="${Args}${delim}${Var}"
     ArgAry[${ArgPos}]=${Var}
     Vars[${ArgPos}]=$Rhs
     WrapExprs[${ArgPos}]=${WrapExpr}
     delim=","
     shift
     ArgPos=$((${ArgPos} + 1))
  done
  ArgCount=${ArgPos}
  echo "    solutions(pred({${Args}}::out) is nondet :- ${pred}(RelHandle,${Args}), L),"
  echo "    list.foldl2(pred({${Args}}::in,SignaturesIn0::in,SignaturesOut0::out,DependenciesIn0::in,DependenciesOut0::out) is det :-"
  echo "               (Cmd = string.append_list([\"${pred}(\","
  for ArgPos in `seq 0 $((${ArgCount} - 2))`; do
      echo "                  to_string(${ArgAry[${ArgPos}]}),\",\","
  done      
  echo "                  to_string(${ArgAry[$((${ArgCount}-1))]}), \")\"]),"
  echo "                (if set.member(Cmd,SignaturesIn0) then"
  echo "                   SignaturesOut0 = SignaturesIn0,"
  echo "                   DependenciesOut0 = DependenciesIn0"
  echo "                 else"
  echo "                   (set.insert(Cmd,SignaturesIn0,Signatures0),"
  echo "                    Dependencies0 = list.append(DependenciesIn0,[argument(Cmd)]),"
  LastPos=$(($ArgCount - 1))
  for ArgPos in `seq 0 $LastPos`; do
    if test $ArgPos = $LastPos; then
      svarIn=Signatures$LastPos
      svarOut=SignaturesOut0
      dvarIn=Dependencies$LastPos
      dvarOut=DependenciesOut0
      delim=""
    else
      svarIn=Signatures${ArgPos}
      svarOut=Signatures$((${ArgPos} + 1))
      dvarIn=Dependencies${ArgPos}
      dvarOut=Dependencies$((${ArgPos} + 1))
      delim=","
    fi         
    if test ${Types[$ArgPos]} = mrs_rel_handle; then
      echo "                    ((if multi_map.contains(RelMap,${Vars[$ArgPos]}) then"
      echo "                        TL$ArgPos = multi_map.lookup(RelMap,${Vars[$ArgPos]}),"
      echo "                        RL$ArgPos = list.map(func({RelHandleA,_,_,_}) = Ret :- Ret = RelHandleA,TL$ArgPos)"
      echo "                      else"
      echo "                        RL$ArgPos = [${Vars[$ArgPos]}]),"
      echo "                     list.foldl2(pred(RelHandleA::in,S0In::in,S0Out::out,O0In::in,O0Out::out) is det :- expandArg(RelHandle,RelMap,ArgMap,wrap_rel_handle(RelHandleA),S0In,S0Out,O0In,O0Out),RL$ArgPos,$svarIn,$svarOut,[],Child$ArgPos)),"
    else
      echo "                    expandArg(RelHandle,RelMap,ArgMap,${WrapExprs[$ArgPos]},$svarIn,$svarOut,[],Child$ArgPos),"
    fi
    echo "                    (if list.length(Child$ArgPos) = 0 then"
    echo "                      $dvarOut = $dvarIn"
    echo "                    else"
    echo "                      $dvarOut = list.append($dvarIn,[dependency(Child$ArgPos)]))$delim"
  done
  echo "              ))),"
  echo "              L,SignaturesIn,SignaturesOut,DependenciesIn,DependenciesOut)"
  lineDelim="else "
done

cat << EOF
  else
    impure unsafe_perform_io(print(Pred)),
    error("unknown predicate").
EOF
