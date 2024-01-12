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
		       set(string),set(string)).
:- mode unpackRelation(in,in,in,in,in,out) is det.

:- implementation.
:- import_module require.
:- import_module solutions.
:- import_module list.
:- import_module calls.
:- import_module string.
:- import_module io.
:- import_module unsafe.

:- pred expandSentenceType(mrs_rel_handle,
                           multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                           multi_map(mrs_types, mrs_rel_handle),
                           mrs_types,
                           set(string),
                           set(string)).
:- mode expandSentenceType(in,in,in,in,in,out).
expandSentenceType(RelHandle,RelMap,ArgMap,ST,OutputsIn,OutputsOut) :-
  (multi_map.lookup(ArgMap,ST,Rels),
   list.foldl(pred(RelHandle0::in,OutputsIn0::in,OutputsOut0::out) is det :- 
     (if RelHandle0 = RelHandle then
        OutputsOut0 = OutputsIn0
      else
        multi_map.lookup(RelMap,RelHandle0,Rels0),
        list.foldl(pred({RelHandle0Ref,_,_,Pred0}::in,OutputsIn1::in,OutputsOut1::out) is det :- 
                        unpackRelation(RelMap,ArgMap,RelHandle0Ref,Pred0,OutputsIn1,OutputsOut1),
                   Rels0,OutputsIn0,OutputsOut0)),
       Rels,OutputsIn,OutputsOut)).

:- pragma promise_pure(unpackRelation/6).
unpackRelation(RelMap,ArgMap,RelHandle,Pred,OutputsIn,OutputsOut) :-
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
    case $1 in
      mrs_indiv)
        Var=Indiv${IndivPos}
        IndivPos=$((${IndivPos} + 1))
        WrapExpr="wrap_indiv(${Var})"
        ;;
      mrs_inst)
        Var=Inst${InstPos}
        InstPos=$((${InstPos} + 1))
        WrapExpr="wrap_inst(${Var})"
        ;;
      mrs_event)
        Var=Event${EventPos}
        EventPos=$((${EventPos} + 1))
        WrapExpr="wrap_event(${Var})"
        ;;
      mrs_rel_handle)
        Var=RelHandle${RelHandlePos}
        RelHandlePos=$((${RelHandlePos} + 1))
        WrapExpr="wrap_rel_handle(${Var})"
        ;;
      mrs_rstr_handle)
        Var=RstrHandle${RstrHandlePos}
        RstrHandlePos=$((${RstrHandlePos} + 1))
        WrapExpr="wrap_rstr_handle(${Var})"
        ;;
      mrs_body_handle)
        Var=BodyHandle${BodyHandlePos}
        BodyHandlePos=$((${BodyHandlePos} + 1))
        WrapExpr="wrap_body_handle(${Var})"
        ;;
      mrs_carg)
        Var=Carg${CargPos}
        CargPos=$((${CargPos} + 1))
        WrapExpr="wrap_carg(${Var})"
        ;;
      mrs_unknown)
        Var=Unk${UnknownPos}
        UnknownPos=$((${UnknownPos} + 1))
        WrapExpr="wrap_unknown(${Var})"
        ;;
      *)
        exit 1
        ;;
     esac
     Args="${Args}${delim}${Var}"
     ArgAry[${ArgPos}]=${Var}
     WrapExprs[${ArgPos}]=${WrapExpr}
     delim=","
     shift
     ArgPos=$((${ArgPos} + 1))
  done
  ArgCount=${ArgPos}
  echo "    solutions(pred({${Args}}::out) is nondet :- ${pred}(RelHandle,${Args}), L),"
  echo "    list.foldl(pred({${Args}}::in,OutputsIn0::in,OutputsOut0::out) is det :-"
  echo "               (Cmd = \"${pred}(\""
  for ArgPos in `seq 0 $((${ArgCount} - 2))`; do
      echo "                  ++ to_string(${ArgAry[${ArgPos}]}) ++ \",\""
  done      
  echo "                  ++ to_string(${ArgAry[$((${ArgCount}-1))]}) ++ \")\","
  echo "                (if set.member(Cmd,OutputsIn0) then"
  echo "                   OutputsOut0 = OutputsIn0"
  echo "                 else"
  echo "                   (set.insert(Cmd,OutputsIn0,Outputs0),"
  for ArgPos in `seq 0 $((${ArgCount} - 2))`; do
      echo   "                    expandSentenceType(RelHandle,RelMap,ArgMap,${WrapExprs[$ArgPos]},Outputs${ArgPos},Outputs$((${ArgPos} + 1))),"
  done
  LastPos=$(($ArgCount - 1))
  echo "                    expandSentenceType(RelHandle,RelMap,ArgMap,${WrapExprs[$LastPos]},Outputs$LastPos,OutputsOut0)))),"
  echo "              L,OutputsIn,OutputsOut)"
 lineDelim="else "
done

cat << EOF
  else
    impure unsafe_perform_io(print(Pred)),
    error("unknown predicate").
EOF
