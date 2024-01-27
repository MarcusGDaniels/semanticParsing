#!/bin/bash

cat << EOF
:- module sentence_collectArgRefs.
:- interface.
:- import_module mrs.
:- import_module multi_map.
:- import_module sentence_predicates.
:- import_module sentence_types.

:- pred collectArgRefs(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                       mrs_rel_handle,
		       preds,
		       multi_map(mrs_types,mrs_rel_handle),
                       multi_map(mrs_types,mrs_rel_handle)).
:- mode collectArgRefs(in,in,in,in,out) is det.

:- implementation.
:- import_module require.
:- import_module solutions.
:- import_module list.
:- import_module calls.
:- import_module io.
:- import_module unsafe.

:- pragma promise_pure(collectArgRefs/5).
collectArgRefs(RelMap,RelHandleIn,Pred,ArgRefMapIn,ArgRefMapOut) :-
EOF

sed -n '/mrs/s/.*pred_\([a-z0-9_]*\)(pred(\(mrs_rel_handle,[^)]*\)))/\1\,\2/p' sentence_predicates.m | tr -d ' ' | tr -d . > _predicate_table

declare -a ArgAry
declare -a WrapExprs

for line in `cat _predicate_table`; do
  set -- `echo $line | tr , ' '`
  pred=$1
  shift
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
        Var=Event${InstPos}
        EventPos=$((${EventPos} + 1))
	WrapExpr="wrap_event(${Var})"
        ;;
      mrs_rel_handle)
        Var=RelHandle${RelHandlePos}
        RelHandlePos=$((${RelHandlePos} + 1))
	WrapExpr="wrap_rel_handle(${Var})"
        ;;
      mrs_rstr_handle)
	Var="mrs_rstr_handle(RstrHandle${RstrHandlePos})"
        RstrHandlePos=$((${RstrHandlePos} + 1))
	WrapExpr="wrap_rstr_handle(${Var})"
        ;;
      mrs_body_handle)
	Var="mrs_body_handle(BodyHandle${BodyHandlePos})"
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
	echo "unknown type $1" 1>&2 
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
  echo "    solutions(pred({${Args}}::out) is nondet :- (${pred}(${Args}), RelHandle0 = RelHandleIn), L),"
  ArgCount=${ArgPos}
  ArgPos=0
  while test $ArgPos -lt $ArgCount; do
    ArgSubPos=0
    Pattern=''
    delim=''
    while test $ArgSubPos -lt $ArgCount; do
      if test $ArgSubPos = $ArgPos; then
         Pattern="${Pattern}${delim}${ArgAry[$ArgPos]}"
      else
         Pattern="${Pattern}${delim}_"
      fi
      ArgSubPos=$(($ArgSubPos + 1))
      delim=","
    done
    if test $ArgPos = 0; then
      ArgRefMapIn=ArgRefMapIn
    else
      ArgRefMapIn=ArgRefMap$(($ArgPos - 1))
    fi
    if test $(($ArgPos + 1)) = $ArgCount; then
      ArgRefMapOut=ArgRefMapOut
    else
      ArgRefMapOut=ArgRefMap${ArgPos}
    fi
    echo -n "    list.foldl(pred({${Pattern}}::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,${WrapExprs[$ArgPos]},RelHandleIn),L,${ArgRefMapIn},${ArgRefMapOut})"
    ArgPos=$(($ArgPos + 1))
    if test $ArgPos -lt $ArgCount; then
      echo ,
    else
      echo
    fi
  done
  lineDelim="else "
done

cat << EOF
  else
    impure unsafe_perform_io(print(Pred)),
    error("unknown predicate").
EOF
