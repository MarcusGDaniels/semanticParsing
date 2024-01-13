#!/bin/bash

cat << EOF
:- module sentence_collectArguments.
:- interface.
:- import_module mrs.
:- import_module multi_map.
:- import_module sentence_predicates.
:- import_module sentence_types.

:- pred collectArguments(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                         mrs_rel_handle,
			 preds,
                         multi_map(mrs_types, mrs_rel_handle),
			 multi_map(mrs_types, mrs_rel_handle)).
:- mode collectArguments(in,in,in,in,out) is det.

:- implementation.
:- import_module require.
:- import_module solutions.
:- import_module list.
:- import_module calls.
:- import_module io.
:- import_module unsafe.

:- pragma promise_pure(collectArguments/5).
collectArguments(RelMap,RelHandle0,Pred,ArgMapIn,ArgMapOut) :-
EOF

sed -n '/mrs/s/.*pred_\([a-z0-9_]*\)(pred(\(mrs_rel_handle,[^)]*\)))/\1\,\2/p' sentence_predicates.m | tr -d ' ' | tr -d . > _predicate_table

declare -a ArgAry
declare -a WrapExprs
declare -a Types

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
        Var=RelHandle${RelHandlePos}
	Rhs=$Var
        RelHandlePos=$((${RelHandlePos} + 1))
	WrapExpr="wrap_rel_handle(${Var})"
        ;;
      mrs_rstr_handle)
	Var="mrs_rstr_handle(RstrHandle${RstrHandlePos})"
	Rhs="mrs_rel_handle(RstrHandle${RstrHandlePos})"
        RstrHandlePos=$((${RstrHandlePos} + 1))
	WrapExpr="wrap_rel_handle(mrs_rel_handle(${Rhs}))"
	Types[${ArgPos}]=mrs_rel_handle
        ;;
      mrs_body_handle)
	Var="mrs_body_handle(BodyHandle${BodyHandlePos})"
	Rhs="mrs_rel_handle(BodyHandle${BodyHandlePos})"
        BodyHandlePos=$((${BodyHandlePos} + 1))
	WrapExpr="wrap_rel_handle(mrs_rel_handle(${Rhs}))"
	Types[${ArgPos}]=mrs_rel_handle
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
     WrapExprs[${ArgPos}]=${WrapExpr}
     Vars[${ArgPos}]=$Rhs
     delim=","
     shift
     ArgPos=$((${ArgPos} + 1))
  done
  echo "    solutions(pred({${Args}}::out) is nondet :- ${pred}(${Args}), L),"
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
      ArgMapIn=ArgMapIn
    else
      ArgMapIn=ArgMap$(($ArgPos - 1))
    fi
    if test $(($ArgPos + 1)) = $ArgCount; then
      ArgMapOut=ArgMapOut
    else
      ArgMapOut=ArgMap${ArgPos}
    fi
    if test ${Types[$ArgPos]} = mrs_rel_handle; then
      echo    "    list.foldl(pred({${Pattern}}::in,AIn::in,AOut::out) is det :- "
      echo    "      ((if multi_map.contains(RelMap,${Vars[$ArgPos]}) then"
      echo    "         TL${ArgPos} = multi_map.lookup(RelMap,${Vars[$ArgPos]}),"
      echo    "         RL${ArgPos} = list.map(func({RelHandleA,_,_,_}) = Ret :- Ret = RelHandleA,TL${ArgPos})"
      echo    "       else"
      echo    "         RL${ArgPos} = [${Vars[$ArgPos]}]),"
      echo    "       list.foldl(pred(RelHandleB::in,AIn0::in,AOut0::out) is det :- AOut0 = multi_map.add(AIn0,wrap_rel_handle(${Vars[$ArgPos]}),RelHandleB),RL${ArgPos},AIn,AOut)),"
      echo -n "     L,${ArgMapIn},${ArgMapOut})"
    else
      echo -n "    list.foldl(pred({${Pattern}}::in,AIn::in,AOut::out) is det :- AOut = multi_map.add(AIn,${WrapExprs[$ArgPos]},RelHandle0),L,${ArgMapIn},${ArgMapOut})"
    fi
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
