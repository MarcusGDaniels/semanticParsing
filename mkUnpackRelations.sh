#!/bin/bash

cat << EOF
:- module sentence_unpackRelation.
:- interface.
:- import_module mrs.
:- import_module multi_map.
:- import_module sentence_predicates.
:- import_module sentence_types.
:- import_module set.
:- import_module list.
:- import_module term.
:- import_module varset.

:- pred unpackRelation(multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                       multi_map(mrs_types,mrs_rel_handle),
                       set(mrs_rel_handle),
                       mrs_rel_handle,
                       preds,
		       set(string),set(string),
		       list(term(T)),list(term(T)), 
		       varset(T),varset(T)).
:- mode unpackRelation(in,in,in,in,in,in,out,in,out,in,out) is det.

:- implementation.
:- import_module require.
:- import_module solutions.
:- import_module calls.
:- import_module string.
:- import_module io.
:- import_module unsafe.

:- pred expandHandle(mrs_rel_handle,
                     multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                     multi_map(mrs_types, mrs_rel_handle),
                     set(mrs_rel_handle),
                     set(string),set(string),
                     list(term(T)),list(term(T)),
		     varset(T),varset(T)).
:- mode expandHandle(in,in,in,in,in,out,in,out,in,out).
:- pragma promise_pure(expandHandle/10).
expandHandle(RelHandle0,RelMap,ArgMap,ExcludeRelSet,SignaturesIn0,SignaturesOut0,CallsIn0,CallsOut0,VarSetIn0,VarSetOut0) :-
   % impure unsafe_perform_io(print("expandHandle:")),
   % impure unsafe_perform_io(print(RelHandle0)),
   % impure unsafe_perform_io(print("\n")),
   (if multi_map.contains(RelMap,RelHandle0) then
     multi_map.lookup(RelMap,RelHandle0,Rels0),
     list.foldl3(pred({RelHandle0Ref,_,_,Pred0}::in,SignaturesIn1::in,SignaturesOut1::out,CallsIn1::in,CallsOut1::out,VarSetIn1::in,VarSetOut1::out) is det :- 
		  unpackRelation(RelMap,ArgMap,ExcludeRelSet,RelHandle0Ref,Pred0,SignaturesIn1,SignaturesOut1,CallsIn1,CallsOut1,VarSetIn1,VarSetOut1),
		Rels0,SignaturesIn0,SignaturesOut0,CallsIn0,CallsOut0,VarSetIn0,VarSetOut0)
    else
      SignaturesOut0 = SignaturesIn0,
      CallsOut0 = CallsIn0,
      VarSetOut0 = VarSetIn0
      ).

:- pred expandArg(mrs_rel_handle,
                  multi_map(mrs_rel_handle,{mrs_rel_handle,string,string,preds}),
                  multi_map(mrs_types, mrs_rel_handle),
		  set(mrs_rel_handle),
                  mrs_types,
                  set(string), set(string),
                  list(term(T)),list(term(T)),
                  varset(T),varset(T)).
:- mode expandArg(in,in,in,in,in,in,out,in,out,in,out).
:- pragma promise_pure(expandArg/11).
expandArg(RelHandle,RelMap,ArgMap,ExcludeRelSet,AT,SignaturesIn,SignaturesOut,CallsIn,CallsOut,VarSetIn,VarSetOut) :-
  multi_map.lookup(ArgMap,AT,Rels),
  % impure unsafe_perform_io(print("expandArg:")),
  % impure unsafe_perform_io(print({AT,Rels})),
  % impure unsafe_perform_io(print("\n")),
  list.foldl3(pred(RelHandle0::in,SignaturesIn0::in,SignaturesOut0::out,CallsIn0::in,CallsOut0::out,VarSetIn0::in,VarSetOut0::out) is det :- 
    (if set.member(RelHandle0,ExcludeRelSet) then
      SignaturesOut0 = SignaturesIn0,
      CallsOut0 = CallsIn0,
      VarSetOut0 = VarSetIn0
    else
      expandHandle(RelHandle0,RelMap,ArgMap,ExcludeRelSet,SignaturesIn0,SignaturesOut0,CallsIn0,CallsOut0,VarSetIn0,VarSetOut0)),
    Rels,SignaturesIn,SignaturesOut,CallsIn,CallsOut,VarSetIn,VarSetOut).

:- pragma promise_pure(unpackRelation/11).
unpackRelation(RelMap,ArgMap,ExcludeRelSet,RelHandle,Pred,SignaturesIn,SignaturesOut,CallsIn,CallsOut,VarSetIn,VarSetOut) :-
  Context = term.context_init,
  (
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
        VarName=$Var
	Rhs=$Var
        IndivPos=$((${IndivPos} + 1))
        WrapExpr="wrap_indiv(${Var})"
        ;;
      mrs_inst)
        Var=Inst${InstPos}
        VarName=$Var
	Rhs=$Var
        InstPos=$((${InstPos} + 1))
        WrapExpr="wrap_inst(${Var})"
        ;;
      mrs_event)
        Var=Event${EventPos}
        VarName=$Var
	Rhs=$Var
        EventPos=$((${EventPos} + 1))
        WrapExpr="wrap_event(${Var})"
        ;;
      mrs_rel_handle)
	Var="mrs_rel_handle(RelHandle${RelHandlePos})"
        VarName=RelHandle${RelHandlePos}
        Rhs="mrs_rel_handle(RelHandle${RelHandlePos})"
        RelHandlePos=$((${RelHandlePos} + 1))
        WrapExpr="wrap_rel_handle(${Var})"
        ;;
      mrs_rstr_handle)
	Var="mrs_rstr_handle(RstrHandle${RstrHandlePos})"
        VarName=RstrHandle${RstrHandlePos}
	Types[${ArgPos}]=mrs_rel_handle
	Rhs="mrs_rel_handle(RstrHandle${RstrHandlePos})"
        RstrHandlePos=$((${RstrHandlePos} + 1))
        WrapExpr="wrap_rstr_handle(${Var})"
        ;;
      mrs_body_handle)
	Var="mrs_body_handle(BodyHandle${BodyHandlePos})"
        VarName=BodyHandle${BodyHandlePos}
	Types[${ArgPos}]=mrs_rel_handle
	Rhs="mrs_rel_handle(BodyHandle${BodyHandlePos})"
        BodyHandlePos=$((${BodyHandlePos} + 1))
        WrapExpr="wrap_body_handle(${Var})"
        ;;
      mrs_carg)
        Var=Carg${CargPos}
	VarName=$Var
	Rhs=$Var
        CargPos=$((${CargPos} + 1))
        WrapExpr="wrap_carg(${Var})"
        ;;
      mrs_unknown)
        Var=Unk${UnknownPos}
	VarName=$Var
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
     VarNames[${ArgPos}]=$VarName
     WrapExprs[${ArgPos}]=$WrapExpr
     delim=","
     shift
     ArgPos=$((${ArgPos} + 1))
  done
  ArgCount=${ArgPos}
  echo "    solutions(pred({${Args}}::out) is nondet :- ${pred}(RelHandle,${Args}), L),"
  echo "    list.foldl3(pred({${Args}}::in,SignaturesIn0::in,SignaturesOut0::out,CallsIn0::in,CallsOut0::out,VarSetIn0::in,VarSetOut0::out) is det :-"
  echo "               (Cmd = string.append_list([\"${pred}(\","
  for ArgPos in `seq 0 $((${ArgCount} - 2))`; do
      echo "                  to_string(${ArgAry[${ArgPos}]}),\",\","
  done      
  echo "                  to_string(${ArgAry[$((${ArgCount}-1))]}), \")\"]),"
  echo "                (if set.member(Cmd,SignaturesIn0) then"
  echo "                   SignaturesOut0 = SignaturesIn0,"
  echo "                   CallsOut0 = CallsIn0,"
  echo "                   VarSetOut0 = VarSetIn0"
  echo "                 else"
  echo "                   (set.insert(Cmd,SignaturesIn0,Signatures0),"
  echo "                    Args0 = [],"
  LastPos=$(($ArgCount - 1))
  echo "                    varset.new_named_var(\"Ret\",RetVar,VarSetIn0,VarSet0),"
  for ArgPos in `seq 0 $LastPos`; do
    if test $ArgPos = 0; then
      svarIn=Signatures0
      vvarIn=VarSet0
      if test $ArgPos = $LastPos; then
        svarOut=SignaturesOut0
        vvarOut=VarSetOut0
      else
        svarOut=Signatures1
        vvarOut=VarSet1
      fi
    elif test $ArgPos = $LastPos; then
      svarIn=Signatures$LastPos
      svarOut=SignaturesOut0
      vvarIn=VarSet$LastPos
      vvarOut=VarSetOut0
      delim=""
    else
      svarIn=Signatures${ArgPos}
      svarOut=Signatures$((${ArgPos} + 1))
      vvarIn=VarSet${ArgPos}
      vvarOut=VarSet$((${ArgPos} + 1))
      delim=","
    fi         
    avarIn=Args${ArgPos}
    avarOut=Args$((${ArgPos} + 1))
    if test ${Types[$ArgPos]} = mrs_rel_handle; then
      echo "                    ((if multi_map.contains(RelMap,${Vars[$ArgPos]}) then"
      echo "                        TL$ArgPos = multi_map.lookup(RelMap,${Vars[$ArgPos]}),"
      echo "                        RL$ArgPos = list.map(func({RelHandleA,_,_,_}) = Ret :- Ret = RelHandleA,TL$ArgPos),"
      echo "                        list.length(RL$ArgPos,LenRL$ArgPos),"
      echo "                        (if LenRL$ArgPos = 1 then"
      echo "                          mrs_rel_handle(mrs_handle(VarNameX$ArgPos)) = det_head(RL$ArgPos),"
      echo "                          varset.new_named_var(VarNameX$ArgPos,Var$ArgPos,$vvarIn,VarSetTmp$ArgPos)"
      echo "                        else"
      echo "                          varset.new_named_var(string.capitalize_first(to_string(${VarNames[$ArgPos]})),Var$ArgPos,$vvarIn,VarSetTmp$ArgPos))"
      echo "                      else"
      echo "                        varset.new_named_var(to_string(${VarNames[$ArgPos]}),Var$ArgPos,$vvarIn,VarSetTmp$ArgPos),"
      echo "                        RL$ArgPos = [${Vars[$ArgPos]}]),"
      echo "                     list.foldl3(pred(RelHandleA::in,S0In::in,S0Out::out,C0In::in,C0Out::out,V0In::in,V0Out::out) is det :-"
      echo "                       expandArg(RelHandle,RelMap,ArgMap,ExcludeRelSet,wrap_rel_handle(RelHandleA),S0In,S0Out,C0In,C0Out,V0In,V0Out),"
      echo "                       RL$ArgPos,$svarIn,$svarOut,[],Arg${ArgPos},VarSetTmp$ArgPos,$vvarOut)"
      echo "                     ),"
    else
      echo "                    varset.new_named_var(to_string(${VarNames[$ArgPos]}),Var$ArgPos,$vvarIn,VarSetTmp$ArgPos),"
      echo "                    expandArg(RelHandle,RelMap,ArgMap,ExcludeRelSet,${WrapExprs[$ArgPos]},$svarIn,$svarOut,[],Arg$ArgPos,VarSetTmp$ArgPos,$vvarOut),"
    fi
    echo "                    list.append($avarIn,"
cat << EOF
                                (if length(Arg$ArgPos) = 0 then
                                  [term.variable(Var$ArgPos,Context)]
                                else
                                  [term.functor(atom("apply"),
                                    [term.functor(atom(":-"),
                                       [term.functor(atom("is"),
                                          [term.functor(atom("="),
                                             [term.functor(term.atom("func"), [], Context),
                                              term.variable(RetVar,Context)],
                                             Context),
                                           term.functor(term.atom("semidet"), [], Context)],
                                          Context),
  				      list.foldl(func(Statement,Acc) = NewAcc :- NewAcc = term.functor(term.atom(","),[Acc,Statement],Context),
                                                 Arg$ArgPos,
  						 term.functor(term.atom("="),[term.variable(RetVar,Context),term.variable(Var$ArgPos,Context)],Context))
				       ],Context)],Context)]),
                                 $avarOut),
EOF
  done
  echo "                    list.append(CallsIn0,[term.functor(term.atom(\"${pred}\"),$avarOut,Context)],CallsOut0)"
  echo "              ))),"
  echo "              L,SignaturesIn,SignaturesOut,CallsIn,CallsOut,VarSetIn,VarSetOut)"
  lineDelim="else "
done

cat << EOF
  else
    impure unsafe_perform_io(print(Pred)),
    error("unknown predicate")
  ).
EOF
