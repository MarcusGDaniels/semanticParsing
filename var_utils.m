:- module var_utils.
:- interface.
:- import_module string.
:- import_module list.
:- import_module varset.
:- import_module term.
:- import_module map.
:- import_module mrs.

:- func collectVarNames(varset.varset(T)) = list(string).
:- func collectInstanceVarNames(varset.varset(T)) = list(string).
:- func collectGlobalVars(varset.varset(T),list(string)) = list(term.var(T)).
:- pred get_var_term(map(mrs_rel_handle,list(string)),varset(T),mrs_rel_handle,var(T),term.context,varset(T),varset(T),term(T)).
:- mode get_var_term(in,in,in,in,in,in,out,out) is det.

:- implementation.
:- import_module set.
:- import_module require.
:- import_module unsafe.
:- import_module io.

collectVarNames(VarSet) = VarNames :-
    VarNamesAll = list.map(func(VarTest) = Ret :- if varset.search_name(VarSet,VarTest,VarName) then Ret = VarName else error("no variable"),varset.vars(VarSet)),
    VarNames = set.to_sorted_list(set.from_list(VarNamesAll)).

collectInstanceVarNames(VarSet) = VarNames :-
    list.filter(pred(VarName::in) is semidet :- string.det_index(VarName,0) = 'X',collectVarNames(VarSet),VarNames).

collectGlobalVars(VarSet,VarNames) = GlobalVars :-
    GlobalVars = list.map(func(VarName) = Ret :-
                           if list.find_first_match(pred(VarTest::in) is semidet :- varset.search_name(VarSet,VarTest,VarName),
                                                    varset.vars(VarSet),
                                                    GlobalVar) then
                             Ret = GlobalVar
                           else
                             error("no value"),
                          VarNames).

:- pragma promise_pure(get_var_term/8).
get_var_term(VarMap,VarSet,RelHandle,Var,Context,VarSetLocalIn,VarSetLocalOut,Ret):-
  (if map.contains(VarMap,RelHandle) then
    mrs_rel_handle(mrs_handle(VarName)) = RelHandle,
    VarNames = map.lookup(VarMap,RelHandle),

    GlobalVars = collectGlobalVars(VarSet,VarNames),
    
    %impure unsafe_perform_io(io.print({RelHandle,VarNames})),
    %impure unsafe_perform_io(io.nl),
    list.foldl_corresponding(pred(Name::in,Var::in,VSLIn::in,VSLOut::out) is det :- 
                               (if varset.new_named_var(Name,Var,VSLIn,VSLNew) then
				 VSLOut = VSLNew
			        else	
				 VSLOut = VSLIn),
			        VarNames, GlobalVars, VarSetLocalIn, VarSetLocalOut),
    var_list_to_term_list(GlobalVars,VarTerms),
    Ret = term.functor(atom(VarName),VarTerms,Context)
  else
    VarSetLocalOut = VarSetLocalIn,
    Ret = term.variable(Var,Context)).
  
