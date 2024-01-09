:- module genMaster.

:- interface.
:- import_module io.
:- pred main(io::di,io::uo) is det.

:- implementation.
:- import_module sentences.
:- import_module sentence_accessors.
:- import_module set.
:- import_module int.
:- import_module list.
:- import_module mrs.
:- import_module multi_map.
:- import_module ranges.

:- func collectSetForSentence(mrs_psoa_post,set({string,string})) = set({string,string}).
:- mode collectSetForSentence(in,in) = out is det.
collectSetForSentence(PsoaPost,SetIn) = SetOut :-
  psoa_post(_,_,R) = PsoaPost,
  list.foldl(pred({_,C,D,_}::in,Sin::in,Sout::out) is det :- set.insert({C,D},Sin,Sout),multi_map.values(R),SetIn,SetOut).

:- pred printDecl(string,io,io).
:- mode printDecl(in,di,uo).
printDecl(Str,IoIn,IoOut) :-
  io.print(Str,IoIn,IoOut0), 
  io.nl(IoOut0,IoOut).

:- pred checkIntersection({string,string},mrs_psoa_post).
:- mode checkIntersection(in,in) is semidet.
checkIntersection(Pair,PsoaPost) :-
  SetActive = collectSetForSentence(PsoaPost,set.init),
  set.member(Pair,SetActive).

:- pred printDefn({string,string},io,io).
:- mode printDefn(in,di,uo).
printDefn(Pair,!IO) :-
  {C,D} = Pair,
  io.print(C,!IO),
  io.print(" :-",!IO),
  io.nl(!IO),
  io.print("  ( ",!IO),
  io.nl(!IO),
  Len = list.length(sentences.sentences),
  L = ranges.to_sorted_list(ranges.range(0,Len-1)),
  list.foldl2(pred(SentenceIndex::in,CountIn::in,CountOut::out,IoIn::di,IoOut::uo) is det :- 
    (PsoaPost = list.det_index0(sentences.sentences,SentenceIndex),
     (if checkIntersection(Pair,PsoaPost) then
       (if CountIn = 0 then
         io.print("     ",IoIn,IoOut0)
        else
         io.print("   ; ",IoIn,IoOut0)),
       io.print("sentence",IoOut0,IoOut1),
       io.print(SentenceIndex,IoOut1,IoOut2),
       io.print(".",IoOut2,IoOut3),
       io.print(C,IoOut3,IoOut4),
       io.nl(IoOut4,IoOut),
       CountOut = CountIn + 1
     else
       IoOut = IoIn,
       CountOut = CountIn)),L,0,TotalCount,!IO),
  io.print("  ).",!IO),
  io.nl(!IO).
 
:- pred printSentenceImport(int,io,io).
:- mode printSentenceImport(in,di,uo) is det.
printSentenceImport(SentenceIndex,!IO) :-
  io.print(":- import_module sentence",!IO),
  io.print(SentenceIndex,!IO),
  io.print(".",!IO),
  io.nl(!IO).

main(!IO) :-
  list.foldl(pred(PsoaPost::in,SetIn::in,SetOut::out) is det :- SetOut = collectSetForSentence(PsoaPost,SetIn),sentences.sentences,set.init,All),

  io.print(":- module calls.\n",!IO),
  io.print(":- interface.\n", !IO),
  io.print(":- import_module mrs.\n", !IO),
  set.foldl(pred({C,D}::in,IoIn::di,IoOut::uo) is det :- printDecl(D,IoIn,IoOut),All,!IO),
  io.print(":- implementation.\n", !IO),
  Len = list.length(sentences.sentences),
  L = ranges.to_sorted_list(ranges.range(0,Len-1)),
  list.foldl(printSentenceImport,L,!IO),
  set.foldl(pred(Pair::in,IoIn::di,IoOut::uo) is det :- printDefn(Pair,IoIn,IoOut),All,!IO).


