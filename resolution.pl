/*
1. YES
2. YES
3. YES
4. NO
5. YES
6. YES
7. YES
8. NO
9. NO
10. YES
*/

?-op(140, fy, neg).
?-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp, equiv, notequiv]).

/* remove(Item, List, Newlist) :- Newlist is the result of removing all occurrences of Item from List. */
remove(_, [], []) :- !.
remove(X, [X | T], NewT) :- remove(X, T, NewT), !.
remove(X, [H | T], [H | NewT]) :- remove(X, T, NewT).

/* append(List1, List2, NewList) :- NewList is the concatenation of List1 and List2. */
append([], X, X).
append([H | T], Z, [H | NewT]) :- append(T, Z, NewT).

/* notmember(Item, List) :- Checks if an item is not part of a list. Returns false if yes. */
notmember(X, [X|_]) :- !, fail.
notmember(X, [_|T]) :- !, notmember(X, T).
notmember(_, []).

/* conjuctive(X) :- X is an alpha formula. */
conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).
conjunctive(_ equiv _).
conjunctive(neg(_ equiv _)).
conjunctive(_ notequiv _).
conjunctive(neg(_ notequiv _)).

/* disjunctive(X) :- X is an beta formula. */
disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).

/* unary(X) :- X is a double negation or a negated constant. */
unary(neg neg _).
unary(neg true).
unary(neg false).

/* components(X, Y, Z) :- Y and Z are the components of formula X, as defined in the alpha and beta table, including equiv and notequiv. */
components(X and Y, X, Y).
components(neg(X and Y), neg(X), neg(Y)).
components(neg(X or Y), neg(X), neg(Y)).
components(X or Y, X, Y).
components(neg(X imp Y), X, neg(Y)).
components(X imp Y, neg(X), Y).
components(neg(X revimp Y), neg(X), Y).
components(X revimp Y, X, neg(Y)).
components(neg(X uparrow Y), X, Y).
components(X uparrow Y, neg(X), neg(Y)).
components(X downarrow Y, neg(X), neg(Y)).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg(Y)).
components(neg(X notimp Y), neg(X), Y).
components(X notrevimp Y, neg(X), Y).
components(neg(X notrevimp Y), X, neg(Y)).
components(X equiv Y, X imp Y, Y imp X).
components(neg(X equiv Y), X or Y, neg(X and Y)).
components(X notequiv Y, neg X or neg Y, X or Y).
components(neg(X notequiv Y), neg(X notimp Y), neg(Y notimp X)).

/* component(X, Y) :- Y is the component of the unary formula X. */
component(neg neg X, X).
component(neg true, false).
component(neg false, true).

/* singlestep(Old, New) :- New is the result of applying a single step of the expansion to Old,
genralised conjunctions of generalised disjunctions. */
singlestep([Disjunction | Rest], New) :- member(Formula, Disjunction),
                                         unary(Formula),
                                         component(Formula, NewFormula),
                                         remove(Formula, Disjunction, Temp),
                                         NewDisjunction = [NewFormula | Temp],
                                         New = [NewDisjunction | Rest].

singlestep([Disjunction | Rest], New) :- member(Beta, Disjunction),
                                         disjunctive(Beta),
                                         components(Beta, Beta1, Beta2),
                                         remove(Beta, Disjunction, Temp),
                                         NewDisjunction = [Beta1, Beta2 | Temp],
                                         New = [NewDisjunction | Rest].

singlestep([Disjunction | Rest], New) :- member(Alpha, Disjunction),
                                         conjunctive(Alpha),
                                         components(Alpha, Alpha1, Alpha2),
                                         remove(Alpha, Disjunction, Temp),
                                         NewDisjunction1 = [Alpha1 | Temp],
                                         NewDisjunction2 = [Alpha2 | Temp],
                                         New = [NewDisjunction1, NewDisjunction2 | Rest].


singlestep([Disjunction | Rest], [Disjunction | NewRest]) :- singlestep(Rest, NewRest).

/* expand(Old, New) :- New is the result of applying singlestep as many times as possible, starting with Old. */
expand(Conjunction, NewConjunction) :- singlestep(Conjunction, Temp),
                                       expand(Temp, NewConjunction).

expand(Conjunction, Conjunction).

/* resolve(Disjunction1, Disjunction2, NewResolved) :- If there is an X occurring in first disjunction and a neg X occurring
 in second disjunction, delete all occurrences of X in first disjunction and neg X in second disjunction. Combine both disjunctions
 and remove duplicates. */
resolve(Disjunction1, Disjunction2, SortedResolved) :- member(X, Disjunction1),
                                                       member(neg X, Disjunction2),
                                                       remove(X, Disjunction1, Temp1),
                                                       remove(neg X, Disjunction2, Temp2),
                                                       append(Temp1, Temp2, Resolved),
                                                       sort(Resolved, SortedResolved).

resolve(Disjunction1, Disjunction2, SortedResolved) :- member(neg X, Disjunction1),
                                                       member(X, Disjunction2),
                                                       remove(neg X, Disjunction1, Temp1),
                                                       remove(X, Disjunction2, Temp2),
                                                       append(Temp1, Temp2, Resolved),
                                                       sort(Resolved, SortedResolved).

/* resolutionstep(Conjunctions, New) :- Takes any 2 disjunctions in the list of conjunctions and calls resolve.
 After recieving the resolvent, check if it's not already member in the list of conjunctions and then add to list.*/
resolutionstep(Conjunctions, New) :- member(Disjunction1, Conjunctions),
                                     member(Disjunction2, Conjunctions),
                                     resolve(Disjunction1, Disjunction2, SortedResolved),
                                     notmember(SortedResolved, Conjunctions),
                                     New = [SortedResolved | Conjunctions].

/* resolution(Old, New) :- New is the result of applying resolutionstep as many times as possible, starting with Old. */
resolution(Conjunction, NewConjunction) :- resolutionstep(Conjunction, Temp), !,
                                           resolution(Temp, NewConjunction).

resolution(Conjunction, Conjunction).

/* clauseform(X, Y) :- Y is the clause form of formula X. */
clauseform(X, Y) :- expand([[X]], Y).

/* if_then_else(X, Y, Z) :- Either X and Y, or not X and Z. */
if_then_else(X, Y, _) :- X, !, Y.
if_then_else(_, _, Z) :- Z.

/* test(X) :- Creates a resolution proof for neg X, if it has a proposition proof, print out YES, print out NO otherwise. */
test(X) :- expand([[neg X]], Y),
           resolution(Y, Z),
           if_then_else(member([], Z), yes, no).

yes :- write('YES'), nl.
no :- write('NO'), nl.