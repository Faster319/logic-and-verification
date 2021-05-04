/* member(Item, List) :- Item occurs in List. */
member(X, [X | _]).
member(X, [_ | T]) :- member(X, T).

/* remove(Item, List, Newlist) :- Newlist is the result of removing all occurrences of Item from List. */
remove(_, [], []).
remove(X, [X | T], NewT) :- remove(X, T, NewT).
remove(X, [H | T], [H | NewT]) :- remove(X, T, NewT).

/* conjuctive(X) :- X is an alpha formula. */
conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).
conjunctive(neg(_ equiv _)).
conjunctive(_ notequiv _).


/* disjunctive(X) :- X is an beta formula. */
disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).
disjunctive(_ equiv _).
disjunctive(neg(_ notequiv _)).

/* unary(X) :- X is a double negation or a negated constant. */
unary(neg neg _).
unary(neg true).
unary(neg false).

/* components(X, Y, Z) :- Y and Z are the components of formula X, as defined in the alpha and beta table */
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
components(X revimp Y, X, neg(Y)).
components(neg(X revimp Y), neg(X), Y).
components(X notrevimp Y, neg(X), Y).
components(neg(X notrevimp Y), X, neg(Y)).
components(neg(X equiv Y), neg(X and Y), neg(neg(X) and neg(Y))).
components(X equiv Y, X and Y, neg(X) and neg(Y)).
components(X notequiv Y, neg(X) or neg(Y), X or Y).
components(neg(X notequiv Y), neg(neg(X) or neg(Y)), neg(X or Y)).

/* component(X, Y) :- Y is the component of the unary formula X. */
component(neg neg X, X).
component(neg ture, false).
component(neg false, true).

/* singlestep(Old, New) :- New is the result of applying a single step of the expansion to Old,
genralised conjunctions of generalised disjunctions. */
singlestep([Disjunction | Rest], New) :- member(Formula, Disjunction),
                                         unary(Formula),
                                         component(Formula, Newformula),
                                         remove(Formula, Disjunction, Temp),
                                         Newdisjunction = [Newformula | Temp],
                                         New = [Newdisjunction | Rest].

singlestep([Disjunction | Rest], New) :- member(Alpha, Disjunction),
                                         conjunctive(Alpha),
                                         components(Alpha, Alpha1, Alpha2),
                                         remove(Alpha, Disjunction, Temp),
                                         Newdis1 = [Alpha1 | Temp],
                                         Newdis2 = [Alpha2 | Temp],
                                         New = [Newdis1, Newdis2 | Rest].

singlestep([Disjunction | Rest], New) :- member(Beta, Disjunction),
                                         disjunctive(Beta),
                                         components(Beta, Beta1, Beta2),
                                         remove(Beta, Disjunction, Temp),
                                         Newdis = [Beta1, Beta2 | Temp],
                                         New = [Newdis | Rest].

/* expand(Old, New) :- New is the result of applying singlestep as many times as possible, starting with Old. */
expand(Conj, Newconj) :- singlestep(Conj, Temp),
                         expand(Temp, Newconj).

expand(Conj, Conj).

/* resolutionstep(Old, New) :- NEED TO CHANGE */
resolutionstep([Disjunction | Rest], New) :- member(X, Disjunction),
                                             remove(X, Disjunction, Temp),
                                             New = [Temp | Rest].

resolutionstep([Disjunction | Rest], New) :- member(neg X, Disjunction),
                                             remove(neg X, Disjunction, Temp),
                                             New = [Temp | Rest].

/* resolution(Old, New) :- */
resolution(Conj, Newconj) :- resolutionstep(Conj, Temp),
                             resolution(Temp, Newconj).

resolution(Conj, Conj).

/* closed(X) :-  */
closed([[] | _]).
closed([_ | Rest]) :- closed([Rest | _]).
%closed([Branch | Rest]) :- member(false, Branch),
%                           closed(Rest).
%
%closed([Branch | Rest]) :- member(X, Branch),
%                           member(neg X, Branch),
%                           closed(Rest).
%
%closed([]).

/* if_then_else(X, Y, Z) :- either X and Y, or not X and Z. */
if_then_else(X, Y, _) :- X, !, Y.

if_then_else(_, _, Z) :- Z.


/* clauseform(X, Z) :- Z is the conjuctive normal form of the formula X */
test(X, Z) :- expand([[neg X]], Y),
              resolution(Y, Z),
              if_then_else(closed(Z), yes, no).

yes :- write('YES'), nl.
no :- write('NO'), nl.