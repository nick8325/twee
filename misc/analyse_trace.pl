:- use_module(boo067_good, []).
:- use_module(boo067_bad, []).

ground(Pred, X) :-
	call(Pred, Y),
	numbervars(Y, 1, _),
	X=Y.

default(Pred, X) :-
    call(Pred, boo067_good, boo067_bad, X).

missing(X) :- default(missing, X).
missing(Good, Bad, X) :-
	ground(Good:lemma, X),
	\+ found(Bad, add(rule(_, X))).

variant(rule(N, X=Y), rule(N, X=Y)).
variant(rule(N, X=Y), rule(N, Y=X)).

found(Mod, Rule) :-
	variant(Rule, Rule1),
	Mod:step(add(Rule1)).

gone(Mod, rule(N, X)) :-
	ground(Mod:lemma, X),
	found(Mod, rule(N, X)),
	Mod:step(delete(N)).

reappeared(Mod, rule(N, X), M) :-
	ground(found(Mod), rule(N, X)),
	found(Mod, rule(M, X)),
	M > N.
