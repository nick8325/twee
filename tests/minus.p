cnf(plus_zero, axiom,
	'+'('0', X) = X).
cnf(plus_zero, axiom,
	'+'(X, '0') = X).
cnf(minus_minus, axiom,
	'-'('-'(X)) = X).
cnf(minus_plus, axiom,
	'-'('+'(X, Y)) = '+'('-'(X), '-'(Y))).

cnf(goal, conjecture,
    '-'('0') = '0').
	%% ?[Y]: d(Y) = '+'(x, x)).
