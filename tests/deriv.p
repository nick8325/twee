% Axioms about arithmetic.

cnf('commutativity of +', axiom,
	'+'(X, Y) = '+'(Y, X)).
cnf('associativity of +', axiom,
	'+'(X, '+'(Y, Z)) = '+'('+'(X, Y), Z)).
cnf('commutativity of *', axiom,
	'*'(X, Y) = '*'(Y, X)).
cnf('associativity of *', axiom,
	'*'(X, '*'(Y, Z)) = '*'('*'(X, Y), Z)).
cnf('plus 0', axiom,
	'+'('0', X) = X).
cnf('times 0', axiom,
	'*'('0', X) = '0').
cnf('times 1', axiom,
	'*'('1', X) = X).
cnf('distributivity', axiom,
	'*'(X, '+'(Y, Z)) = '+'('*'(X, Y), '*'(X, Z))).
cnf('minus', axiom,
    '+'(X, '-'(X)) = '0').

cnf('derivative of 0', axiom,
	d('0') = '0').
cnf('derivative of 1', axiom,
	d('1') = '0').
cnf('derivative of x', axiom,
	d(x) = '1').
cnf('derivative of +', axiom,
	d('+'(T,U)) = '+'(d(T), d(U))).
cnf('derivative of *', axiom,
	d('*'(T, U)) = '+'('*'(T, d(U)), '*'(U, d(T)))).
cnf('derivative of sin', axiom,
    d(sin(T)) = '*'(cos(T), d(T))).
cnf('derivative of cos', axiom,
    d(cos(T)) = '-'('*'(sin(T), d(T)))).

fof(goal, conjecture,
	?[T]: d(T) = '*'(x, cos(x))).
    
