% Needs case split on X < c.
cnf(a, axiom, '+'(X, Y) = '+'(Y, X)).
cnf(a, axiom, '+'(X, '+'(Y, Z)) = '+'('+'(X, Y), Z)).
cnf(a, axiom, '+'(X, X) = X).
cnf(a, axiom, '-'('+'('-'('+'(X, Y)), '-'('+'(X, '-'(Y))))) = X).
cnf(a, axiom, '+'('-'('+'('-'(a), b)), '-'('+'('-'(a), '-'(b)))) != a).
