cnf(a, axiom, '+'(X, Y) = '+'(Y, X)).
cnf(a, axiom, '+'(X, '+'(Y, Z)) = '+'('+'(X, Y), Z)).
cnf(a, axiom, '+'('0', X) = X).
cnf(a, axiom, '+'(X, '-'(X)) = '0').
