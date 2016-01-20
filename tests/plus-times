cnf(a, axiom, '+'(X, Y) = '+'(Y, X)).
cnf(a, axiom, '+'(X, '+'(Y, Z)) = '+'('+'(X, Y), Z)).
cnf(a, axiom, '*'(X, Y) = '*'(Y, X)).
cnf(a, axiom, '*'(X, '*'(Y, Z)) = '*'('*'(X, Y), Z)).
cnf(a, axiom, '+'(X, '0') = X).
cnf(a, axiom, '*'(X, '0') = '0').
cnf(a, axiom, '*'(X, '1') = X).
cnf(a, axiom, '*'(X, '+'(Y, Z)) = '+'('*'(X, Y), '*'(X, Z))).
