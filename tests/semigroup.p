cnf(assoc, axiom, '*'(X, '*'(Y, Z)) = '*'('*'(X, Y), Z)).
cnf(two_three, axiom, '*'(X, X) = '*'(X, '*'(X, X))).
cnf(twiddle, axiom, '*'('*'(X, X), Y) = '*'(Y, '*'(X, X))).
cnf(conjecture, axiom, '*'('*'(a, b), '*'(a, b)) != '*'('*'(a, a), '*'(b, b))).
