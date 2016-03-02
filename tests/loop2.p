cnf(a, axiom, mult(X, ld(X, Y)) = Y).
cnf(a, axiom, ld(X, mult(X, Y)) = Y).
cnf(a, axiom, mult(rd(X, Y), Y) = X).
cnf(a, axiom, rd(mult(X, Y), Y) = X).
cnf(a, axiom, mult(X, mult(Y, mult(X, Z))) = mult(mult(mult(X, Y), X), Z)).
cnf(a, axiom, mult(a,rd(b,b)) != a).
