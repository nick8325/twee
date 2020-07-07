cnf(comm, axiom, '+'(X, Y) = '+'(Y, X)).
cnf(assoc, axiom, '+'(X, '+'(Y, Z)) = '+'('+'(X, Y), Z)).
cnf(zero, axiom, '+'(X, '0') = X).
cnf(idem, axiom, '+'(X, X) = X).
cnf(a, axiom, a != b).
