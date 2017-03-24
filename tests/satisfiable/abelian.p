cnf(commutativity, axiom, '+'(X, Y) = '+'(Y, X)).
cnf(associativity, axiom, '+'(X, '+'(Y, Z)) = '+'('+'(X, Y), Z)).
cnf(identity, axiom, '+'('0', X) = X).
cnf(cancellation, axiom, '+'(X, '-'(X)) = '0').
