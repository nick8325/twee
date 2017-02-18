cnf(plus_comm, axiom, '+'(X, Y) = '+'(Y, X)).
cnf(plus_assoc, axiom, '+'(X, '+'(Y, Z)) = '+'('+'(X, Y), Z)).
cnf(times_comm, axiom, '*'(X, Y) = '*'(Y, X)).
cnf(times_assoc, axiom, '*'(X, '*'(Y, Z)) = '*'('*'(X, Y), Z)).
cnf(plus_zero, axiom, '+'(X, '0') = X).
cnf(times_zero, axiom, '*'(X, '0') = '0').
cnf(times_one, axiom, '*'(X, '1') = X).
cnf(distrib, axiom, '*'(X, '+'(Y, Z)) = '+'('*'(X, Y), '*'(X, Z))).
