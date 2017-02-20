% Needs case split on X < c.
cnf(comm, axiom, '+'(X, Y) = '+'(Y, X)).
cnf(assoc, axiom, '+'(X, '+'(Y, Z)) = '+'('+'(X, Y), Z)).
cnf(idem, axiom, '+'(X, X) = X).
cnf(funny, axiom, '-'('+'('-'('+'(X, Y)), '-'('+'(X, '-'(Y))))) = X).
cnf(conjecture, negated_conjecture, '+'('-'('+'('-'(a), b)), '-'('+'('-'(a), '-'(b)))) != a).
