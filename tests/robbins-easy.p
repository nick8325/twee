cnf(comm, axiom, '+'(X, Y) = '+'(Y, X)).
cnf(assoc, axiom, '+'(X, '+'(Y, Z)) = '+'('+'(X, Y), Z)).
cnf(funny, axiom, '+'('-'('+'('-'(X), Y)), '-'('+'('-'(X), '-'(Y)))) = X).
cnf(conjecture, axiom, '-'('+'('-'('+'(a, b)), '-'('+'(a, '-'(b))))) != a).
