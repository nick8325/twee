cnf(comm, axiom, '+'(X, Y) = '+'(Y, X)).
cnf(assoc, axiom, '+'(X, '+'(Y, Z)) = '+'('+'(X, Y), Z)).
cnf(funny, axiom, '-'('+'('-'('+'(X, Y)), '-'('+'(X, '-'(Y))))) = X).
cnf(ma, axiom, '-'(a) = ma).
cnf(mma, axiom, '-'(ma) = mma).
cnf(conjecture, negated_conjecture, mma != a).
