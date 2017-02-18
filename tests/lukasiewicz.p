cnf(imp_true, axiom, implies(true, X) = X).
cnf(imp_compose, axiom, implies(implies(X, Y), implies(implies(Y, Z), implies(X, Z))) = true).
cnf(imp_not, axiom, implies(implies(not(X), not(Y)), implies(Y, X)) = true).
cnf(imp_switch, axiom, implies(implies(X, Y), Y) = implies(implies(Y, X), X)).
cnf(or_def, axiom, or(X, Y) = implies(not(X), Y)).
cnf(conjecture, axiom, or(a,or(b,c)) != or(or(a,b),c)).
