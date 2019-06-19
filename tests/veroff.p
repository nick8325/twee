cnf(majority, axiom,
    f(X,X,Y) = X).
cnf('2a', axiom,
    f(X,Y,Z) = f(Z,X,Y)).
cnf('2b', axiom,
    f(X,Y,Z) = f(X,Z,Y)).
cnf(associativity, axiom,
    f(f(X,W,Y),W,Z) = f(X,W,f(Y,W,Z))).

cnf(a123, axiom, f(a1,a2,a3) = f123).
cnf(a145, axiom, f(a1,a4,a5) = f145).
cnf(a245, axiom, f(a2,a4,a5) = f245).
cnf(a345, axiom, f(a3,a4,a5) = f345).
cnf(lhs, axiom, f(f123,a4,a5) = c1).
cnf(rhs, axiom, f(f145,f245,f345) = c2).
cnf(goal, axiom, c1 != c2).
