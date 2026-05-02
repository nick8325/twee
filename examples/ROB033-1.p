cnf(commutativity_of_add, axiom, add(X, Y)=add(Y, X)).
cnf(associativity_of_add, axiom,
    add(add(X, Y), Z)=add(X, add(Y, Z))).
cnf(robbins_axiom, axiom,
    negate(add(negate(add(X, Y)), negate(add(X, negate(Y)))))=X).
cnf(sos04, axiom, g(A)=negate(add(A, negate(A)))).
cnf(sos05, axiom, h(A)=add(A, add(A, add(A, g(A))))).
cnf(goals, negated_conjecture,
    add(negate(add(x0, negate(x1))),
        negate(add(negate(x0), negate(x1))))!=x1).
