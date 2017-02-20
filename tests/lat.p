cnf(idempotence_of_meet, axiom, meet(X, X)=X).
cnf(idempotence_of_join, axiom, join(X, X)=X).
cnf(absorption1, axiom, meet(X, join(X, Y))=X).
cnf(absorption2, axiom, join(X, meet(X, Y))=X).
cnf(commutativity_of_meet, axiom, meet(X, Y)=meet(Y, X)).
cnf(commutativity_of_join, axiom, join(X, Y)=join(Y, X)).
cnf(associativity_of_meet, axiom,
    meet(meet(X, Y), Z)=meet(X, meet(Y, Z))).
cnf(associativity_of_join, axiom,
    join(join(X, Y), Z)=join(X, join(Y, Z))).
cnf(equation_H34, axiom,
    meet(X, join(Y, meet(Z, U)))=meet(X,
                                      join(Y, meet(Z, join(Y, meet(U, join(Y, Z))))))).
cnf(prove_H28, negated_conjecture,
    meet(a, join(b, meet(a, meet(c, d))))!=meet(a,
                                                join(b, meet(c, meet(d, join(a, meet(b, d))))))).
