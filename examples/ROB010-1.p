cnf(condition,hypothesis,
    ( negate(add(a,negate(b))) = c )).

cnf(prove_result,negated_conjecture,
    (  negate(add(c,negate(add(b,a)))) != a )).

cnf(commutativity_of_add,axiom,
    ( add(X,Y) = add(Y,X) )).

cnf(robbins_axiom,axiom,
    ( negate(add(negate(add(X,Y)),negate(add(X,negate(Y))))) = X )).
