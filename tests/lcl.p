cnf(wajsberg_1, axiom, implies(truth, X)=X).
cnf(wajsberg_3, axiom,
    implies(implies(X, Y), Y)=implies(implies(Y, X), X)).
cnf(wajsberg_4, axiom,
    implies(implies(not(X), not(Y)), implies(Y, X))=truth).
cnf(lemma_antecedent, axiom, implies(X, Y)=implies(Y, X)).
cnf(prove_wajsberg_lemma, axiom, x!=y).
