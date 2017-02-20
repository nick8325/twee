cnf(k_def, axiom, '@'('@'(k, X), Y) = X).
cnf(s_def, axiom, '@'('@'('@'(s, X), Y), Z) = '@'('@'(X, Z), '@'(Y, Z))).
cnf(conjecture, negated_conjecture, '@'(X, a(X)) != '@'(a(X), '@'(X, a(X)))).
