cnf(k_def, axiom, '@'('@'(k, X), Y) = X).
cnf(s_def, axiom, '@'('@'('@'(s, X), Y), Z) = '@'('@'(X, Z), '@'(Y, Z))).
cnf(conjecture, axiom, '@'(X, a(X)) != '@'(a(X), '@'(X, a(X)))).
