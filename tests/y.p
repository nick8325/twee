cnf(c_def, axiom, '@'('@'('@'(c, X), Y), Z) = '@'(X, '@'(Y, Z))).
cnf(f_def, axiom, '@'('@'('@'(f, X), Y), Z) = '@'('@'(X, Z), Y)).
cnf(w_def, axiom, '@'(w, X) = '@'(X, X)).
cnf(conjecture, negated_conjecture, '@'(X, a) != '@'(a, '@'(X, a))).
