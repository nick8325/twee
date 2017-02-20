fof(k_def, axiom, ![X, Y]: '@'('@'(k, X), Y) = X).
fof(s_def, axiom, ![X, Y, Z]: '@'('@'('@'(s, X), Y), Z) = '@'('@'(X, Z), '@'(Y, Z))).
fof(conjecture, conjecture, ?[Y]: ![F]: '@'(Y, F) = '@'(F, '@'(Y, F))).
