% Obviously inconsistent because w X Y = X X Y = X.
% Interesting thing is the final rules:
% w @ X0 -> X0 @ X0 (unoriented)
% X0 @ X0 -> w @ X0 (unoriented)
% X0 @ X1 -> X0 @ ? (weak on [X1])
% X0 @ X1 -> w @ X0 (unoriented)
% We should maybe use X0 @ X1 -> X0 @ ? to simplify the
% other rules (many of which would still be oriented the same)
cnf(c_def, axiom, '@'('@'('@'(c, X), Y), Z) = '@'(X, '@'(Y, Z))).
cnf(f_def, axiom, '@'('@'('@'(f, X), Y), Z) = '@'('@'(X, Z), Y)).
cnf(w_def, axiom, '@'(w, X) = '@'(X, X)).
cnf(w_def_oops, axiom, '@'('@'(w, X), Y) = X).
cnf(conjecture, axiom, '@'(X, a) != '@'(a, '@'(X, a))).
