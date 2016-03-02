% Obviously inconsistent because w X Y = X X Y = X.
% Interesting thing is the final rules:
% w '@' X'0' '->' X'0' '@' X'0' (unoriented)
% X'0' '@' X'0' '->' w '@' X'0' (unoriented)
% X'0' '@' X'1' '->' X'0' '@' ? (weak on [X'1'])
% X'0' '@' X'1' '->' w '@' X'0' (unoriented)
% We should maybe use X'0' '@' X'1' '->' X'0' '@' ? to simplify the
% other rules (many of which would still be oriented the same)
cnf(a, axiom, '@'('@'('@'(c, X), Y), Z) = '@'(X, '@'(Y, Z))).
cnf(a, axiom, '@'('@'('@'(f, X), Y), Z) = '@'('@'(X, Z), Y)).
cnf(a, axiom, '@'(w, X) = '@'(X, X)).
cnf(a, axiom, '@'('@'(w, X), Y) = X).
cnf(a, axiom, '@'(X, a) != '@'(a, '@'(X, a))).
