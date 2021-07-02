cnf(ifeq_axiom, axiom, ifeq(A, A, B, C)=B).
cnf(k_def, axiom, '@'('@'(k, X), Y)=X).
cnf(s_def, axiom, '@'('@'('@'(s, X), Y), Z)='@'('@'(X, Z), '@'(Y, Z))).
cnf(conjecture, negated_conjecture, ifeq('@'(Y, f(Y)), '@'(f(Y), '@'(Y, f(Y))), a, b)=b).
cnf(goal, negated_conjecture, a!=b).
