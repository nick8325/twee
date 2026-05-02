cnf(associativity, axiom,
    X * (Y * Z) = (X * Y) * Z).
cnf(plus_zero, axiom,
    X * e = X).
cnf(minus_right, axiom,
    X * inv(X) = e).
cnf(goal, conjecture,
    a = b).
