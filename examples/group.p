cnf(associativity, axiom,
    X + (Y + Z) = (X + Y) + Z).
cnf(plus_zero, axiom,
    '0' + X = X).
cnf(plus_zero, axiom,
    X + '0' = X).
cnf(minus_left, axiom,
    (-X) + X = '0').
cnf(minus_right, axiom,
    X + (-X) = '0').
cnf(assumption, assumption,
    a + b = a).
cnf(goal, conjecture,
    b = '0').
