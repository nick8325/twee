cnf(plus_comm, axiom,
    X + Y = Y + X).
cnf(plus_assoc, axiom,
    X + (Y + Z) = (X + Y) + Z).
cnf(times_comm, axiom,
    X * Y = Y * X).
cnf(times_assoc, axiom,
    X * (Y * Z) = (X * Y) * Z).
cnf(plus_zero, axiom,
    X + zero = X).
cnf(times_zero, axiom,
    X * zero = zero).
cnf(times_one, axiom,
    X * one = X).
cnf(distr, axiom,
    X * (Y + Z) = (X * Y) + (X * Z)).
cnf(distr, axiom,
    (X + Y) * Z = (X * Z) + (Y * Z)).
cnf(plus_s, axiom,
    s(X) + Y = s(X+Y)).
cnf(times_s, axiom,
    s(X)*Y = Y + (X*Y)).
cnf(sum_zero, axiom,
    sum(zero) = zero).
cnf(sum_s, axiom,
    sum(s(N)) = s(N) + sum(N)).
cnf(ih, axiom,
    sum(a) + sum(a) = a * s(a)).
cnf(conjecture, conjecture,
    sum(s(a)) + sum(s(a)) = s(a) * s(s(a))).
