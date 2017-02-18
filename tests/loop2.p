cnf(mult_ld, axiom, mult(X, ld(X, Y)) = Y).
cnf(ld_mult, axiom, ld(X, mult(X, Y)) = Y).
cnf(mult_rd, axiom, mult(rd(X, Y), Y) = X).
cnf(rd_mult, axiom, rd(mult(X, Y), Y) = X).
cnf(moufang, axiom, mult(X, mult(Y, mult(X, Z))) = mult(mult(mult(X, Y), X), Z)).
cnf(conjecture, axiom, mult(a,rd(b,b)) != a).
