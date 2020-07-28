cnf(mult_ld, axiom, '*'(X, '\\'(X, Y)) = Y).
cnf(ld_mult, axiom, '\\'(X, '*'(X, Y)) = Y).
cnf(mult_rd, axiom, '*'('/'(X, Y), Y) = X).
cnf(rd_mult, axiom, '/'('*'(X, Y), Y) = X).
cnf(moufang, axiom, '*'(X, '*'(Y, '*'(X, Z))) = '*'('*'('*'(X, Y), X), Z)).
cnf(conjecture, negated_conjecture, '\\'(a,a) != '/'(a,a)).
