cnf('*-\\', axiom, '*'(X, '\\'(X, Y)) = Y).
cnf('\\-*', axiom, '\\'(X, '*'(X, Y)) = Y).
cnf('*-/', axiom, '*'('/'(X, Y), Y) = X).
cnf('/-*', axiom, '/'('*'(X, Y), Y) = X).
cnf(moufang, axiom, '*'(X, '*'(Y, '*'(X, Z))) = '*'('*'('*'(X, Y), X), Z)).
cnf(conjecture, negated_conjecture, '*'(a,'/'(b,b)) != a).
