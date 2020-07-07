% Entropic groupoid, taken from unfailing completion paper
cnf(a, axiom, '*'('*'(X,Y),'*'(Z,W)) = '*'('*'(X,Z),'*'(Y,W))).
cnf(a, axiom, '*'('*'(X,Y),X) = X).
cnf(a, axiom, a != b).
