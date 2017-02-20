cnf(rev_rev, axiom, rev(rev(X)) = X).
cnf(app_assoc, axiom, '++'(X,'++'(Y,Z)) = '++'('++'(X,Y),Z)).
cnf(rev_app, axiom, '++'(rev(X),rev(Y)) = rev('++'(Y,X))).
cnf(conjecture, negated_conjecture, '++'(a,rev(b)) != rev('++'(b, rev(a)))).
