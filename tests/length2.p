cnf(app_assoc, axiom, '++'(Xs, '++'(Ys, Zs)) = '++'('++'(Xs, Ys), Zs)).
cnf(app_length, axiom, length('++'(Xs, Ys)) = length('++'(Ys, Xs))).
cnf(conjecture, axiom, length('++'('++'(c,a),b)) != length('++'(a,'++'(b,c)))).
