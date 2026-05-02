cnf(app_assoc, axiom, '++'(Xs, '++'(Ys, Zs)) = '++'('++'(Xs, Ys), Zs)).
cnf(length_app, axiom, length('++'(Xs, Ys)) = length('++'(Ys, Xs))).
cnf(a, axiom, a != b).
