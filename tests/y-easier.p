cnf(a, axiom, app(app(k, X), Y) = X).
cnf(a, axiom, app(app(app(s, X), Y), Z) = app(app(X, Z), app(Y, Z))).
cnf(a, axiom, app(app(app(b, X), Y), Z) = app(X, app(Y, Z))).
cnf(a, axiom, app(m, X) = app(X, X)).
cnf(a, axiom, app(X, a(X)) != app(a(X), app(X, a(X)))).
