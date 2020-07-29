cnf('x\\(y\\x)=x', axiom,
    X \ (Y \ X) = X).
cnf('x\\(x\\y)=y\\(y\\x)', axiom,
    X \ (X \ Y) = Y \ (Y \ X)).
cnf('(x\\y)\\z=(x\\z)\\(y\\z)', axiom,
    (X \ Y) \ Z = (X \ Z) \ (Y \ Z)).
cnf(conjecture, conjecture,
    (a \ c) \ b = (a \ b) \ c).
