cnf('x\\(y\\x)=x', axiom,
    X \ (Y \ X) = X).
cnf('x\\(x\\y)=y\\(y\\x)', axiom,
    X \ (X \ Y) = Y \ (Y \ X)).
cnf('(x\\y)\\z=(x\\z)\\(y\\z)', axiom,
    (X \ Y) \ Z = (X \ Z) \ (Y \ Z)).

cnf(empty, axiom,
    X \ empty = X).

cnf(equals, conjecture,
    (X \ Y = empty & Y \ X = empty) => X = Y).

cnf(union, axiom,
    X \ union(Y, Z) = (X \ Y) \ Z).

cnf(union, conjecture,
    union(a,b) = union(b,a)).
cnf(union, conjecture,
    union(a,a) = a).
cnf(union, conjecture,
    union(a,union(b,c)) = union(union(a,b),c)).

cnf(intersection, axiom,
    intersection(X, Y) = X \ (X \ Y)).

cnf(intersection, conjecture,
    intersection(a,b) = intersection(b,a)).
cnf(intersection, conjecture,
    intersection(a,a) = a).
cnf(intersection, conjecture,
    intersection(a,intersection(b,c)) = intersection(intersection(a,b),c)).
cnf(intersection, conjecture,
    intersection(X, Y) = union(X,Y) \ union(X \ Y, Y \ X)).
