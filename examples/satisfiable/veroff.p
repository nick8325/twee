cnf(majority, axiom,
    f(X,X,Y) = X).
cnf('2a', axiom,
    f(X,Y,Z) = f(Z,X,Y)).
cnf('2b', axiom,
    f(X,Y,Z) = f(X,Z,Y)).
%cnf(associativity, axiom,
%    f(f(X,W,Y),W,Z) = f(X,W,f(Y,W,Z))).

cnf(dist_long, conjecture,
    f(f(x,y,z),u,w) = f(f(x,u,w),f(y,u,w),f(z,u,w))).
