% http://www.dcs.bbk.ac.uk/~szabolcs/rellat-jlamp-second-submission-2.pdf
% appendix b. theorem 3.4, clause 8.
cnf(a, axiom, '^'(X, Y) = '^'(Y, X)).
cnf(a, axiom, '^'(X, '^'(Y, Z)) = '^'(Y, '^'(X, Z))).
cnf(a, axiom, '^'('^'(X, Y), Z) = '^'(X, '^'(Y, Z))).
cnf(a, axiom, v(X, Y) = v(Y, X)).
cnf(a, axiom, v(X, v(Y, Z)) = v(Y, v(X, Z))).
cnf(a, axiom, v(v(X, Y), Z) = v(X, v(Y, Z))).
cnf(a, axiom, v(X, '^'(X, Y)) = X).
cnf(a, axiom, '^'(X, v(X, Y)) = X).
cnf(a, axiom, upme(X,Y,Z) = '^'(X, v(Y, Z))).
cnf(a, axiom, lome(X,Y,Z) = v('^'(X, Y), '^'(X, Z))).
cnf(a, axiom, upjo(X,Y,Z) = '^'(v(X, Y), v(X, Z))).
cnf(a, axiom, lojo(X,Y,Z) = v(X, '^'(Y, Z))).
cnf(a, axiom, v(upme('^'(a, X1),Y1,Z1), '^'(Y1, Z1)) = '^'(v('^'('^'(a, X1), Y1), Z1), v('^'('^'(a, X1), Z1), Y1))).
cnf(a, axiom, upme(X,Y,Z) = v(upme(X,Y,'^'(a, Z)), upme(X,Z,'^'(a, Y)))).
cnf(c1, axiom, c1 = upme(a,x2,y2)).
cnf(c2, axiom, c2 = upme(a,x2,z2)).
cnf(c3, axiom, c3 = upme(x2,y2,z2)).
cnf(c4, axiom, c4 = lome(x2,y2,z2)).
fof(a, conjecture, c1 = c2 => c3 = c4).
%fof(a, conjecture, (upme(a,x2,y2) = upme(a,x2,z2) => upme(x2,y2,z2) = lome(x2,y2,z2))).
