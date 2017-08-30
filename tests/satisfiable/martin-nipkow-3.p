cnf(a, axiom, '*'('*'(X,X),Y) = Y).
cnf(a, axiom, '*'('*'(X,Y),Z) = '*'('*'(Y,Z),X)).
% In the final rules we get
%    (X * Y) * Z -> Y * (Z * X)
% where Martin and Nipkow report associativity:
%    (X * Y) * Z -> X * (Y * Z)
% Why is that?
