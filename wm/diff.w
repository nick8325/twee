NAME diff
MODE proof
SORTS ANY
SIGNATURE
diff: ANY ANY -> ANY
a: -> ANY
b: -> ANY
c: -> ANY
ORDERING
KBO
a=1, b=1, c=1, diff=1
diff > c > b > a
VARIABLES
X, Y, Z: ANY
EQUATIONS
diff(X, diff(Y, X)) = X
diff(X, diff(X, Y)) = diff(Y, diff(Y, X))
diff(diff(X, Y), Z) = diff(diff(X, Z), diff(Y, Z))
CONCLUSION
diff(diff(a,c),b) = diff(diff(a,b),c)
