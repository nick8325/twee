NAME loop
MODE proof
SORTS ANY
SIGNATURE
mult: ANY ANY -> ANY
ld: ANY ANY -> ANY
rd: ANY ANY -> ANY
a: -> ANY
b: -> ANY
ORDERING
KBO
a=1, b=1, mult=1, ld=0, rd=0
rd > ld > mult > b > a
VARIABLES
X, Y, Z: ANY
EQUATIONS
mult(X, ld(X, Y)) = Y
mult(rd(X, Y), Y) = X
ld(X, mult(X, Y)) = Y
rd(mult(X, Y), Y) = X
mult(X, mult(Y, mult(X, Z))) = mult(mult(mult(X, Y), X), Z)
CONCLUSION
mult(a, rd(b, b)) = a
