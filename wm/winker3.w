NAME diff
MODE proof
SORTS ANY
SIGNATURE
a: -> ANY
b: -> ANY
c: -> ANY
d: -> ANY
neg: ANY -> ANY
plus: ANY ANY -> ANY
ORDERING
LPO
neg > plus > c > d > b > a
VARIABLES
X, Y, Z: ANY
EQUATIONS
plus(X, Y) = plus(Y, X)
plus(X, plus(Y, Z)) = plus(plus(X, Y), Z)
neg(plus(neg(plus(X, Y)), neg(plus(X, neg(Y))))) = X
plus(c, d) = c
CONCLUSION
plus(X, X) = X
