NAME diff
MODE proof
SORTS ANY
SIGNATURE
a: -> ANY
b: -> ANY
neg: ANY -> ANY
plus: ANY ANY -> ANY
ORDERING
KBO
%LPO
a=1, b=1, neg=1, plus=1
neg > plus > b > a
VARIABLES
X, Y, Z: ANY
EQUATIONS
plus(X, Y) = plus(Y, X)
plus(X, plus(Y, Z)) = plus(plus(X, Y), Z)
neg(plus(neg(plus(X, Y)), neg(plus(X, neg(Y))))) = X
CONCLUSION
%plus(neg(plus(neg(a), b)), neg(plus(neg(a), neg(b)))) = a
plus(a, a) = a
