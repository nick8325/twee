NAME semigroup
MODE proof
SORTS ANY
SIGNATURE
mult: ANY ANY -> ANY
a: -> ANY
b: -> ANY
ORDERING
KBO
a=1, b=1, mult=1
mult > b > a
VARIABLES
X, Y, Z: ANY
EQUATIONS
mult(X, mult(Y, Z)) = mult(mult(X, Y), Z)
mult(X, X) = mult(X, mult(X, X))
mult(mult(X, X), Y) = mult(Y, mult(X, X))
CONCLUSION
mult(mult(a, b), mult(a, b)) = mult(mult(a, a), mult(b, b))
