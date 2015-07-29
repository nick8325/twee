NAME semigroup
MODE completion
SORTS ANY
SIGNATURE
mult: ANY ANY -> ANY
ORDERING
KBO
mult=1
VARIABLES
X, Y, Z, W: ANY
EQUATIONS
mult(mult(X, Y), mult(Z, W)) = mult(mult(X, Z), mult(Y, W))
mult(mult(X, Y), X) = X
CONCLUSION
