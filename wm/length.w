NAME diff
MODE completion
SORTS ANY
SIGNATURE
length: ANY -> ANY
app: ANY ANY -> ANY
ORDERING
KBO
length=1, app=1
app > length
VARIABLES
X, Y, Z: ANY
EQUATIONS
app(X, app(Y, Z)) = app(app(X, Y), Z)
length(app(X, Y)) = length(app(Y, X))
CONCLUSION
