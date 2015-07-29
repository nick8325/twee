NAME y
MODE proof
SORTS ANY
SIGNATURE
a: -> ANY
false: -> ANY
true:  -> ANY
k: -> ANY
s: -> ANY
equals: ANY ANY -> ANY
app: ANY ANY -> ANY
ORDERING
KBO
a=1, false=1, true=1, s=1, k=1, equals=0, app=1
equals > app > s > k > true > false > a
VARIABLES
X, Y, Z: ANY
EQUATIONS
app(app(k, X), Y) = X
app(app(app(s, X), Y), Z) = app(app(X, Z), app(Y, Z))
equals(X, X) = true
equals(app(X, a), app(a, app(X, a))) = false
CONCLUSION
false = true
