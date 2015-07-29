NAME y
MODE proof
SORTS ANY
SIGNATURE
a: -> ANY
false: -> ANY
true:  -> ANY
k: -> ANY
s: -> ANY
app: ANY ANY -> ANY
ORDERING
KBO
a=1, false=1, true=1, s=1, k=1, app=0
app > s > k > true > false > a
VARIABLES
X, Y, Z: ANY
EQUATIONS
app(app(k, X), Y) = X
app(app(app(s, X), Y), Z) = app(app(X, Z), app(Y, Z))
CONCLUSION
app(X, a) = app(a, app(X, a))
