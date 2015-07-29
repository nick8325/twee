NAME y
MODE proof
SORTS ANY
SIGNATURE
a: -> ANY
false: -> ANY
true:  -> ANY
c: -> ANY
f: -> ANY
w: -> ANY
equals: ANY ANY -> ANY
app: ANY ANY -> ANY
ORDERING
KBO
a=1, false=1, true=1, c=1, f=1, w=1, equals=0, app=0
equals > app > w > f > c > true > false > a
VARIABLES
X, Y, Z: ANY
EQUATIONS
app(w, X) = app(X, X)
app(app(app(c, X), Y), Z) = app(X, app(Y, Z))
app(app(app(f, X), Y), Z) = app(app(X, Z), Y)
equals(X, X) = true
equals(app(X, a), app(a, app(X, a))) = false
CONCLUSION
false = true
