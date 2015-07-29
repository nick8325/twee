NAME diff
MODE completion
SORTS ANY
SIGNATURE
+: -> ANY
app: ANY ANY -> ANY
ORDERING
KBO
+=1, app=0
app > +
VARIABLES
X, Y, Z: ANY
EQUATIONS
app(app(+, X), Y) = app(app(+, Y), X)
app(app(+, X), app(app(+, Y), Z)) = app(app(+, app(app(+, X), Y)), Z)
CONCLUSION
