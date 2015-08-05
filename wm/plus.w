NAME diff
MODE completion
SORTS ANY
SIGNATURE
+: ANY ANY -> ANY
0: -> ANY
ORDERING
KBO
+=1, 0=1
+ > 0
VARIABLES
X, Y, Z: ANY
EQUATIONS
+(X, Y) = +(Y, X)
+(X, +(Y, Z)) = +(+(X, Y), Z)
+(0, X) = X
+(X, X) = X
CONCLUSION
