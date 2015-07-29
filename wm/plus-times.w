NAME diff
MODE completion
SORTS ANY
SIGNATURE
0: -> ANY
1: -> ANY
+: ANY ANY -> ANY
*: ANY ANY -> ANY
ORDERING
KBO
0=1, 1=1, +=1, *=1
* > + > 1 > 0
VARIABLES
X, Y, Z: ANY
EQUATIONS
+(X, Y) = +(Y, X)
+(X, +(Y, Z)) = +(+(X, Y), Z)
+(0, X) = X
*(X, Y) = *(Y, X)
*(X, *(Y, Z)) = *(*(X, Y), Z)
*(0, X) = 0
*(1, X) = X
*(X, +(Y, Z)) = +(*(X, Y), *(X, Z))
CONCLUSION
