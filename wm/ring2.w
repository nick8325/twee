NAME diff
MODE proof
SORTS ANY
SIGNATURE
a: -> ANY
b: -> ANY
0: -> ANY
1: -> ANY
+: ANY ANY -> ANY
*: ANY ANY -> ANY
-: ANY -> ANY
ORDERING
KBO
0=1, 1=1, +=1, *=1, -=1, a=1, b=1
- > * > + > 1 > 0 > a > b
VARIABLES
X, Y, Z: ANY
EQUATIONS
+(X, Y) = +(Y, X)
+(X, +(Y, Z)) = +(+(X, Y), Z)
+(0, X) = X
+(X, -(X)) = 0
*(X, *(Y, Z)) = *(*(X, Y), Z)
*(X, +(Y, Z)) = +(*(X, Y), *(X, Z))
*(+(X, Y), Z) = +(*(X, Z), *(Y, Z))
*(X, *(X, *(X, *(X, *(X, X))))) = X
CONCLUSION
*(a, b) = *(b, a)
