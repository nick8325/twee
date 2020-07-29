cnf(axiom, axiom,
    ((X + Y) + Z) + -(X+Z) = Y).
cnf('definition of identity', axiom,
    e = a + -a).
fof('identity is constant', conjecture,
    e = b + -b).
fof('left identity', conjecture,
    ![X]: e + X = X).
fof('right identity', conjecture,
    ![X]: X + e = e).
fof('left inverse', conjecture,
    ![X]: -X + X = e).
fof('right inverse', conjecture,
    ![X]: X + -X = e).
fof(associativity, conjecture,
    ![X, Y, Z]: (X + Y) + Z = X + (Y + Z)).
fof(commutativity, conjecture,
    ![X, Y]: X + Y = Y + X).
