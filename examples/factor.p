% Axioms about arithmetic.

cnf('commutativity_of_plus', axiom,
    X + Y = Y + X).
cnf('associativity_of_plus', axiom,
    X + (Y + Z) = (X + Y) + Z).
cnf('commutativity_of_times', axiom,
    X * Y = Y * X).
cnf('associativity_of_times', axiom,
    X * (Y * Z) = (X * Y) * Z).
cnf('plus_zero', axiom,
    '0' + X = X).
cnf('times_zero', axiom,
    '0' * X = '0').
cnf('times_one', axiom,
    '1' * X = X).
cnf('distributivity', axiom,
    X * (Y + Z) = (X * Y) + (X * Z)).
cnf('minus', axiom,
    X + -X = '0').

cnf(two, axiom, two = '1'+'1').
cnf(three, axiom, three = '1'+two).
cnf(four, axiom, four = '1'+three).
cnf(five, axiom, five = '1'+four).
cnf(six, axiom, six = '1'+five).
cnf(seven, axiom, seven = '1'+six).
cnf(eight, axiom, eight = '1'+seven).
cnf(nine, axiom, nine = '1'+eight).
cnf(minus_six, axiom, minus_four = -four).
cnf(minus_six, axiom, minus_six = -six).

fof(factoring, conjecture,
    ?[A,B,C]: ![X]:
      (X*(X*X)) + ((minus_six*(X*X)) + ((nine*X) + minus_four)) = ((X +
      -'1')*((X + -'1') * (X + -four)))).

fof(factoring, conjecture,
    ?[A,B,C]: ![X]:
    (X*(X*X)) +
    (-(('1'+('1'+('1'+('1'+('1'+'1')))))*(X*X)) +
     ((('1'+('1'+('1'+('1'+('1'+('1'+('1'+('1'+'1'))))))))*X) +
     -('1'+('1'+('1'+'1'))))) =
    (X + -A)*((X + -B)*(X + -C))).
