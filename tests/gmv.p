cnf('Associativity-∧', axiom,
    (X ∧ Y) ∧ Z = X ∧ (Y ∧ Z)).   
cnf('Associativity-∨', axiom,
    (X ∨ Y) ∨ Z = X ∨ (Y ∨ Z)).
cnf('Idempotence-∧', axiom,
    X ∧ X = X).
cnf('Idempotence-∨', axiom,
    X ∨ X = X).
cnf('Commutativity-∧', axiom,
    X ∧ Y = Y ∧ X).
cnf('Commutativity-∨', axiom,
    X ∨ Y = Y ∨ X).
cnf('Absorption a', axiom,
    (X ∧ Y) ∨ X = X).
cnf('Absorption b', axiom,
    (X ∨ Y) ∧ X = X).

cnf('Residual a', axiom,
    (X * ((X \ Z) ∧ Y)) ∨ Z = Z).
cnf('Residual b', axiom,
    ((Y ∧ (Z / X)) * X) ∨ Z = Z).
cnf('Residual c', axiom,
    (X \ ((X * Y) ∨ Z)) ∧ Y = Y).
cnf('Residual d', axiom,
    (((Y * X) ∨ Z) / X) ∧ Y = Y).

cnf('Associativity-* (fusion)', axiom,
    (X * Y) * Z = X * (Y * Z)).
cnf('Left monoid unit', axiom,
    '1' * X = X).
cnf('Right monoid unit', axiom,
    X * '1' = X).

cnf('GMV a', axiom,
    X ∨ Y = X / ((X ∨ Y) \ X)).
cnf('GMV b', axiom,
    X ∨ Y = (X / (X ∨ Y)) \ X).

cnf('Definition-@', axiom,
    X @ Y = (X * (X \ '1')) * ((Y \ '1') \ '1')).

cnf('Goal 1', conjecture,
    x @ x = x).
cnf('Goal 2', conjecture,
    (x @ y) @ z = x @ z).
cnf('Goal 3', conjecture,
    x @ (y @ z) = x @ z).
  
cnf('Goal 4', conjecture,
    (x ∧ y) @ (z ∧ u) = (x @ z) ∧ (y @ u)).
cnf('Goal 5', conjecture,
    (x ∨ y) @ (z ∨ u) = (x @ z) ∨ (y @ u)).
cnf('Goal 6', conjecture,
    (x \ y) @ (z \ u) = (x @ z) \ (y @ u)).
cnf('Goal 7', conjecture,
    (x / y) @ (z / u) = (x @ z) / (y @ u)).
  
cnf('Goal 8', conjecture,
    (x * (x \ '1')) @ '1' = x * (x \ '1')).
cnf('Goal 9', conjecture,
    '1' @ (x * (x \ '1')) = '1').
cnf('Goal 10', conjecture,
    (x \ '1') @ '1' = '1').
cnf('Goal 11', conjecture,
    '1' @ (x \ '1') = x \ '1').
  
cnf('Goal 12', conjecture,
    (x / (y \ x)) @ (x ∨ y) = x ∨ y).
cnf('Goal 13', conjecture,
    ((x / y) \ x) @ (x ∨ y) = x ∨ y).
cnf('Goal 14', conjecture,
    (x ∨ y) @ (x / (y \ x)) = x / (y \ x)).
cnf('Goal 15', conjecture,
    (x ∨ y) @ ((x / y) \ x) = (x / y) \ x).
