tff(type, type, '_⁻¹' : $i > $i).
tff(type, type, '_⁻' : $i > $i).

cnf('commutativity of ∨', axiom,
    A ∨ B = B ∨ A).
cnf('associativity of ∨', axiom,
    A ∨ (B ∨ C) = (A ∨ B) ∨ C).
cnf('a kind of de Morgan', axiom,
    (A⁻ ∨ B⁻)⁻ ∨ (A⁻ ∨ B)⁻ = A).
cnf('definition of ∧', axiom,
    A ∧ B = (A⁻ ∨ B⁻)⁻).
cnf('associativity of ;', axiom,
    A ; (B ; C) = (A ; B) ; C).
cnf('identity for ;', axiom,
    A ; '1' = A).
cnf('distributivity of ; over ∨', axiom,
    (A ∨ B) ; C = (A ; C) ∨ (B ; C)).
cnf('involution of ⁻¹', axiom,
    A⁻¹ ⁻¹ = A).
cnf('additivity of ⁻¹', axiom,
    (A ∨ B)⁻¹ = A⁻¹ ∨ B⁻¹).
cnf('multiplicativity of ⁻¹', axiom,
    (A ; B)⁻¹ = B⁻¹ ; A⁻¹).
cnf('cancellativity of ⁻', axiom,
    (A⁻¹ ; (A ; B)⁻) ∨ B⁻ = B⁻).
cnf('definition of top', axiom,
    top = A ∨ A⁻).
cnf('definition of zero', axiom,
    zero = A ∧ A⁻).
cnf(goal, conjecture,
    ((r1 ; r2) ∧ r3) ∨ ((r1; (r2 ∧ (r1⁻¹ ; r3))) ∧ r3) =
    (r1 ; (r2 ∧ (r1⁻¹ ; r3))) ∧ r3).
