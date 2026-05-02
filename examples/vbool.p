fof(associativity, axiom,
    ![X, Y, Z]:
    X ⊕ (Y ⊕ Z) = (X ⊕ Y) ⊕ Z).

fof(commutativity, axiom,
    ![X, Y]:
    X ⊕ Y = Y ⊕ X).

fof(idempotence, axiom,
    ![X]:
    X ⊕ X = X).

fof(non_injectivity, conjecture,
    ![A, B]: ?[X]: A ⊕ X = B ⊕ X).

% Examples:
% plus is commutative, associative, and injective, but not idempotent
% max is idempotent, commutative, and associativity, but not injective
