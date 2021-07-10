% http://www.dcs.bbk.ac.uk/~szabolcs/rellat-jlamp-second-submission-2.pdf
% appendix a. theorem 3.4, clause 7.
cnf(commutativity, axiom,
    X ∧ Y = Y ∧ X).
cnf(associativity, axiom,
    X ∧ (Y ∧ Z) = (X ∧ Y) ∧ Z).
cnf(commutativity, axiom,
    X ∨ Y = Y ∨ X).
cnf(associativity, axiom,
    X ∨ (Y ∨ Z) = (X ∨ Y) ∨ Z).
cnf(absorption, axiom,
    X ∨ (X ∧ Y) = X).
cnf(absorption, axiom,
    X ∧ (X ∨ Y) = X).
cnf(definition_of_upme, axiom,
    upme(X,Y,Z) = X ∧ (Y ∨ Z)).
cnf(definition_of_lome, axiom,
    lome(X,Y,Z) = (X ∧ Y) ∨ (X ∧ Z)).
cnf(definition_of_upjo, axiom,
    upjo(X,Y,Z) = (X ∨ Y) ∧ (X ∨ Z)).
cnf(definition_of_lojo, axiom,
    lojo(X,Y,Z) = X ∨ (Y ∧ Z)).

fof(conjecture, conjecture,
    (![X1, Y1, W]:
    upme(a ∧ X1,Y1,W) ∨ (Y1 ∧ W) = (((a ∧ X1) ∧ Y1) ∨ W) ∧ (((a ∧ X1) ∧ W) ∨ Y1)) =>
    upme(a ∧ z1,z2,z3) = lome(a ∧ z1,z2,z3)).
