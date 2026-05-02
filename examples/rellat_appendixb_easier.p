% http://www.dcs.bbk.ac.uk/~szabolcs/rellat-jlamp-second-submission-2.pdf
% appendix b. theorem 3.4, clause 8, assuming axiom rl1.
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
cnf(rh1, axiom,
    upme(a ∧ X1,Y1,Z1) ∨ (Y1 ∧ Z1) = (((a ∧ X1) ∧ Y1) ∨ Z1) ∧ (((a ∧ X1) ∧ Z1) ∨ Y1)).
cnf(rh2, axiom,
    upme(X,Y,Z) = upme(X,Y,a ∧ Z) ∨ upme(X,Z,a ∧ Y)).
cnf(rl1, axiom,
    lome(X,Y,Z) = upme(X,upme(Y,X,Z),upme(Z,X,Y))).
fof(conjecture, conjecture,
    upme(a,x2,y2) = upme(a,x2,z2) => upme(x2,y2,z2) = lome(x2,y2,z2)).
