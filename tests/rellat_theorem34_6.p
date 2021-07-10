% http://www.dcs.bbk.ac.uk/~szabolcs/rellat-jlamp-second-submission-2.pdf
% theorem 3.4, clause 6.
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
cnf(eq1, axiom,
    upme(a ∧ Z1,Z2,Z3) = lome(a ∧ Z1,Z2,Z3)).
cnf(qu2, axiom,
    upme(a,X2,Y2) = upme(a,X2,Z2) => upme(X2,Y2,Z2) = lome(X2,Y2,Z2)).
fof(rl1, conjecture,
    lome(x,y,z) =
    (x∧(y∧(x∨z)))∨(z∧(x∨y))).
%fof(rl2, conjecture,
%    t∧(((x∨y)∧(x∨z))∨((u∨w)∧(u∨v))) =
%    (t∧(((x∨y)∧(x∨z))∨(u∨(w∧v))))∨(t∧(((u∨w)∧(u∨v))∨(x∨(y∧z))))).
