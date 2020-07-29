% http://www.dcs.bbk.ac.uk/~szabolcs/rellat-jlamp-second-submission-2.pdf
% appendix b. theorem 3.4, clause 8.
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
cnf('definition of upme', axiom,
    upme(X,Y,Z) = X ∧ (Y ∨ Z)).
cnf('definition of lome', axiom,
    lome(X,Y,Z) = (X ∧ Y) ∨ (X ∧ Z)).
%cnf('definition of upjo', axiom,
%    upjo(X,Y,Z) = (X ∨ Y) ∧ (X ∨ Z)).
%cnf('definition of lojo' axiom,
%    lojo(X,Y,Z) = X ∨ (Y ∧ Z)).
cnf('upme property 1', axiom,
    upme(a ∧ X1,Y1,Z1) ∨ (Y1 ∧ Z1) = (((a ∧ X1) ∧ Y1) ∨ Z1) ∧ (((a ∧ X1) ∧ Z1) ∨ Y1)).
cnf('upme property 2', axiom,
    upme(X,Y,Z) = upme(X,Y,a ∧ Z) ∨ upme(X,Z,a ∧ Y)).
fof(conjecture, conjecture,
    upme(a,x2,y2) = upme(a,x2,z2) => upme(x2,y2,z2) = lome(x2,y2,z2)).
