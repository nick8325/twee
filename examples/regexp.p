%% and, or
cnf(def, axiom, and(true,B) = B).
cnf(def, axiom, and(false,B) = false).
cnf(def, axiom, and(X,Y) = and(Y,X)).

cnf(def, axiom, or(true,B) = true).
cnf(def, axiom, or(false,B) = B).
cnf(def, axiom, or(X,Y) = or(Y,X)).

%% eq
cnf(def, axiom, eq(X,X) = true).
cnf(def, axiom, eq(X,Y) = eq(Y,X)).
cnf(def, axiom, eq(a,b) = false).
cnf(def, axiom, eq(a,c) = false).
cnf(def, axiom, eq(b,c) = false).

%% haseps
cnf(def, axiom, haseps(atom(A)) = false).
cnf(def, axiom, haseps(zero) = false).
cnf(def, axiom, haseps(eps) = true).
cnf(def, axiom, haseps(plus(P,Q)) = or(haseps(P),haseps(Q))).
cnf(def, axiom, haseps(seq(P,Q)) = and(haseps(P),haseps(Q))).
cnf(def, axiom, haseps(star(P)) = true).

%% step
cnf(def, axiom, step(atom(A),A) = eps).
cnf(def, axiom, eq(A,B) = false => step(atom(A),B) = zero).
cnf(def, axiom, step(zero,B) = zero).
cnf(def, axiom, step(eps,B) = zero).
cnf(def, axiom, step(plus(P,Q),B) = plus(step(P,B),step(Q,B))).
cnf(def, axiom, haseps(P) = true => step(seq(P,Q),B) = plus(seq(step(P,B),Q),step(Q,B))).
cnf(def, axiom, haseps(P) = false => step(seq(P,Q),B) = plus(seq(step(P,B),Q),zero)).
cnf(def, axiom, step(star(P),B) = seq(step(P,B),star(P))).

%% rec
cnf(def, axiom, rec(P,nil) = haseps(P)).
cnf(def, axiom, rec(P,cons(A,As)) = rec(step(P,A),As)).

%% question
cnf(hypothesis, axiom, rec(seq(P,Q), As) = rec(seq(Q,P), As)).
cnf(goal, axiom, true != false).

%cnf(a, axiom, atom(A) != zero & atom(A) != eps & atom(A) != plus(P, Q) & atom(A) != seq(P, Q) & atom(A) != star(P)).
%cnf(a, axiom, zero != eps & zero != plus(P, Q) & zero != seq(P, Q) & zero != star(P)).
%cnf(a, axiom, eps != plus(P, Q) & eps != seq(P, Q) & eps != star(P)).
%cnf(a, axiom, plus(P, Q) != seq(P, Q) & plus(P, Q) != star(P)).
%cnf(a, axiom, seq(P, Q) != star(P)).
%cnf(a, axiom, un_atom(atom(A)) = A).
%cnf(a, axiom, un_plus_1(plus(P, Q)) = P).
%cnf(a, axiom, un_plus_2(plus(P, Q)) = Q).
%cnf(a, axiom, un_seq_1(seq(P, Q)) = P).
%cnf(a, axiom, un_seq_2(seq(P, Q)) = Q).
%cnf(a, axiom, un_star(star(P)) = P).
%cnf(a, axiom, a != b & b != c & a != c).
