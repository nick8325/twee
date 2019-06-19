cnf(ifeq_axiom, axiom, ifeq(A, A, B, C)=B).
cnf(ifeq_axiom, axiom, ifeq(X2, X2, U2, V2)=U2).
cnf(ifeq_axiom, axiom, ifeq(X2, Y2, U2, U2)=U2).
cnf(ifeq_axiom, axiom, ifeq(X2, Y2, X2, Y2)=Y2).
cnf(ifeq_axiom, axiom,
    ifeq(ifeq(U2, V2, A4, B4), ifeq(U2, V2, A3, B3),
          ifeq(U2, V2, A, B), ifeq(U2, V2, A2, B2))=ifeq(U2, V2,
                                                            ifeq(A4, A3, A, A2),
                                                            ifeq(B4, B3, B, B2))).
cnf(ifeq_axiom, axiom,
    ifeq(X2, Y2, ifeq(X2, Y2, U2, V2),
          ifeq(X2, Y2, S2, T2))=ifeq(X2, Y2, U2, T2)).
cnf(a, axiom, ifeq(p, true, q, true)=q).
cnf(a, negated_conjecture, ifeq(q, true, a, b)=b).
cnf(a_1, negated_conjecture, ifeq(p, true, a, b)=b).
cnf(goal, negated_conjecture, a!=b).
