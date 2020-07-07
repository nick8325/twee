%------------------------------------------------------------------------------
% File     : GRP666-4 : TPTP v7.2.0. Released v4.0.0.
% Domain   : Group Theory (Quasigroups)
% Problem  : Inverse property A-loops are Moufang
% Version  : Especial.
% English  :

% Refs     : [KKP02] Kinyon et al. (2002), Every Diassociative A-loop is M
%          : [PS08]  Phillips & Stanovsky (2008), Automated Theorem Proving
%          : [Sta08] Stanovsky (2008), Email to G. Sutcliffe
% Source   : [Sta08]
% Names    : KKP02a [PS08]

% Status   : Unsatisfiable
% Rating   : 0.84 v7.1.0, 0.83 v7.0.0, 0.89 v6.3.0, 0.82 v6.2.0, 0.71 v6.1.0, 0.81 v5.5.0, 0.84 v5.4.0, 0.87 v5.3.0, 0.75 v5.2.0, 0.86 v5.1.0, 0.87 v5.0.0, 0.86 v4.1.0, 0.82 v4.0.1, 0.86 v4.0.0
% Syntax   : Number of clauses     :   12 (   0 non-Horn;  12 unit;   1 RR)
%            Number of atoms       :   12 (  12 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    8 (   4 constant; 0-2 arity)
%            Number of variables   :   25 (   0 singleton)
%            Maximal term depth    :    5 (   3 average)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments :
%------------------------------------------------------------------------------
cnf(c01,axiom,
    ( mult(A,ld(A,B)) = B )).

cnf(c02,axiom,
    ( ld(A,mult(A,B)) = B )).

cnf(c03,axiom,
    ( mult(rd(A,B),B) = A )).

cnf(c04,axiom,
    ( rd(mult(A,B),B) = A )).

cnf(c05,axiom,
    ( mult(A,unit) = A )).

cnf(c06,axiom,
    ( mult(unit,A) = A )).

cnf(c07,axiom,
    ( ld(mult(A,B),mult(A,mult(B,mult(C,D)))) = mult(ld(mult(A,B),mult(A,mult(B,C))),ld(mult(A,B),mult(A,mult(B,D)))) )).

cnf(c08,axiom,
    ( rd(mult(mult(mult(A,B),C),D),mult(C,D)) = mult(rd(mult(mult(A,C),D),mult(C,D)),rd(mult(mult(B,C),D),mult(C,D))) )).

cnf(c09,axiom,
    ( ld(A,mult(mult(B,C),A)) = mult(ld(A,mult(B,A)),ld(A,mult(C,A))) )).

cnf(c10,axiom,
    ( mult(i(A),mult(A,B)) = B )).

cnf(c11,axiom,
    ( mult(mult(A,B),i(B)) = A )).

cnf(goals,negated_conjecture,
    ( mult(mult(a,b),mult(c,a)) != mult(mult(a,mult(b,c)),a) )).

%------------------------------------------------------------------------------
