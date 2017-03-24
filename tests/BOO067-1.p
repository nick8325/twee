%--------------------------------------------------------------------------
% File     : BOO067-1 : TPTP v6.3.0. Released v2.6.0.
% Domain   : Boolean Algebra (Ternary)
% Problem  : Ternary Boolean Algebra Single axiom is complete, part 1
% Version  : [MP96] (equality) axioms.
% English  :

% Refs     : [McC98] McCune (1998), Email to G. Sutcliffe
%          : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.42 v6.3.0, 0.35 v6.2.0, 0.29 v6.1.0, 0.31 v6.0.0, 0.48 v5.5.0, 0.47 v5.4.0, 0.33 v5.3.0, 0.25 v5.2.0, 0.29 v5.1.0, 0.33 v5.0.0, 0.29 v4.1.0, 0.18 v4.0.1, 0.36 v4.0.0, 0.38 v3.7.0, 0.11 v3.4.0, 0.12 v3.3.0, 0.21 v3.1.0, 0.33 v2.7.0, 0.27 v2.6.0
% Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR)
%            Number of atoms       :    2 (   2 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    7 (   5 constant; 0-3 arity)
%            Number of variables   :    7 (   0 singleton)
%            Maximal term depth    :    5 (   3 average)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments : A UEQ part of BOO035-1
%--------------------------------------------------------------------------
cnf(single_axiom,axiom,
    ( multiply(multiply(A,inverse(A),B),inverse(multiply(multiply(C,D,E),F,multiply(C,D,G))),multiply(D,multiply(G,F,E),C)) = B )).

cnf(prove_tba_axioms_1,negated_conjecture,
    (  multiply(multiply(d,e,a),b,multiply(d,e,c)) != multiply(d,e,multiply(a,b,c)) )).

%--------------------------------------------------------------------------
