%--------------------------------------------------------------------------
% File     : GRP196-1 : TPTP v7.4.0. Released v2.2.0.
% Domain   : Group Theory (Semigroups)
% Problem  : In semigroups, xyyy=yyyx -> (uy)^9 = u^9v^9.
% Version  : [MP96] (equality) axioms.
% English  :

% Refs     : [McC98] McCune (1998), Email to G. Sutcliffe
%          : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq
%          : [McC95] McCune (1995), Four Challenge Problems in Equational L
% Source   : [McC98]
% Names    : CS-3 [MP96]
%          : Problem B [McC95]

% Status   : Unsatisfiable
% Rating   : 0.88 v7.4.0, 0.91 v7.3.0, 0.89 v7.0.0, 0.95 v6.4.0, 1.00 v4.0.1, 0.93 v4.0.0, 0.92 v3.7.0, 0.89 v3.4.0, 1.00 v3.3.0, 0.93 v3.1.0, 1.00 v2.2.1
% Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR)
%            Number of atoms       :    3 (   3 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   2 constant; 0-2 arity)
%            Number of variables   :    5 (   0 singleton)
%            Maximal term depth    :   18 (   8 average)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments : The problem was originally posed for cancellative semigroups,
%            Otter does this with a nonstandard representation [MP96].
%--------------------------------------------------------------------------
%----Include semigroups axioms
include('Axioms/GRP008-0.ax').
%--------------------------------------------------------------------------
%----Hypothesis:
cnf(condition,hypothesis,
    ( '*'(X,'*'(Y,'*'(Y,Y))) = '*'(Y,'*'(Y,'*'(Y,X))) )).

%----Denial of conclusion:
cnf(prove_this,negated_conjecture,
    (  '*'(a,'*'(b,'*'(a,'*'(b,'*'(a,'*'(b,'*'(a,'*'(b,'*'(a,'*'(b,'*'(a,'*'(b,'*'(a,'*'(b,'*'(a,'*'(b,'*'(a,b))))))))))))))))) != '*'(a,'*'(a,'*'(a,'*'(a,'*'(a,'*'(a,'*'(a,'*'(a,'*'(a,'*'(b,'*'(b,'*'(b,'*'(b,'*'(b,'*'(b,'*'(b,'*'(b,b))))))))))))))))) )).

%--------------------------------------------------------------------------
