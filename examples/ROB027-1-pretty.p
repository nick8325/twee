%--------------------------------------------------------------------------
% File     : ROB027-1 : TPTP v6.3.0. Released v1.2.0.
% Domain   : Robbins Algebra
% Problem  : -(-c) = c => Boolean
% Version  : [Win90] (equality) axioms.
%            Theorem formulation : Denies Huntington's axiom.
% English  : If there are elements c and d such that c+d=d, then the
%            algebra is Boolean.

% Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras
%          : [Win90] Winker (1990), Robbins Algebra: Conditions that make a
%          : [Wos94] Wos (1994), Two Challenge Problems
% Source   : [Wos94]
% Names    : - [Wos94]

% Status   : Open
% Rating   : 1.00 v2.0.0
% Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   2 RR)
%            Number of atoms       :    5 (   5 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    5 (   3 constant; 0-2 arity)
%            Number of variables   :    7 (   0 singleton)
%            Maximal term depth    :    6 (   3 average)
% SPC      : CNF_UNK_UEQ

% Comments : Commutativity, associativity, and Huntington's axiom
%            axiomatize Boolean algebra.
%--------------------------------------------------------------------------
%----Include axioms for Robbins algebra
%--------------------------------------------------------------------------
cnf(commutativity_of_add,axiom,
    ( '+'(X,Y) = '+'(Y,X) )).

cnf(associativity_of_add,axiom,
    ( '+'('+'(X,Y),Z) = '+'(X,'+'(Y,Z)) )).

cnf(robbins_axiom,axiom,
    ( '-'('+'('-'('+'(X,Y)),'-'('+'(X,'-'(Y))))) = X )).

%--------------------------------------------------------------------------
%--------------------------------------------------------------------------
cnf(double_negation,hypothesis,
    ( '-'('-'(c)) = c )).

cnf(prove_huntingtons_axiom,negated_conjecture,
    '+'('-'('+'(a,'-'(b))),'-'('+'('-'(a),'-'(b)))) != b).

%--------------------------------------------------------------------------
%----Definition of g
cnf(sos04,axiom,(
    g(A) = '-'('+'(A,'-'(A))) )).

%----Definition of h
cnf(sos05,axiom,(
    h(A) = '+'(A,'+'(A,'+'(A,'-'('+'(A,'-'(A)))))))).
