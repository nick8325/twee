%--------------------------------------------------------------------------
% File     : LAT072-1 : TPTP v6.3.0. Released v2.6.0.
% Domain   : Lattice Theory (Ortholattices)
% Problem  : Given single axiom OML-23A, prove associativity
% Version  : [MRV03] (equality) axioms.
% English  : Given a single axiom candidate OML-23A for orthomodular lattices
%            (OML) in terms of the Sheffer Stroke, prove a Sheffer stroke form
%            of associativity.

% Refs     : [MRV03] McCune et al. (2003), Sheffer Stroke Bases for Ortholatt
% Source   : [MRV03]
% Names    : OML-23A-associativity [MRV03]

% Status   : Unsatisfiable
% Rating   : 0.95 v6.3.0, 0.94 v6.2.0, 0.93 v6.1.0, 0.94 v6.0.0, 0.95 v5.4.0, 1.00 v2.6.0
% Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR)
%            Number of atoms       :    2 (   2 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   3 constant; 0-2 arity)
%            Number of variables   :    4 (   2 singleton)
%            Maximal term depth    :    7 (   4 average)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments :
%--------------------------------------------------------------------------
%----Single axiom OML-23A
cnf(oml_23A,axiom,
    ( f(f(f(f(B,A),f(A,C)),D),f(A,f(f(C,f(f(A,A),C)),C))) = A )).

cnf(a, axiom, f(X,Y) = f(Y, X)).

%----Denial of Sheffer stroke associativity
cnf(associativity,negated_conjecture,
    (  f(a,f(f(b,c),f(b,c))) != f(c,f(f(b,a),f(b,a))) )).

%--------------------------------------------------------------------------
