%--------------------------------------------------------------------------
% File     : LAT071-1 : TPTP v6.2.0. Released v2.6.0.
% Domain   : Lattice Theory (Orthomodularlattices)
% Problem  : Given single axiom OML-21C, prove associativity
% Version  : [MRV03] (equality) axioms.
% English  : Given a single axiom candidate OML-21C for orthomodular lattices
%            (OML) in terms of the Sheffer Stroke, prove a Sheffer stroke form
%            of associativity.

% Refs     : [MRV03] McCune et al. (2003), Sheffer Stroke Bases for Ortholatt
% Source   : [MRV03]
% Names    : OML-21C-associativity [MRV03]

% Status   : Open
% Rating   : 1.00 v2.6.0
% Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR)
%            Number of atoms       :    2 (   2 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   3 constant; 0-2 arity)
%            Number of variables   :    4 (   2 singleton)
%            Maximal term depth    :    6 (   4 average)
% SPC      : CNF_UNK_UEQ

% Comments :
%--------------------------------------------------------------------------
%----Single axiom OML-21C
cnf(oml_21C,axiom,
    ( f(f(B,A),f(f(f(f(B,A),A),f(C,A)),f(f(A,A),D))) = A )).

cnf(a, axiom, f(z, f(z, z)) = k).
cnf(fbc, axiom, fbc=f(b,c)).
cnf(fba, axiom, fba=f(b,a)).
cnf(fbc2, axiom, fbc2=f(fbc,fbc)).
cnf(fba2, axiom, fba2=f(fba,fba)).
cnf(lhs, axiom, lhs=f(a,fbc2)).
cnf(rhs, axiom, rhs=f(c,fba2)).
cnf(comm, axiom, f(X,Y)=f(Y,X)).

%----Denial of Sheffer stroke associativity
cnf(associativity,negated_conjecture,
    lhs != rhs).

%--------------------------------------------------------------------------
