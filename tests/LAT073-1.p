%--------------------------------------------------------------------------
% File     : LAT073-1 : TPTP v7.2.0. Released v2.6.0.
% Domain   : Lattice Theory (Ortholattices)
% Problem  : Given single axiom MOL-23C, prove modularity
% Version  : [MRV03] (equality) axioms.
% English  : Given a single axiom candidate MOL-23C for modular ortholattices
%            (MOL) in terms of the Sheffer Stroke, prove a Sheffer stroke form
%            of modularity.

% Refs     : [MRV03] McCune et al. (2003), Sheffer Stroke Bases for Ortholatt
% Source   : [MRV03]
% Names    : MOL-23C-modularity [MRV03]

% Status   : Open
% Rating   : 1.00 v2.6.0
% Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR)
%            Number of atoms       :    2 (   2 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   3 constant; 0-2 arity)
%            Number of variables   :    4 (   1 singleton)
%            Maximal term depth    :    7 (   4 average)
% SPC      : CNF_OPN_RFO_PEQ_UEQ

% Comments :
%--------------------------------------------------------------------------
%----Single axiom MOL-23C
cnf(mol_23C,axiom,
    ( f(f(f(B,f(A,B)),B),f(A,f(C,f(f(A,B),f(f(C,C),D))))) = A )).

%----Denial of Sheffer stroke modularity
cnf(modularity,negated_conjecture,
    (  f(a,f(b,f(a,f(c,c)))) != f(a,f(c,f(a,f(b,b)))) )).

cnf(bonus, axiom, f(A,B)=f(B,A)).

%--------------------------------------------------------------------------
