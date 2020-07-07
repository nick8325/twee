%cnf(s_definition, axiom, '$'('$'('$'(s, X), Y), Z)='$'('$'(X, Z), '$'(Y, Z))).
%cnf(b_definition, axiom, '$'('$'('$'(b, X), Y), Z)='$'(X, '$'(Y, Z))).
%cnf(c_definition, axiom, '$'('$'('$'(c, X), Y), Z)='$'('$'(X, Z), Y)).
cnf(critical_pair, axiom, '$'('$'('$'(s, '$'(b, X)), Y), Z) = '$'(X, '$'(Z, '$'(Y, Z)))).
%cnf(i_definition, axiom, '$'(i, X)=X).
cnf(i_specific, axiom, '$'(i, '$'('$'(s, '$'(b, X)), i)) = '$'('$'(s, '$'(b, X)), i)).
cnf(wfp, axiom, wfp(X)='$'('$'('$'(s, '$'(b, X)), i), '$'('$'(s, '$'(b, X)), i))).
cnf(prove_wfp, negated_conjecture, wfp(a)!='$'(a, wfp(a))).
