%fof(identity, axiom,
%    ![X]: f(X, e) = X).
%fof(right_inverse, axiom,
%    ![X]: f(X, i(X)) = e).
fof(associativity, axiom,
    ![X, Y, Z]: f(X, f(Y, Z)) = f(f(X, Y), Z)).
fof(left_inverse, axiom,
    ![X]: f(i(X),X) = e).
fof(left_identity, axiom,
    ![X]: f(e, X) = X).
cnf(a, axiom, a != b).

%fof(inverse_distrib, axiom,
%    ![X,Y]: f(i(X),i(Y)) = i(f(X,Y))).
%fof(commutativity, conjecture,
%    ![X,Y]: f(X,Y) = f(Y,X)).
