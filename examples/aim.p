cnf(left_ident, axiom,
  '1' * X = X).
cnf(right_ident, axiom,
  X * '1' = X).
cnf(left_division_1, axiom,
  X \ (X * Y) = Y).
cnf(left_division_2, axiom,
  X * (X \ Y) = Y).
cnf(right_division_1, axiom,
  (X * Y) / Y = X).
cnf(right_division_2, axiom,
  (X / Y) * Y = X).
cnf(associator, axiom,
  (X * (Y * Z)) \ ((X * Y) * Z) = a(X,Y,Z)).
cnf(commutator, axiom,
  (X * Y) \ (Y * X) = k(Y,X)).
cnf(l, axiom,
  (Y * X) \ (Y * (X * U)) = l(U,X,Y)).
cnf(r, axiom,
  ((U * X) * Y) / (X * Y) = r(U,X,Y)).
cnf(t, axiom,
  X \ (U * X) = t(U,X)).
cnf(abelian_inner_mapping_1, axiom,
  t(t(U,X),Y) = t(t(U,Y),X)).
cnf(abelian_inner_mapping_2, axiom,
  t(l(U,X,Y),Z) = l(t(U,Z),X,Y)).
cnf(abelian_inner_mapping_3, axiom,
  t(r(U,X,Y),Z) = r(t(U,Z),X,Y)).
cnf(abelian_inner_mapping_4, axiom,
  l(r(U,X,Y),Z,W) = r(l(U,Z,W),X,Y)).
cnf(abelian_inner_mapping_5, axiom,
  l(l(U,X,Y),Z,W) = l(l(U,Z,W),X,Y)).
cnf(abelian_inner_mapping_6, axiom,
  r(r(U,X,Y),Z,W) = r(r(U,Z,W),X,Y)).

% aK (or "single-a") goals
cnf(ka, conjecture,
  k(a(x,y,z),u) = '1').
cnf(aK1, conjecture,
  a(k(x,y),z,u) = '1').
cnf(aK2, conjecture,
  a(x,k(y,z),u) = '1').
cnf(aK3, conjecture,
  a(x,y,k(z,u)) = '1').

% aa (or "double-a") goals
cnf(aa1, conjecture,
  a(a(x,y,z),u,w) = '1').
cnf(aa2, conjecture,
  a(x,a(y,z,u),w) = '1').
cnf(aa3, conjecture,
  a(x,y,a(z,u,w)) = '1').

cnf(bonus, axiom, (X * (Y / X)) \ X = Y \ (Y / (Y / X))).
