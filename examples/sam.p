cnf(f_assoc, axiom,
    meet(X,meet(Y,Z)) = meet(meet(X,Y),Z)).
cnf(f_comm, axiom,
    meet(X,Y) = meet(Y,X)).
cnf(f_idem, axiom,
    meet(X,X) = X).
cnf(g_assoc, axiom,
    join(X,join(Y,Z)) = join(join(X,Y),Z)).
cnf(g_comm, axiom,
    join(X,Y) = join(Y,X)).
cnf(g_idem, axiom,
    join(X,X) = X).

cnf(ax31, axiom,
    meet(X, join(X,Y)) = X).
cnf(ax32, axiom,
    meet(zero, X) = zero).
cnf(ax33, axiom,
    join(zero, X) = X).
cnf(ax34, axiom,
    join(X, meet(X, Y)) = X).
cnf(ax35, axiom,
    meet(one, X) = X).
cnf(ax36, axiom,
    join(one, X) = one).
cnf(ax37, axiom,
    meet(X,Z) = X =>
    meet(join(X,Y),Z) = join(X,meet(Y,Z))).

cnf(comp, definition,
    comp(X,Y) <=> (meet(X,Y) = zero & join(X,Y) = one)).

cnf(premise1, assumption,
    comp(a, join(c,d))).
cnf(premise2, assumption,
    comp(b, join(c,d))).
cnf(goal, conjecture,
    meet(join(a,meet(b,c)),join(a,meet(b,d)))=a).
