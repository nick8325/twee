% SPASS solves this instantly, Twee takes ages!
cnf(axiom, axiom, multiply(U,add(V,W))=add(multiply(U,V),multiply(U,W))).
cnf(axiom, axiom, add(U,additive_inverse(add(additive_inverse(V),U)))=V).
cnf(axiom, axiom, add(U,additive_inverse(add(V,add(W,U))))=additive_inverse(add(V,W))).
cnf(axiom, axiom, add(additive_inverse(U),V)=additive_inverse(add(U,additive_inverse(V)))).
cnf(axiom, axiom, multiply(multiply(U,V),W)=add(associator(U,V,W),multiply(U,multiply(V,W)))).
cnf(axiom, axiom, additive_inverse(add(multiply(U,multiply(V,W)),add(multiply(U,multiply(X,W)),additive_inverse(add(multiply(multiply(U,V),W),multiply(multiply(U,X),W))))))=associator(U,add(V,X),W)).

cnf(conjecture, conjecture, add(associator(U,V,W),associator(U,X,W))=associator(U,add(V,X),W)).
