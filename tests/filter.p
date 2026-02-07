fof('associativity of ∘', axiom,
    ![F, G, H]:
    F ∘ (G ∘ H) = (F ∘ G) ∘ H).

fof('∘ identity', axiom,
    ![F]:
    id ∘ F = F).

fof('∘ identity', axiom,
    ![F]:
    F ∘ id = F).

fof('map functor', axiom,
    ![F, G]:
    map(F) ∘ map(G) = map(F ∘ G)).

fof('map functor', axiom,
    map(id) = id).

fof('naturality of concat', axiom,
    ![F]:
    map(F) ∘ concat = concat ∘ map(map(F))).

fof('defn filter', axiom,
    ![P]:
    filter(P) = concat ∘ map(test(P))).

% test(P) = \x -> if P(x) then [x] else []

%fof('test property', axiom,
%    ![P, F]:
%    test(P) ∘ F =
%    map(F) ∘ test(P ∘ F)).

fof('map/filter', conjecture,
    ![P, F]:
    filter(P) ∘ map(F) = map(F) ∘ filter(P ∘ F)).


% cond(P, F, G) = \x -> if P(x) then F(x) else G(x)

fof('test defn', axiom,
    ![P]:
    test(P) = cond(P, unit, nil)).
fof('cond ∘', axiom,
    ![F, P, G, H]:
    F ∘ cond(P, G, H) = cond(P, F ∘ G, F ∘ H)).
fof('cond ∘', axiom,
    ![F, P, G, H]:
    cond(P, G, H) ∘ F = cond(P ∘ F, G ∘ F, H ∘ F)).
fof('nil', axiom,
    ![F]:
    nil ∘ F = nil).
fof('nil', axiom,
    ![F]:
    map(F) ∘ nil = nil).
fof('unit', axiom,
    ![F]:
    map(F) ∘ unit = unit ∘ F).
