cnf('associativity of ∘', axiom,
    F ∘ (G ∘ H) = (F ∘ G) ∘ H).

cnf('∘ identity', axiom,
    id ∘ F = F).

cnf('∘ identity', axiom,
    F ∘ id = F).

cnf('map functor', axiom,
    map(F) ∘ map(G) = map(F ∘ G)).

cnf('map functor', axiom,
    map(id) = id).

cnf('defn pruneBy', axiom,
    pruneBy(F) = F ∘ (map(pruneRow) ∘ F)).

cnf('defn expand', axiom,
    expand = product ∘ map(product)).

cnf('expand after boxs', axiom,
    expand ∘ boxs = map(boxs) ∘ expand).

cnf('filter with boxs', axiom,
    filter (P ∘ boxs) = map(boxs) ∘ (filter(P) ∘ map(boxs))).

cnf('boxs involution', axiom,
    boxs ∘ boxs = id).

cnf('filter after product', axiom,
    filter(all(P)) ∘ product = product ∘ map(filter(P))).

cnf('law of pruneRow', axiom,
    filter(nodups) ∘ (product ∘ pruneRow) = filter(nodups) ∘ product).

cnf('conjecture', conjecture,
    filter(all(nodups) ∘ boxs) ∘ (expand ∘ pruneBy(boxs)) =
    filter(all(nodups) ∘ boxs) ∘ expand).
