rules(Module, Rule, Used) :-
    %(Module:step(add(rule(_, Rule))); Module:step(add(rule(_, Rule, _, _)))),
    Module:step(add(rule(_, Rule, _, _))),
    (find_lemma(Module, Rule) -> Used=true; Used=false).

find_lemma(Module, Rule) :-
    copy_term(Rule, GroundRule), numbervars(GroundRule),
    clause(Module:lemma(GroundRule), true, Ref),
    clause(Module:lemma(Lemma), true, Ref),
    Rule =@= Lemma.

anywhere(Module, T) :-
    Module:goal(T); Module:axiom(T); rules(Module, T, _).

module_var(Module, X) :-
    anywhere(Module, T),
    term_variables(T, Xs),
    numbervars(Xs),
    member(X, Xs).

all_vars(Module, S) :-
    setof(X, module_var(Module, X), S).

module_func(Where, X/N) :-
    call(Where, T),
    sub_term(U, T),
    nonvar(U),
    functor(U, X, N),
    X \= '='.

module_func_with_count(Module, F, AxiomCount, GoalCount) :-
    module_func(anywhere(Module), F),
    once(setof(_, module_func(Module:axiom, F), S1); S1=[]),
    once(setof(_, module_func(Module:goal, F), S2); S2=[]),
    length(S1, AxiomCount),
    length(S2, GoalCount).

all_funcs(Module, S) :-
    setof(X/AxiomCount/GoalCount, module_func_with_count(Module, X, AxiomCount, GoalCount), S).

print_trace(Module) :-
    all_vars(Module, S),
    all_funcs(Module, T),
    writeln((vars, S)),
    writeln((funcs, T)),
    forall(Module:goal(Goal), (numbervars(Goal), writeln((goal, Goal)))),
    forall(Module:axiom(Axiom), (numbervars(Axiom), writeln((axiom, Axiom)))),
    forall(rules(Module, Rule, Used), (numbervars(Rule), writeln((Used, Rule)))).

init :- writeln(hello).
