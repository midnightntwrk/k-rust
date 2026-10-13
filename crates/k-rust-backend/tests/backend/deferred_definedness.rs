//! The definedness of an operand that `#if`, `andThenBool` or `orElseBool` never evaluates is a
//! deferred atom (`Predicate::Defined`), decided only by steps that apply no definition
//! equation: folding by builtin hooks on literals, a ceil equation whose condition that folding
//! decides, the key condition of a collection of literal keys, and one equation step selected
//! by matching alone. The tests decide atoms through the predicate simplifier, which is the
//! only place that decides them, and read its work counters: no equation attempt and no round
//! of term simplification.

use k_rust_backend::{
    definition::BackendDefinition,
    rewrite::{ExecutionOptions, HaltReason, Pattern, execute},
    rule::Predicate,
    simplify::SimplificationOptions,
    smt::NoSolver,
    term::Term,
};
use k_rust_kore::{
    kore::parser::parse_definition,
    measure::{Counter, snapshot},
};

use crate::support::{internal_term, unstopped::simplify_predicate_with_solver};

/// `loopi() = loopi() +Int 1`, `f(X) = X +Int 1`, `two(X) = once(X)` and `once(X) = X`; the
/// partial hooked `lookup` (`MAP.lookup`) without an equation; the partial hooked `tdiv` with the
/// ceil equation `⌈tdiv(I1, I2)⌉ = (I2 =/=Int 0)`; over `Nat`,
/// `h(g(z)) = z` above `h(_) = \bottom [owise]`, with `g(s(X)) = z`, and `p(z) = z` above
/// `p(_) = \bottom [owise]`.
fn definition() -> BackendDefinition {
    let equation = |head: &str, sort: &str, pattern: &str, right: &str, attributes: &str| {
        format!(
            r"axiom{{R}} \implies{{R}}(\and{{R}}(\top{{R}}(), \and{{R}}(\in{{{sort}, R}}(X0:{sort}, {pattern}), \top{{R}}())), \equals{{{sort}, R}}({head}{{}}(X0:{sort}), \and{{{sort}}}({right}, \top{{{sort}}}()))) [{attributes}]"
        )
    };
    let nullary = r#"axiom{R} \implies{R}(\and{R}(\top{R}(), \top{R}()), \equals{SortInt{}, R}(loopi{}(), \and{SortInt{}}(plus{}(loopi{}(), \dv{SortInt{}}("1")), \top{SortInt{}}()))) [label{}("loop")]"#;
    let source = format!(
        r#"[] module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            sort SortKItem{{}} []
            hooked-sort SortMap{{}}
                [hook{{}}("MAP.Map"), unit{{}}(mapUnit{{}}()), element{{}}(mapItem{{}}()), concat{{}}(mapConcat{{}}())]
            hooked-symbol mapUnit{{}}() : SortMap{{}} [function{{}}(), total{{}}(), hook{{}}("MAP.unit")]
            hooked-symbol mapItem{{}}(SortInt{{}}, SortInt{{}}) : SortMap{{}}
                [function{{}}(), total{{}}(), hook{{}}("MAP.element")]
            hooked-symbol mapConcat{{}}(SortMap{{}}, SortMap{{}}) : SortMap{{}}
                [function{{}}(), hook{{}}("MAP.concat"), assoc{{}}(), comm{{}}()]
            hooked-symbol lookup{{}}(SortMap{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), hook{{}}("MAP.lookup")]
            hooked-symbol plus{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
            hooked-symbol tdiv{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), hook{{}}("INT.tdiv"), smt-hook{{}}("div")]
            hooked-symbol neInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.ne"), smt-hook{{}}("distinct")]
            symbol loopi{{}}() : SortInt{{}} [function{{}}()]
            symbol f{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
            symbol two{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
            symbol once{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
            sort SortNat{{}} []
            symbol z{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}()]
            symbol s{{}}(SortNat{{}}) : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol g{{}}(SortNat{{}}) : SortNat{{}} [function{{}}()]
            symbol h{{}}(SortNat{{}}) : SortNat{{}} [function{{}}()]
            symbol p{{}}(SortNat{{}}) : SortNat{{}} [function{{}}()]
            hooked-symbol ite{{}}(SortBool{{}}, SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), total{{}}(), hook{{}}("KEQUAL.ite")]
            hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.eq"), smt-hook{{}}("=")]
            symbol imp{{}}() : SortInt{{}} [function{{}}(), total{{}}(), impure{{}}()]
            symbol one{{}}() : SortInt{{}} [function{{}}(), total{{}}()]
            sort SortState{{}} []
            symbol hold{{}}(SortInt{{}}) : SortState{{}} [constructor{{}}()]
            {nullary}
            axiom{{R}} \implies{{R}}(\and{{R}}(\top{{R}}(), \top{{R}}()), \equals{{SortInt{{}}, R}}(imp{{}}(), \and{{SortInt{{}}}}(\dv{{SortInt{{}}}}("1"), \top{{SortInt{{}}}}()))) [label{{}}("imp")]
            axiom{{R}} \implies{{R}}(\and{{R}}(\top{{R}}(), \top{{R}}()), \equals{{SortInt{{}}, R}}(one{{}}(), \and{{SortInt{{}}}}(\dv{{SortInt{{}}}}("1"), \top{{SortInt{{}}}}()))) [label{{}}("one")]
            {}
            {}
            {}
            {}
            {}
            {}
            {}
            {}
            axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{R, R}}(
                \ceil{{SortInt{{}}, R}}(tdiv{{}}(I1:SortInt{{}}, I2:SortInt{{}})),
                \and{{R}}(
                    \equals{{SortBool{{}}, R}}(neInt{{}}(I2:SortInt{{}}, \dv{{SortInt{{}}}}("0")), \dv{{SortBool{{}}}}("true")),
                    \top{{R}}())))
                [label{{}}("ceil-div"), simplification{{}}()]
        endmodule []"#,
        equation(
            "f",
            "SortInt{}",
            "VarX:SortInt{}",
            r#"plus{}(VarX:SortInt{}, \dv{SortInt{}}("1"))"#,
            r#"label{}("f")"#
        ),
        equation(
            "two",
            "SortInt{}",
            "VarX:SortInt{}",
            "once{}(VarX:SortInt{})",
            r#"label{}("two")"#
        ),
        equation(
            "once",
            "SortInt{}",
            "VarX:SortInt{}",
            "VarX:SortInt{}",
            r#"label{}("once")"#
        ),
        equation(
            "g",
            "SortNat{}",
            "s{}(VarX:SortNat{})",
            "z{}()",
            r#"label{}("g")"#
        ),
        equation("h", "SortNat{}", "g{}(z{}())", "z{}()", r#"label{}("h")"#),
        equation(
            "h",
            "SortNat{}",
            "VarY:SortNat{}",
            r"\bottom{SortNat{}}()",
            r#"label{}("h-owise"), owise{}()"#
        ),
        equation("p", "SortNat{}", "z{}()", "z{}()", r#"label{}("p")"#),
        equation(
            "p",
            "SortNat{}",
            "VarY:SortNat{}",
            r"\bottom{SortNat{}}()",
            r#"label{}("p-owise"), owise{}()"#
        ),
    );
    let syntax = parse_definition(&source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

/// The predicate simplifier's decision of `Defined(subject)`, and whether it applied an
/// equation or simplified a term on the way.
fn decide(definition: &BackendDefinition, subject: &str) -> (Predicate, bool) {
    let atom = Predicate::Defined(internal_term(definition, subject));
    let before = snapshot();
    let decided = simplify_predicate_with_solver(
        definition,
        &atom,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap_or_else(|error| panic!("{subject}: {error:?}"));
    let work = snapshot().delta(&before);
    let evaluated =
        work.get(Counter::SimplifyEquationAttempts) > 0 || work.get(Counter::SimplifyRounds) > 0;
    (decided, evaluated)
}

fn defined(definition: &BackendDefinition, subject: &str) -> Predicate {
    Predicate::Defined(internal_term(definition, subject))
}

const LOOPI: &str = "loopi{}()";

#[test]
fn deciding_a_deferred_atom_applies_no_definition_equation() {
    // The subjects of the atoms an `#if` with a diverging discarded operand states: none is
    // evaluated, and each stays open, since only `loopi`'s equation could decide it.
    let definition = definition();
    let map = format!(
        r#"mapConcat{{}}(mapItem{{}}({LOOPI}, \dv{{SortInt{{}}}}("1")), mapItem{{}}(\dv{{SortInt{{}}}}("2"), \dv{{SortInt{{}}}}("2")))"#
    );
    for subject in [
        LOOPI.to_owned(),
        format!(r#"tdiv{{}}(\dv{{SortInt{{}}}}("1"), {LOOPI})"#),
        map,
    ] {
        let (decided, evaluated) = decide(&definition, &subject);
        assert_eq!(decided, defined(&definition, &subject), "{subject}");
        assert!(!evaluated, "{subject}");
    }
}

#[test]
fn one_equation_step_whose_instance_is_defined_establishes_a_deferred_atom() {
    // `f(-1) = -1 +Int 1` is an instance of an axiom whose right-hand side is defined, so
    // `f(-1)` is; `two(-1) = once(-1)` leaves `once(-1)`, which only another step would show
    // defined, so `two(-1)` stays open. Neither is evaluated.
    let definition = definition();
    let (decided, evaluated) = decide(&definition, r#"f{}(\dv{SortInt{}}("-1"))"#);
    assert_eq!(decided, Predicate::True);
    assert!(!evaluated);
    let subject = r#"two{}(\dv{SortInt{}}("-1"))"#;
    let (decided, evaluated) = decide(&definition, subject);
    assert_eq!(decided, defined(&definition, subject));
    assert!(!evaluated);
}

#[test]
fn a_ceil_equation_decides_a_deferred_atom_only_by_folding_its_condition() {
    // `⌈tdiv(I1, I2)⌉ = (I2 =/=Int 0)`: the condition folds to `true` at `I2 = 2` and to `false`
    // at `I2 = 0`, whatever `I1`; at `I2 = two(-1)` it needs two equation steps, so the atom stays
    // open although `two(-1)` is `-1`.
    let definition = definition();
    let (decided, evaluated) = decide(&definition, r#"tdiv{}(X:SortInt{}, \dv{SortInt{}}("2"))"#);
    assert_eq!(decided, Predicate::True);
    assert!(!evaluated);
    let (decided, _) = decide(&definition, r#"tdiv{}(X:SortInt{}, \dv{SortInt{}}("0"))"#);
    assert_eq!(decided, Predicate::False);
    let subject = r#"tdiv{}(\dv{SortInt{}}("1"), two{}(\dv{SortInt{}}("-1")))"#;
    let (decided, evaluated) = decide(&definition, subject);
    assert_eq!(decided, defined(&definition, subject));
    assert!(!evaluated);
    // Builtin hooks fold a subject on literals first: `1 /Int 0` is undefined.
    let (decided, _) = decide(
        &definition,
        r#"tdiv{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0"))"#,
    );
    assert_eq!(decided, Predicate::False);
}

#[test]
fn a_ceil_equation_over_hook_arithmetic_states_its_condition() {
    // D2': over variables, literals and pure total hooks the instance of the ceil equation is
    // stated in place of the opaque atom, so the solver reads `Y =/=Int 0` (simplified to
    // `\\not(Y = 0)`) itself.
    let definition = definition();
    let (decided, evaluated) = decide(&definition, "tdiv{}(X:SortInt{}, Y:SortInt{})");
    assert_eq!(
        decided,
        Predicate::Not(Box::new(Predicate::Equals(
            internal_term(&definition, "Y:SortInt{}"),
            internal_term(&definition, r#"\dv{SortInt{}}("0")"#),
        )))
    );
    // The stated condition is an ordinary predicate, simplified by its hooks.
    let _ = evaluated;
    // An argument that is not hook arithmetic keeps the atom.
    let subject = "tdiv{}(X:SortInt{}, two{}(Y:SortInt{}))";
    let (decided, _) = decide(&definition, subject);
    assert_eq!(decided, defined(&definition, subject));
}

#[test]
fn one_equation_step_gives_a_ground_argument_its_value() {
    // `f(-1) = -1 +Int 1` folds to `0` by hooks: one equation step on literal arguments, whose
    // right-hand side is decided by hooks alone, gives `f(-1)` its value, so `1 /Int f(-1)` is
    // `1 /Int 0`, undefined, and `1 /Int f(1)` is defined. `two(-1) = once(-1)` takes a second
    // step and gives no value. No step evaluates anything else.
    let definition = definition();
    let (decided, evaluated) = decide(
        &definition,
        r#"tdiv{}(\dv{SortInt{}}("1"), f{}(\dv{SortInt{}}("-1")))"#,
    );
    assert_eq!(decided, Predicate::False);
    assert!(!evaluated);
    let (decided, _) = decide(
        &definition,
        r#"tdiv{}(\dv{SortInt{}}("1"), f{}(\dv{SortInt{}}("1")))"#,
    );
    assert_eq!(decided, Predicate::True);
}

#[test]
fn a_map_of_distinct_literal_keys_establishes_only_its_own_key_condition() {
    // Distinct literal keys and no rest: the map's own condition holds; its values' atoms are
    // stated beside it. A rest may hold a key, so a map with one stays open.
    let definition = definition();
    let closed = format!(
        r#"mapConcat{{}}(mapItem{{}}(\dv{{SortInt{{}}}}("1"), {LOOPI}), mapItem{{}}(\dv{{SortInt{{}}}}("2"), \dv{{SortInt{{}}}}("3")))"#
    );
    let (decided, evaluated) = decide(&definition, &closed);
    assert_eq!(decided, Predicate::True);
    assert!(!evaluated);
    let open = r#"mapConcat{}(mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("2")), M:SortMap{})"#;
    let (decided, _) = decide(&definition, open);
    assert_eq!(decided, defined(&definition, open));
}

#[test]
fn a_hook_on_a_ground_collection_decides_a_deferred_atom() {
    // `MAP.lookup` reads its arguments only, so on a closed map of literals it decides the atom
    // without an equation: a key the map binds is defined, one it does not bind is not. An
    // argument that is not ground and constructor-like gives the hook nothing to read: a map
    // with a rest, and a map whose value `loopi()` only its equation could reduce, leave the
    // atom open, and `loopi()` is not evaluated.
    let definition = definition();
    let map = r#"mapConcat{}(mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("10")), mapItem{}(\dv{SortInt{}}("3"), \dv{SortInt{}}("30")))"#;
    let (decided, evaluated) = decide(
        &definition,
        &format!(r#"lookup{{}}({map}, \dv{{SortInt{{}}}}("3"))"#),
    );
    assert_eq!(decided, Predicate::True);
    assert!(!evaluated);
    let (decided, evaluated) = decide(
        &definition,
        &format!(r#"lookup{{}}({map}, \dv{{SortInt{{}}}}("2"))"#),
    );
    assert_eq!(decided, Predicate::False);
    assert!(!evaluated);
    // The key is folded first: `1 +Int 2` is `3`.
    let (decided, evaluated) = decide(
        &definition,
        &format!(
            r#"lookup{{}}({map}, plus{{}}(\dv{{SortInt{{}}}}("1"), \dv{{SortInt{{}}}}("2")))"#
        ),
    );
    assert_eq!(decided, Predicate::True);
    assert!(!evaluated);
    for subject in [
        r#"lookup{}(mapConcat{}(mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("10")), M:SortMap{}), \dv{SortInt{}}("3"))"#.to_owned(),
        format!(r#"lookup{{}}(mapItem{{}}(\dv{{SortInt{{}}}}("1"), {LOOPI}), \dv{{SortInt{{}}}}("1"))"#),
    ] {
        let (decided, evaluated) = decide(&definition, &subject);
        assert_eq!(decided, defined(&definition, &subject), "{subject}");
        assert!(!evaluated, "{subject}");
    }
}

#[test]
fn one_equation_step_does_not_refute_through_an_unevaluated_argument_below_a_function_pattern() {
    // `p(z) = z` fails to match `p(s(z))` on every instance, so the `owise` equation, whose
    // right-hand side is `\bottom`, applies there. `h(g(z)) = z` has a function below its root:
    // its match against `h(g(s(z)))` fails too, comparing `z` with `s(z)`, but `g(s(z))` is `z`
    // under `g`'s equation, so the failure refutes only the syntax of an unevaluated argument,
    // and the atom stays open.
    let definition = definition();
    let (decided, evaluated) = decide(&definition, "p{}(s{}(z{}()))");
    assert_eq!(decided, Predicate::False);
    assert!(!evaluated);
    let subject = "h{}(g{}(s{}(z{}())))";
    let (decided, evaluated) = decide(&definition, subject);
    assert_eq!(decided, defined(&definition, subject));
    assert!(!evaluated);
}

/// The one leaf of running `state` under `constraints` for at most `depth` steps.
fn run(
    definition: &BackendDefinition,
    state: &str,
    constraints: Vec<Predicate>,
    depth: u64,
) -> (Term, Vec<Predicate>, HaltReason) {
    let result = execute(
        definition,
        Pattern {
            term: internal_term(definition, state),
            constraints,
        },
        ExecutionOptions {
            max_depth: depth,
            ..ExecutionOptions::default()
        },
    );
    let [leaf] = result.leaves.as_slice() else {
        panic!("{state}: {:?}", result.leaves);
    };
    (
        leaf.pattern.term.clone(),
        leaf.pattern.constraints.clone(),
        leaf.halt_reason.clone(),
    )
}

#[test]
fn a_resumed_state_reads_a_ceil_as_the_deferred_atoms_of_its_subject() {
    // A run reports a deferred atom as `\ceil(t)`, and a state given back to execution reads it
    // as the atoms of `t`: here the map's own condition, which its literal keys establish, and
    // `loopi()`'s, which stays a sibling and is never evaluated.
    let definition = definition();
    let map = format!(
        r#"mapConcat{{}}(mapItem{{}}(\dv{{SortInt{{}}}}("1"), {LOOPI}), mapItem{{}}(\dv{{SortInt{{}}}}("2"), \dv{{SortInt{{}}}}("3")))"#
    );
    let (_, constraints, _) = run(
        &definition,
        r#"hold{}(\dv{SortInt{}}("0"))"#,
        vec![Predicate::Ceil(internal_term(&definition, &map))],
        1,
    );
    assert_eq!(constraints, [defined(&definition, LOOPI)]);
}

#[test]
fn a_resumed_ceil_stays_open_where_an_ordinary_one_is_evaluated() {
    // The cost of reading a resumed `\ceil` as deferred: `\ceil(two(3))` stays open in the
    // resumed state, where the ordinary `\ceil` is decided by evaluating `two(3)` to `3`.
    let definition = definition();
    let two = r#"two{}(\dv{SortInt{}}("3"))"#;
    let (_, constraints, _) = run(
        &definition,
        r#"hold{}(\dv{SortInt{}}("0"))"#,
        vec![Predicate::Ceil(internal_term(&definition, two))],
        1,
    );
    assert_eq!(constraints, [defined(&definition, two)]);
    let ordinary = simplify_predicate_with_solver(
        &definition,
        &Predicate::Ceil(internal_term(&definition, two)),
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();
    assert_eq!(ordinary, Predicate::True);
}

/// The constraints `source` simplifies under.
fn constraints_of(definition: &BackendDefinition, source: &str) -> Vec<Predicate> {
    crate::support::unstopped::simplify(
        definition,
        &internal_term(definition, source),
        SimplificationOptions::default(),
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"))
    .constraints()
    .to_vec()
}

#[test]
fn an_evaluated_operand_is_a_fact_only_when_it_holds_no_impure_application() {
    // The deciding operand `one() ==Int two(1)` is evaluated, so the discarded `two(1)`, one of
    // its subterms, is defined wherever the result is, and no obligation is stated. With `imp()`
    // (declared `impure`) in the deciding operand, the operand is no such fact: the discarded
    // `two(1)` keeps its deferred atom.
    let definition = definition();
    let pure = r#"ite{}(eqInt{}(one{}(), two{}(\dv{SortInt{}}("1"))), \dv{SortInt{}}("1"), two{}(\dv{SortInt{}}("1")))"#;
    assert_eq!(constraints_of(&definition, pure), []);
    let impure = r#"ite{}(eqInt{}(imp{}(), two{}(\dv{SortInt{}}("1"))), \dv{SortInt{}}("1"), two{}(\dv{SortInt{}}("1")))"#;
    assert_eq!(
        constraints_of(&definition, impure),
        [defined(&definition, r#"two{}(\dv{SortInt{}}("1"))"#)]
    );
}

#[test]
fn a_nested_conditional_states_its_discarded_atoms_once() {
    // The outer conditional's discarded `two(2)` is a subterm of its selected operand, the inner
    // conditional, so the outer omits it; the inner conditional discards the same `two(2)` and
    // states its atom, which the result keeps.
    let definition = definition();
    let nested = r#"ite{}(\dv{SortBool{}}("true"), ite{}(\dv{SortBool{}}("true"), \dv{SortInt{}}("1"), two{}(\dv{SortInt{}}("2"))), two{}(\dv{SortInt{}}("2")))"#;
    assert_eq!(
        constraints_of(&definition, nested),
        [defined(&definition, r#"two{}(\dv{SortInt{}}("2"))"#)]
    );
}
