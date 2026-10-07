use k_rust_backend::{
    definition::{BackendDefinition, DefinitionError},
    rule::Predicate,
    simplify::SimplificationOptions,
    smt::NoSolver,
    term::{FunctionType, HeadRole, SymbolType},
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::support::{
    internal_term,
    unstopped::{simplify, simplify_predicate_with_solver},
};

const SOURCE: &str = r#"[]
    module MAIN
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
            [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
        hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
            [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
        sort SortS{} []
        symbol mk{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol wrap{}(SortInt{}) : SortS{} [anywhere{}()]
        axiom{R} \implies{R}(
            \and{R}(
                \equals{SortBool{}, R}(
                    eqInt{}(VarX:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                ),
                \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \top{R}())
            ),
            \equals{SortS{}, R}(
                wrap{}(X0:SortInt{}),
                \and{SortS{}}(
                    mk{}(divInt{}(VarX:SortInt{}, \dv{SortInt{}}("0"))),
                    \top{SortS{}}()
                )
            )
        ) [anywhere{}()]
        symbol half{}(SortInt{}) : SortS{} [macro{}()]
    endmodule []"#;

fn internalize(source: &str) -> Result<BackendDefinition, DefinitionError> {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
}

#[test]
fn an_unclaimed_anywhere_head_is_a_partial_equation_head() {
    let definition = internalize(SOURCE).expect("unclaimed equation heads should internalize");
    let attributes = &definition.symbols()["wrap"].attributes;
    assert_eq!(
        attributes.symbol_type,
        SymbolType::Function(FunctionType::Partial)
    );
    assert_eq!(attributes.head_role(), HeadRole::EquationHead);
}

#[test]
fn an_unclaimed_macro_symbol_is_a_partial_residual() {
    let definition = internalize(SOURCE).expect("unclaimed equation heads should internalize");
    let attributes = &definition.symbols()["half"].attributes;
    assert_eq!(
        attributes.symbol_type,
        SymbolType::Function(FunctionType::Partial)
    );
    assert_eq!(attributes.head_role(), HeadRole::Residual);
}

/// Single-valuedness does not make a value production a computed function.
/// Its equation can still make an application undefined, so the marker must not imply totality.
#[test]
fn marked_value_productions_keep_the_unclaimed_roles_and_definedness() {
    let source = SOURCE
        .replace(
            "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}()]",
            "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]",
        )
        .replace(
            "[macro{}()]",
            "[macro{}(), function{}(), value-production{}()]",
        );
    let definition = internalize(&source).expect("marked value productions should internalize");
    for (name, role) in [
        ("wrap", HeadRole::EquationHead),
        ("half", HeadRole::Residual),
    ] {
        let attributes = &definition.symbols()[name].attributes;
        assert_eq!(
            attributes.symbol_type,
            SymbolType::Function(FunctionType::Partial)
        );
        assert_eq!(attributes.head_role(), role);
    }
    for name in ["divInt", "eqInt"] {
        assert!(
            matches!(
                definition.symbols()[name].attributes.head_role(),
                HeadRole::Function { declared: true, .. }
            ),
            "{name}"
        );
    }
    assert_eq!(
        simplified_predicate(&definition, r"\ceil{SortS{}, SortS{}}(wrap{}(X:SortInt{}))"),
        Predicate::Ceil(internal_term(&definition, "wrap{}(X:SortInt{})")),
    );
    assert_eq!(
        simplified_predicate(
            &definition,
            r#"\ceil{SortS{}, SortS{}}(wrap{}(\dv{SortInt{}}("0")))"#
        ),
        Predicate::False,
    );
    let computed = internalize(&SOURCE.replace("[anywhere{}()]", "[anywhere{}(), function{}()]"))
        .expect("a declared function should internalize");
    assert!(matches!(
        computed.symbols()["wrap"].attributes.head_role(),
        HeadRole::Function { declared: true, .. }
    ));
}

#[test]
fn a_symbol_without_claim_or_equation_marker_is_still_rejected() {
    let source = SOURCE.replace(
        "sort SortS{} []",
        "sort SortS{} []\n        symbol plain{}(SortInt{}) : SortS{} []",
    );
    assert!(matches!(
        internalize(&source),
        Err(DefinitionError::InvalidSymbolType(_))
    ));
}

fn simplified_predicate(definition: &BackendDefinition, source: &str) -> Predicate {
    let syntax = parse_pattern(source).expect("predicate should parse");
    let (predicate, _) = definition
        .admit_unverified(&syntax, &[])
        .internalize_predicate()
        .expect("predicate should internalize");
    simplify_predicate_with_solver(
        definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("predicate should simplify")
}

/// A value production whose anywhere equation `wrap(s(X)) = wrap(X)` reapplies its own head, so
/// no totality claim is emitted for it; `t` is a second constructor of the argument sort.
const VALUE_HEAD: &str = r#"[]
    module MAIN
        sort SortNat{} []
        symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
        symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
        symbol t{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
        sort SortW{} []
        symbol wrap{}(SortNat{}) : SortW{} [anywhere{}(), function{}(), value-production{}()]
        axiom{R} \implies{R}(
            \and{R}(
                \top{R}(),
                \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(VarX:SortNat{})), \top{R}())
            ),
            \equals{SortW{}, R}(
                wrap{}(X0:SortNat{}),
                \and{SortW{}}(wrap{}(VarX:SortNat{}), \top{SortW{}}())
            )
        ) [anywhere{}()]
    endmodule []"#;

/// `value-production` states that an application no equation reduces is a value of its sort.
/// So where no equation can reach any instance of an application, its definedness is that of
/// its arguments: `wrap(z)` and `wrap(t(Y))` (whose arguments the equation's `s(_)` cannot match)
/// are defined, and `wrap(s(z))` is defined because it evaluates to `wrap(z)`. `wrap(Y)` keeps
/// its obligation, since the equation reaches its instance `wrap(s(z))`. Without the marker the
/// anywhere head claims nothing about an irreducible application, so `wrap(z)` keeps its
/// obligation too.
#[test]
fn an_irreducible_value_production_application_is_defined() {
    let definition = internalize(VALUE_HEAD).expect("value production should internalize");
    for (query, expected) in [
        ("wrap{}(z{}())", Predicate::True),
        ("wrap{}(t{}(Y:SortNat{}))", Predicate::True),
        ("wrap{}(s{}(z{}()))", Predicate::True),
        (
            "wrap{}(Y:SortNat{})",
            Predicate::Ceil(internal_term(&definition, "wrap{}(Y:SortNat{})")),
        ),
    ] {
        assert_eq!(
            simplified_predicate(
                &definition,
                &format!(r"\ceil{{SortW{{}}, SortW{{}}}}({query})")
            ),
            expected,
            "{query}"
        );
    }
    let unmarked = internalize(&VALUE_HEAD.replace(
        "[anywhere{}(), function{}(), value-production{}()]",
        "[anywhere{}()]",
    ))
    .expect("an unmarked anywhere head should internalize");
    assert_eq!(
        simplified_predicate(&unmarked, r"\ceil{SortW{}, SortW{}}(wrap{}(z{}()))"),
        Predicate::Ceil(internal_term(&unmarked, "wrap{}(z{}())")),
    );
}

/// Without a totality claim, `ceil(wrap(X))` remains an obligation.
/// The equation makes both `ceil(wrap(0))` and `wrap(0)` bottom.
/// Adding `functional` makes the symbolic query top, contradicting its bottom instance at `X = 0`.
#[test]
fn the_definedness_of_a_partial_equation_head_is_decided_by_its_equations() {
    let definition = internalize(SOURCE).expect("unclaimed equation heads should internalize");
    let query = r"\ceil{SortS{}, SortS{}}(wrap{}(X:SortInt{}))";
    let symbolic = simplified_predicate(&definition, query);
    assert_ne!(symbolic, Predicate::True);
    assert_eq!(
        symbolic,
        Predicate::Ceil(internal_term(&definition, "wrap{}(X:SortInt{})"))
    );
    assert_eq!(
        simplified_predicate(
            &definition,
            r#"\ceil{SortS{}, SortS{}}(wrap{}(\dv{SortInt{}}("0")))"#,
        ),
        Predicate::False,
    );
    let result = simplify(
        &definition,
        &internal_term(&definition, r#"wrap{}(\dv{SortInt{}}("0"))"#),
        SimplificationOptions::default(),
    )
    .expect("term should simplify");
    // The result conjoins its constraints to the retained term, so false makes it bottom.
    assert_eq!(result.constraints(), [Predicate::False]);

    let claimed = internalize(&SOURCE.replace(
        "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}()]",
        "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}(), functional{}()]",
    ))
    .expect("claimed equation heads should internalize");
    assert_eq!(simplified_predicate(&claimed, query), Predicate::True);
}

/// `SOURCE` with `wrap` marked as a value production, and `u()`, an unmarked anywhere constant
/// that no equation reduces: its definedness stays an obligation of its own.
fn conditional_value_production() -> BackendDefinition {
    internalize(
        &SOURCE
            .replace(
                "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}()]",
                "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]\n        symbol u{}() : SortInt{} [anywhere{}()]",
            ),
    )
    .expect("a conditional value production should internalize")
}

fn simplified_predicate_under(
    definition: &BackendDefinition,
    source: &str,
    known: &[&str],
) -> Predicate {
    let internalize = |source: &str| {
        let syntax = parse_pattern(source).expect("predicate should parse");
        definition
            .admit_unverified(&syntax, &[])
            .internalize_predicate()
            .expect("predicate should internalize")
            .0
    };
    let known = known
        .iter()
        .map(|source| internalize(source))
        .collect::<Vec<_>>();
    simplify_predicate_with_solver(
        definition,
        &internalize(source),
        &known,
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("predicate should simplify")
}

/// `wrap`'s only equation `wrap(X) = mk(X /Int 0) requires X ==Int 0` reduces an application
/// only where its `requires` holds. `value-production` makes an application that no equation
/// reduces a value, so where the `requires` is false the application's definedness is that of
/// its argument: `wrap(1)` is defined on every valuation, `wrap(X)` wherever the path condition
/// refutes `X ==Int 0`, and `wrap(u())` there exactly when `u()` is. Without such a refutation
/// `wrap(X)` keeps its obligation, `wrap(0)` is still undefined (its equation applies and
/// divides by zero), and an unmarked head keeps the obligation of `wrap(1)`.
#[test]
fn a_value_production_application_whose_reaching_equations_are_refuted_is_defined() {
    let definition = conditional_value_production();
    let ceil = |argument: &str| format!(r"\ceil{{SortS{{}}, SortS{{}}}}(wrap{{}}({argument}))");
    let refuted = |argument: &str| {
        format!(
            r#"\equals{{SortBool{{}}, SortS{{}}}}(eqInt{{}}({argument}, \dv{{SortInt{{}}}}("0")), \dv{{SortBool{{}}}}("false"))"#
        )
    };
    let one = r#"\dv{SortInt{}}("1")"#;
    assert_eq!(
        simplified_predicate_under(&definition, &ceil(one), &[]),
        Predicate::True
    );
    assert_eq!(
        simplified_predicate_under(
            &definition,
            &ceil("X:SortInt{}"),
            &[&refuted("X:SortInt{}")]
        ),
        Predicate::True
    );
    assert_eq!(
        simplified_predicate_under(&definition, &ceil("u{}()"), &[&refuted("u{}()")]),
        Predicate::Ceil(internal_term(&definition, "u{}()"))
    );
    assert_eq!(
        simplified_predicate_under(&definition, &ceil("X:SortInt{}"), &[]),
        Predicate::Ceil(internal_term(&definition, "wrap{}(X:SortInt{})"))
    );
    assert_eq!(
        simplified_predicate_under(&definition, &ceil(r#"\dv{SortInt{}}("0")"#), &[]),
        Predicate::False
    );
    let unmarked = internalize(SOURCE).expect("an unmarked anywhere head should internalize");
    assert_eq!(
        simplified_predicate_under(&unmarked, &ceil(one), &[]),
        Predicate::Ceil(internal_term(&unmarked, &format!("wrap{{}}({one})")))
    );
}

/// Value productions `h` and `w`, with `h(3, Z) = h(1, Z)` (so `h(3, Z)` and `h(1, Z)` denote one
/// value) and an equation headed by `w` whose left-hand side is `w(h({pattern}, 0))`, with the
/// condition `{requires}` and the right-hand side `mk({argument} /Int 0)`.
const NON_NORMAL_PATTERN: &str = r#"[]
    module MAIN
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
            [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
        hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
            [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
        sort SortH{} []
        sort SortS{} []
        symbol mk{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol h{}(SortInt{}, SortInt{}) : SortH{} [anywhere{}(), function{}(), value-production{}()]
        symbol w{}(SortH{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]
        axiom{R} \implies{R}(
            \and{R}(
                \top{R}(),
                \and{R}(
                    \in{SortInt{}, R}(X0:SortInt{}, \dv{SortInt{}}("3")),
                    \and{R}(\in{SortInt{}, R}(X1:SortInt{}, VarZ:SortInt{}), \top{R}())
                )
            ),
            \equals{SortH{}, R}(
                h{}(X0:SortInt{}, X1:SortInt{}),
                \and{SortH{}}(h{}(\dv{SortInt{}}("1"), VarZ:SortInt{}), \top{SortH{}}())
            )
        ) [anywhere{}()]
        axiom{R} \implies{R}(
            \and{R}(
                {requires},
                \and{R}(
                    \in{SortH{}, R}(X0:SortH{}, h{}({pattern}, \dv{SortInt{}}("0"))),
                    \top{R}()
                )
            ),
            \equals{SortS{}, R}(
                w{}(X0:SortH{}),
                \and{SortS{}}(mk{}(divInt{}({argument}, \dv{SortInt{}}("0"))), \top{SortS{}}())
            )
        ) [anywhere{}()]
    endmodule []"#;

fn non_normal_pattern(pattern: &str, requires: &str, argument: &str) -> BackendDefinition {
    internalize(
        &NON_NORMAL_PATTERN
            .replace("{pattern}", pattern)
            .replace("{requires}", requires)
            .replace("{argument}", argument),
    )
    .expect("the non-normal pattern definition should internalize")
}

fn ceil_w_h(first: &str, second: &str) -> String {
    format!(r"\ceil{{SortS{{}}, SortS{{}}}}(w{{}}(h{{}}({first}, {second})))")
}

/// `\ceil(w(h(1, 0)))` and `\ceil(w(h(3, 0)))` under `definition`: both denote
/// `\ceil(w(h(1, 0)))`, since `h(3, 0) = h(1, 0)`, and neither may simplify to `\top` when the
/// definition makes `w(h(3, 0))` undefined.
fn assert_w_h_keeps_its_obligation(definition: &BackendDefinition) {
    let zero = r#"\dv{SortInt{}}("0")"#;
    for first in [r#"\dv{SortInt{}}("1")"#, r#"\dv{SortInt{}}("3")"#] {
        let query = ceil_w_h(first, zero);
        assert_eq!(
            simplified_predicate_under(definition, &query, &[]),
            Predicate::Ceil(internal_term(
                definition,
                r#"w{}(h{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0")))"#
            )),
            "{query}"
        );
    }
}

/// `w(h(3, 0)) = mk(1 /Int 0)` makes `w(h(3, 0))` undefined, and `h(3, 0) = h(1, 0)` makes
/// `w(h(1, 0))` the same value, so `\ceil(w(h(1, 0)))` is `\bottom`, and so is the instance
/// `Y = 0` of `\ceil(w(h(1, Y)))`. The equation's left-hand side does not match `w(h(1, 0))` and
/// does not unify with `w(h(1, Y))` as terms, but its argument `h(3, 0)` is not a normal form:
/// that `h(3, 0)` and `h(1, 0)` differ as terms does not make them different values. So neither
/// the failed match (the simplifier's normal-form certificate, on the ground application) nor
/// the failed unification (instance normality, on the symbolic one) shows that the equation
/// misses them, and both keep their obligation.
#[test]
fn an_equation_whose_pattern_argument_is_reducible_reaches_the_values_it_denotes() {
    let definition = non_normal_pattern(
        r#"\dv{SortInt{}}("3")"#,
        r"\top{R}()",
        r#"\dv{SortInt{}}("1")"#,
    );
    assert_w_h_keeps_its_obligation(&definition);
    let symbolic = ceil_w_h(r#"\dv{SortInt{}}("1")"#, "Y:SortInt{}");
    assert_eq!(
        simplified_predicate_under(&definition, &symbolic, &[]),
        Predicate::Ceil(internal_term(
            &definition,
            r#"w{}(h{}(\dv{SortInt{}}("1"), Y:SortInt{}))"#
        )),
        "{symbolic}"
    );
}

/// `w(h(X, 0)) = mk(X /Int 0) requires X ==Int 3` makes `w(h(3, 0))` undefined, and
/// `h(3, 0) = h(1, 0)` makes `w(h(1, 0))` the same value. Matching `w(h(X, 0))` against
/// `w(h(1, 0))` succeeds only at `X = 1`, where the `requires` is false, but that match is not the
/// only valuation of the left-hand side denoting `w(h(1, 0))`: `h(X, 0)` is not normal on every
/// instance, and at `X = 3` the `requires` holds. So the refuted `requires` does not discharge
/// the obligation.
#[test]
fn a_refuted_requires_does_not_discharge_definedness_through_a_reducible_pattern_argument() {
    let definition = non_normal_pattern(
        "VarX:SortInt{}",
        r#"\equals{SortBool{}, R}(eqInt{}(VarX:SortInt{}, \dv{SortInt{}}("3")), \dv{SortBool{}}("true"))"#,
        "VarX:SortInt{}",
    );
    assert_w_h_keeps_its_obligation(&definition);
}

/// The anywhere equation `{head}(X0) = {right}` with `X0 \in {pattern}`, of argument sort
/// `{argument}` and result sort `{result}`.
fn anywhere_equation(
    head: &str,
    argument: &str,
    result: &str,
    pattern: &str,
    right: &str,
) -> String {
    format!(
        r"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{{argument}, R}}(X0:{argument}, {pattern}), \top{{R}}())),
            \equals{{{result}, R}}({head}{{}}(X0:{argument}), \and{{{result}}}({right}, \top{{{result}}}()))
        ) [anywhere{{}}()]"
    )
}

fn subsort(sub: &str, sup: &str) -> String {
    format!(
        r"axiom{{R}} \exists{{R}}(Value:{sup}, \equals{{{sup}, R}}(Value:{sup}, inj{{{sub}, {sup}}}(From:{sub}))) [subsort{{{sub}, {sup}}}()]"
    )
}

fn assert_ceil_kept(definition: &BackendDefinition, term: &str, sort: &str, kept: &str) {
    let query = format!(r"\ceil{{{sort}, {sort}}}({term})");
    assert_eq!(
        simplified_predicate_under(definition, &query, &[]),
        Predicate::Ceil(internal_term(definition, kept)),
        "{query}"
    );
}

/// `f(f(inj{K,F}(k(X)))) = c`: deciding whether the equation's argument `f(inj{K,F}(k(X)))` is
/// normal scans the equation itself against that argument, which asks the same question of the
/// same term. The decision must end, and does: the argument is normal (the equation needs an
/// `f` application inside `f`, and an instance of the argument has an injection there).
///
/// `\ceil(f(inj{K,F}(k(c))))` is `\top` by the axioms (an instance of the equation's argument is
/// an `f` application, never the injection `inj{K,F}(k(c))`, so no equation reaches the value
/// production's application), but the obligation is kept: the syntactic unification test reads
/// the equation's `f(…)` argument up to equations, which leaves its root open. That is a sound
/// loss of precision; this test pins that the decision ends with a sound answer.
#[test]
fn a_self_nested_left_hand_side_is_decided_without_unbounded_recursion() {
    let source = format!(
        r#"[]
    module MAIN
        sort SortK{{}} []
        sort SortF{{}} []
        symbol inj{{From, To}}(From) : To [sortInjection{{}}()]
        {}
        symbol c{{}}() : SortF{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
        symbol k{{}}(SortF{{}}) : SortK{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
        symbol f{{}}(SortF{{}}) : SortF{{}} [anywhere{{}}(), function{{}}(), value-production{{}}()]
        {}
    endmodule []"#,
        subsort("SortK{}", "SortF{}"),
        anywhere_equation(
            "f",
            "SortF{}",
            "SortF{}",
            "f{}(inj{SortK{}, SortF{}}(k{}(VarX:SortF{})))",
            "c{}()",
        ),
    );
    let definition = internalize(&source).expect("the self-nested definition should internalize");
    let term = "f{}(inj{SortK{}, SortF{}}(k{}(c{}())))";
    assert_ceil_kept(&definition, term, "SortF{}", term);
}
