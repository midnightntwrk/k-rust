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

/// Integers, `mk` and `w : H -> S` (a value production), for the narrowing probes below; each
/// adds its sorts, symbols and equations in place of `{rest}`.
const NARROWING: &str = r#"[]
    module MAIN
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
            [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
        sort SortH{} []
        sort SortS{} []
        symbol inj{From, To}(From) : To [sortInjection{}()]
        symbol mk{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol w{}(SortH{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]
        {rest}
    endmodule []"#;

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

/// `w(… ) = mk(1 /Int 0)` with the given left-hand side argument: every instance is undefined.
fn undefined_w(pattern: &str) -> String {
    anywhere_equation(
        "w",
        "SortH{}",
        "SortS{}",
        pattern,
        r#"mk{}(divInt{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0")))"#,
    )
}

fn subsort(sub: &str, sup: &str) -> String {
    format!(
        r"axiom{{R}} \exists{{R}}(Value:{sup}, \equals{{{sup}, R}}(Value:{sup}, inj{{{sub}, {sup}}}(From:{sub}))) [subsort{{{sub}, {sup}}}()]"
    )
}

fn narrowing_definition(rest: &[String]) -> BackendDefinition {
    internalize(&NARROWING.replace("{rest}", &rest.join("\n        ")))
        .expect("the narrowing definition should internalize")
}

fn assert_ceil_kept(definition: &BackendDefinition, term: &str, sort: &str, kept: &str) {
    let query = format!(r"\ceil{{{sort}, {sort}}}({term})");
    assert_eq!(
        simplified_predicate_under(definition, &query, &[]),
        Predicate::Ceil(internal_term(definition, kept)),
        "{query}"
    );
}

/// Sorts `B < A < T`, `h(inj{A,T}(X:A)) = k(X)` and `w(h(inj{B,T}(b0))) = mk(1 /Int 0)`. The
/// subsort axioms make `inj{B,T}(b0)` the value `inj{A,T}(inj{B,A}(b0))`, an instance of the
/// `h` equation's argument at `X = inj{B,A}(b0)`. So `h(inj{B,T}(b0)) = k(inj{B,A}(b0))`, and
/// `w(k(inj{B,A}(b0)))` is the undefined `w(h(inj{B,T}(b0)))`: neither `\ceil` may simplify to
/// `\top`. The right-hand side `k(X)` is a reduct of `h(inj{B,T}(b0))` although the equation's
/// injection source `A` lies above the term's `B`.
#[test]
fn narrowing_reads_an_injection_from_a_lower_sort_as_one_from_the_pattern_sort() {
    let definition = narrowing_definition(&[
        "sort SortB{} []".into(),
        "sort SortA{} []".into(),
        "sort SortT{} []".into(),
        subsort("SortB{}", "SortA{}"),
        subsort("SortA{}", "SortT{}"),
        subsort("SortB{}", "SortT{}"),
        "symbol b0{}() : SortB{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol k{}(SortA{}) : SortH{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol h{}(SortT{}) : SortH{} [anywhere{}(), function{}(), value-production{}()]".into(),
        anywhere_equation(
            "h",
            "SortT{}",
            "SortH{}",
            "inj{SortA{}, SortT{}}(VarX:SortA{})",
            "k{}(VarX:SortA{})",
        ),
        undefined_w("h{}(inj{SortB{}, SortT{}}(b0{}()))"),
    ]);
    let kept = "w{}(k{}(inj{SortB{}, SortA{}}(b0{}())))";
    for term in [kept, "w{}(h{}(inj{SortB{}, SortT{}}(b0{}())))"] {
        assert_ceil_kept(&definition, term, "SortS{}", kept);
    }
}

/// Sorts `C < A < T` and `C < B < T`, with `A` and `B` unrelated; `h(inj{A,T}(X:A)) = k(X)`,
/// `g() = inj{C,B}(c0)` and `w(h(inj{B,T}(g()))) = mk(1 /Int 0)`. Injections compose, so
/// `inj{B,T}(g()) = inj{C,T}(c0) = inj{A,T}(inj{C,A}(c0))`: `h(inj{B,T}(g())) = k(inj{C,A}(c0))`,
/// and `w(k(inj{C,A}(c0)))` is undefined. The `h` equation's injection from `A` reaches the
/// injection from the unrelated `B` through the reduct of its operand, an injection from the
/// common subsort `C`.
#[test]
fn narrowing_reads_an_injection_from_an_unrelated_sort_through_a_common_subsort() {
    let definition = narrowing_definition(&[
        "sort SortC{} []".into(),
        "sort SortA{} []".into(),
        "sort SortB{} []".into(),
        "sort SortT{} []".into(),
        subsort("SortC{}", "SortA{}"),
        subsort("SortC{}", "SortB{}"),
        subsort("SortA{}", "SortT{}"),
        subsort("SortB{}", "SortT{}"),
        subsort("SortC{}", "SortT{}"),
        "symbol c0{}() : SortC{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol k{}(SortA{}) : SortH{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol g{}() : SortB{} [anywhere{}(), function{}(), value-production{}()]".into(),
        "symbol h{}(SortT{}) : SortH{} [anywhere{}(), function{}(), value-production{}()]".into(),
        r"axiom{R} \implies{R}(
            \and{R}(\top{R}(), \top{R}()),
            \equals{SortB{}, R}(g{}(), \and{SortB{}}(inj{SortC{}, SortB{}}(c0{}()), \top{SortB{}}()))
        ) [anywhere{}()]"
            .into(),
        anywhere_equation(
            "h",
            "SortT{}",
            "SortH{}",
            "inj{SortA{}, SortT{}}(VarX:SortA{})",
            "k{}(VarX:SortA{})",
        ),
        undefined_w("h{}(inj{SortB{}, SortT{}}(g{}()))"),
    ]);
    let kept = "w{}(k{}(inj{SortC{}, SortA{}}(c0{}())))";
    assert_ceil_kept(&definition, kept, "SortS{}", kept);
}

/// `g(5) = f(0)`, `h(g(X)) = k2(X)` and `w(h(f(0))) = mk(1 /Int 0)`. Then
/// `h(f(0)) = h(g(5)) = k2(5)`, so `w(k2(5))` is the undefined `w(h(f(0)))`. The `h` equation's
/// argument `g(X)` is not normal on every instance, so that `g(X)` and `f(0)` differ as terms
/// does not keep `k2(X)` from being a reduct of `h(f(0))`.
#[test]
fn narrowing_reads_a_reducible_left_hand_side_argument_up_to_its_values() {
    let int_to = |head: &str, sort: &str, attributes: &str| {
        format!("symbol {head}{{}}(SortInt{{}}) : {sort} [{attributes}]")
    };
    let value_production = "anywhere{}(), function{}(), value-production{}()";
    let definition = narrowing_definition(&[
        "sort SortG{} []".into(),
        int_to("f", "SortG{}", value_production),
        int_to("g", "SortG{}", value_production),
        "symbol h{}(SortG{}) : SortH{} [anywhere{}(), function{}(), value-production{}()]".into(),
        int_to(
            "k2",
            "SortH{}",
            "constructor{}(), functional{}(), injective{}()",
        ),
        anywhere_equation(
            "g",
            "SortInt{}",
            "SortG{}",
            r#"\dv{SortInt{}}("5")"#,
            r#"f{}(\dv{SortInt{}}("0"))"#,
        ),
        anywhere_equation(
            "h",
            "SortG{}",
            "SortH{}",
            "g{}(VarX:SortInt{})",
            "k2{}(VarX:SortInt{})",
        ),
        undefined_w(r#"h{}(f{}(\dv{SortInt{}}("0")))"#),
    ]);
    let kept = r#"w{}(k2{}(\dv{SortInt{}}("5")))"#;
    assert_ceil_kept(&definition, kept, "SortS{}", kept);
}

/// `g(8) = g(7)`, `h(g(X)) = k2(X)` and `w(h(g(7))) = mk(1 /Int 0)`, with `k2` a value
/// production that no equation rewrites. Then `k2(8) = h(g(8)) = h(g(7))`, so `w(k2(8))` is
/// undefined. Narrowing `h(g(X))` against `h(g(7))` succeeds at `X = 7` only, but `g(X)` is not
/// normal on every instance: at `X = 8` its value is `g(7)` too, so `k2(8)` is a reduct of
/// `h(g(7))` as well, which the binding `X = 7` alone does not cover.
#[test]
fn narrowing_binds_no_variable_through_a_reducible_left_hand_side_argument() {
    let int_to = |head: &str, sort: &str| {
        format!(
            "symbol {head}{{}}(SortInt{{}}) : {sort} [anywhere{{}}(), function{{}}(), value-production{{}}()]"
        )
    };
    let definition = narrowing_definition(&[
        "sort SortG{} []".into(),
        int_to("g", "SortG{}"),
        "symbol h{}(SortG{}) : SortH{} [anywhere{}(), function{}(), value-production{}()]".into(),
        int_to("k2", "SortH{}"),
        anywhere_equation(
            "g",
            "SortInt{}",
            "SortG{}",
            r#"\dv{SortInt{}}("8")"#,
            r#"g{}(\dv{SortInt{}}("7"))"#,
        ),
        anywhere_equation(
            "h",
            "SortG{}",
            "SortH{}",
            "g{}(VarX:SortInt{})",
            "k2{}(VarX:SortInt{})",
        ),
        undefined_w(r#"h{}(g{}(\dv{SortInt{}}("7")))"#),
    ]);
    let kept = r#"w{}(k2{}(\dv{SortInt{}}("8")))"#;
    assert_ceil_kept(&definition, kept, "SortS{}", kept);
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

/// The anywhere equation `{head}(X0, X1) = {right}` with `X0 \in {first}` and `X1 \in {second}`,
/// of argument sorts `{sorts}` and result sort `{result}`.
fn binary_anywhere_equation(
    head: &str,
    sorts: (&str, &str),
    result: &str,
    (first, second): (&str, &str),
    right: &str,
) -> String {
    let (first_sort, second_sort) = sorts;
    format!(
        r"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{{first_sort}, R}}(X0:{first_sort}, {first}), \and{{R}}(\in{{{second_sort}, R}}(X1:{second_sort}, {second}), \top{{R}}()))),
            \equals{{{result}, R}}({head}{{}}(X0:{first_sort}, X1:{second_sort}), \and{{{result}}}({right}, \top{{{result}}}()))
        ) [anywhere{{}}()]"
    )
}

/// `g : Int -> G` and `f : G x Int -> S` value productions, `c1, c2, c3 : G` constructors, the
/// equation `g(5) = c1`, and the `f` equations `{equations}`.
fn overlap_definition(equations: &[(&str, &str)]) -> BackendDefinition {
    let mut rest = vec![
        "sort SortG{} []".to_string(),
        "symbol c1{}() : SortG{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol c2{}() : SortG{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol c3{}() : SortG{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol g{}(SortInt{}) : SortG{} [anywhere{}(), function{}(), value-production{}()]".into(),
        "symbol f{}(SortG{}, SortInt{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]"
            .into(),
        anywhere_equation(
            "g",
            "SortInt{}",
            "SortG{}",
            r#"\dv{SortInt{}}("5")"#,
            "c1{}()",
        ),
    ];
    rest.extend(equations.iter().map(|(first, right)| {
        binary_anywhere_equation(
            "f",
            ("SortG{}", "SortInt{}"),
            "SortS{}",
            (first, "VarZ:SortInt{}"),
            right,
        )
    }));
    narrowing_definition(&rest)
}

const UNDEFINED_MK: &str = r#"mk{}(divInt{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0")))"#;

/// `g(5) = c1`, `f(c1, Z) = f(c2, Z)` and `f(g(X), Z) = mk(1 /Int 0)` (review 3, F1). Then
/// `f(c2, Y) = f(c1, Y) = f(g(5), Y) = mk(1 /Int 0)`, which is undefined. No reduct of `g(X)`
/// is `c2`, so the `f(g(X), Z)` equation's argument misses `f(c2, Y)`'s; the instance
/// `f(g(5), Z)` reaches it only through a step below the root followed by a root step of the
/// other equation. So `\ceil(f(c2, Y))` keeps its obligation, while `f(c3, Y)`, which no
/// reduct of an instance of either left-hand side is, is defined.
#[test]
fn a_root_step_by_another_equation_leads_an_overlapped_instance_back_to_the_application() {
    let definition = overlap_definition(&[
        ("c1{}()", "f{}(c2{}(), VarZ:SortInt{})"),
        ("g{}(VarX:SortInt{})", UNDEFINED_MK),
    ]);
    let kept = "f{}(c2{}(), Y:SortInt{})";
    assert_ceil_kept(&definition, kept, "SortS{}", kept);
    assert_eq!(
        simplified_predicate_under(
            &definition,
            r"\ceil{SortS{}, SortS{}}(f{}(c3{}(), Y:SortInt{}))",
            &[]
        ),
        Predicate::True
    );
}

/// The ground instance of [`a_root_step_by_another_equation_leads_an_overlapped_instance_back_to_the_application`]:
/// every equation fails to match `f(c2, 0)`, but those failures do not certify it as a value.
#[test]
fn a_root_step_by_another_equation_leads_an_overlapped_ground_instance_back_to_the_application() {
    let definition = overlap_definition(&[
        ("c1{}()", "f{}(c2{}(), VarZ:SortInt{})"),
        ("g{}(VarX:SortInt{})", UNDEFINED_MK),
    ]);
    let kept = r#"f{}(c2{}(), \dv{SortInt{}}("0"))"#;
    assert_ceil_kept(&definition, kept, "SortS{}", kept);
}

/// `g(5) = c1`, `f(g(X), Z) = f(c2, Z)` and `f(c1, Z) = mk(1 /Int 0)`. Then
/// `f(c2, Y) = f(g(5), Y) = f(c1, Y)`, undefined. `f(c2, Y)` is reached from `f(g(5), Y)` only
/// through the first equation's own root step, but `f(g(5), Y)` has a second step (`g(5) = c1`)
/// whose normal form is not `f(c2, Y)`: an equation's own root step counts at an instance that
/// another step also rewrites.
#[test]
fn an_equations_own_root_step_from_an_overlapped_instance_reaches_its_normal_forms() {
    let definition = overlap_definition(&[
        ("g{}(VarX:SortInt{})", "f{}(c2{}(), VarZ:SortInt{})"),
        ("c1{}()", UNDEFINED_MK),
    ]);
    for kept in [
        "f{}(c2{}(), Y:SortInt{})",
        r#"f{}(c2{}(), \dv{SortInt{}}("0"))"#,
    ] {
        assert_ceil_kept(&definition, kept, "SortS{}", kept);
    }
    assert_eq!(
        simplified_predicate_under(
            &definition,
            r"\ceil{SortS{}, SortS{}}(f{}(c3{}(), Y:SortInt{}))",
            &[]
        ),
        Predicate::True
    );
}

/// `f(X, Z) = mk(X /Int 0) requires X ==Int 3` and `f(3, Z) = f(1, Z)` overlap at the root
/// (review 3, F2): `f(1, Y) = f(3, Y) = mk(3 /Int 0)`, undefined. Matching the conditional
/// equation against `f(1, Y)` succeeds only at `X = 1`, where its `requires` is false, but the
/// instance `f(3, Z)` of its left-hand side, which the other equation also rewrites, reaches
/// `f(1, Y)`: the refuted `requires` discharges nothing. `f(2, Y)` is reached by neither.
#[test]
fn a_refuted_requires_does_not_discharge_definedness_under_a_root_overlap() {
    let int = |value: &str| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
    let definition = narrowing_definition(&[
        r#"hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]"#.into(),
        r#"hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]"#.into(),
        "symbol f{}(SortInt{}, SortInt{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]".into(),
        binary_anywhere_equation(
            "f",
            ("SortInt{}", "SortInt{}"),
            "SortS{}",
            (&int("3"), "VarZ:SortInt{}"),
            &format!("f{{}}({}, VarZ:SortInt{{}})", int("1")),
        ),
        r#"axiom{R} \implies{R}(
            \and{R}(\equals{SortBool{}, R}(eqInt{}(VarX:SortInt{}, \dv{SortInt{}}("3")), \dv{SortBool{}}("true")),
              \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \and{R}(\in{SortInt{}, R}(X1:SortInt{}, VarZ:SortInt{}), \top{R}()))),
            \equals{SortS{}, R}(f{}(X0:SortInt{}, X1:SortInt{}), \and{SortS{}}(mk{}(divInt{}(VarX:SortInt{}, \dv{SortInt{}}("0"))), \top{SortS{}}()))
        ) [anywhere{}()]"#
            .into(),
    ]);
    let kept = format!("f{{}}({}, Y:SortInt{{}})", int("1"));
    assert_ceil_kept(&definition, &kept, "SortS{}", &kept);
    assert_eq!(
        simplified_predicate_under(
            &definition,
            &format!(
                r"\ceil{{SortS{{}}, SortS{{}}}}(f{{}}({}, Y:SortInt{{}}))",
                int("2")
            ),
            &[]
        ),
        Predicate::True
    );
}
