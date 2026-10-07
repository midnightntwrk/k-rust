use std::fmt::Write as _;

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

/// `e, d : Int -> A`, `k : Int -> T` and `c : T` constructors, `f : A x T -> S` a value
/// production with `f(e(Y), W) = f(d(Y), c)`, `f(V, k({second})) = f(d({second}), c)` and
/// `{last}`. The first two overlap at the root, at `f(e(Y), k({second}))` with `Y` and
/// `{second}` independent: `f(e(1), k(3))` has the normal forms of `f(d(1), c)` and of
/// `f(d(3), c)`.
fn root_overlap_definition(second: &str, last: String) -> BackendDefinition {
    narrowing_definition(&[
        r#"hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]"#.to_string(),
        r#"hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]"#.into(),
        "sort SortA{} []".into(),
        "sort SortT{} []".into(),
        "symbol e{}(SortInt{}) : SortA{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol d{}(SortInt{}) : SortA{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol k{}(SortInt{}) : SortT{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol c{}() : SortT{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol f{}(SortA{}, SortT{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]".into(),
        binary_anywhere_equation(
            "f",
            ("SortA{}", "SortT{}"),
            "SortS{}",
            ("e{}(VarY:SortInt{})", "VarW:SortT{}"),
            "f{}(d{}(VarY:SortInt{}), c{}())",
        ),
        binary_anywhere_equation(
            "f",
            ("SortA{}", "SortT{}"),
            "SortS{}",
            ("VarV:SortA{}", &format!("k{{}}({second}:SortInt{{}})")),
            &format!("f{{}}(d{{}}({second}:SortInt{{}}), c{{}}())"),
        ),
        last,
    ])
}

const ROOT_OVERLAP_SUBJECT: &str = r#"f{}(d{}(\dv{SortInt{}}("1")), c{}())"#;

/// [`root_overlap_definition`] with `f(d(X), c) = mk(X /Int 0) requires X ==Int 3` (review 4,
/// F1): `f(d(1), c) = f(e(1), k(3)) = f(d(3), c) = mk(3 /Int 0)`, undefined. The `requires`
/// is false at the only match of `f(d(1), c)`, but the root overlap reaches `f(d(1), c)`, so
/// it discharges nothing, whether the second equation's variable is named like the first's
/// (`VarY`) or not (`VarU`): the axioms are the same up to renaming their variables.
#[test]
fn a_root_overlap_is_read_apart_from_the_names_its_equations_share_under_a_refuted_requires() {
    for second in ["VarY", "VarU"] {
        let definition = root_overlap_definition(
            second,
            r#"axiom{R} \implies{R}(
            \and{R}(\equals{SortBool{}, R}(eqInt{}(VarX:SortInt{}, \dv{SortInt{}}("3")), \dv{SortBool{}}("true")),
              \and{R}(\in{SortA{}, R}(X0:SortA{}, d{}(VarX:SortInt{})), \and{R}(\in{SortT{}, R}(X1:SortT{}, c{}()), \top{R}()))),
            \equals{SortS{}, R}(f{}(X0:SortA{}, X1:SortT{}), \and{SortS{}}(mk{}(divInt{}(VarX:SortInt{}, \dv{SortInt{}}("0"))), \top{SortS{}}()))
        ) [anywhere{}()]"#
                .into(),
        );
        assert_ceil_kept(
            &definition,
            ROOT_OVERLAP_SUBJECT,
            "SortS{}",
            ROOT_OVERLAP_SUBJECT,
        );
    }
}

/// [`root_overlap_definition`] with `f(d(3), c) = mk(1 /Int 0)`: `f(d(1), c)` is undefined by
/// the same conversion and is not a value, whatever the second equation's variable is named.
#[test]
fn a_root_overlap_is_read_apart_from_the_names_its_equations_share() {
    for second in ["VarY", "VarU"] {
        let definition = root_overlap_definition(
            second,
            binary_anywhere_equation(
                "f",
                ("SortA{}", "SortT{}"),
                "SortS{}",
                (r#"d{}(\dv{SortInt{}}("3"))"#, "c{}()"),
                UNDEFINED_MK,
            ),
        );
        assert_ceil_kept(
            &definition,
            ROOT_OVERLAP_SUBJECT,
            "SortS{}",
            ROOT_OVERLAP_SUBJECT,
        );
    }
}

/// One sort `A`: constructors `k, s, m, m2 : A -> A` and `c, d : A`; value productions `p, h :
/// A x A -> A`, `q : A x A x A -> A`, `v : A -> A` and `f : A -> S`; the equations `{rest}`,
/// `q({first}, X, X) = c` and `f(p(A, s(Z))) = mk(1 /Int 0)`. With `{first}` = `c`, instance
/// normality refutes `q(Z, s(Z), s(d))` (`Z = c`, then `s(c)` against `s(d)`) but not
/// `q(Z1, s(Z2), s(d))`; with `k(c)`, likewise `q(k(Z), s(Z), s(d))`.
fn chained_reducts_definition(first: &str, rest: &[String]) -> BackendDefinition {
    let mut equations = vec![
        "sort SortA{} []".to_string(),
        "symbol k{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol s{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol m{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol m2{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol c{}() : SortA{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol d{}() : SortA{} [constructor{}(), functional{}(), injective{}()]".into(),
        "symbol p{}(SortA{}, SortA{}) : SortA{} [anywhere{}(), function{}(), value-production{}()]".into(),
        "symbol h{}(SortA{}, SortA{}) : SortA{} [anywhere{}(), function{}(), value-production{}()]".into(),
        "symbol q{}(SortA{}, SortA{}, SortA{}) : SortA{} [anywhere{}(), function{}(), value-production{}()]".into(),
        "symbol v{}(SortA{}) : SortA{} [anywhere{}(), function{}(), value-production{}()]".into(),
        "symbol f{}(SortA{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]".into(),
        r#"axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortA{}, R}(X0:SortA{}, {first}), \and{R}(\in{SortA{}, R}(X1:SortA{}, VarX:SortA{}), \and{R}(\in{SortA{}, R}(X2:SortA{}, VarX:SortA{}), \top{R}())))),
            \equals{SortA{}, R}(q{}(X0:SortA{}, X1:SortA{}, X2:SortA{}), \and{SortA{}}(c{}(), \top{SortA{}}()))
        ) [anywhere{}()]"#
            .replace("{first}", first),
        anywhere_equation(
            "f",
            "SortA{}",
            "SortS{}",
            "p{}(VarA:SortA{}, s{}(VarZ:SortA{}))",
            UNDEFINED_MK,
        ),
    ];
    equations.extend(rest.iter().cloned());
    narrowing_definition(&equations)
}

const CHAINED_SUBJECT: &str = "f{}(m{}(m2{}(c{}())))";

/// [`chained_reducts_definition`] with `q(c, X, X) = c`, `p(k(Y), V) = m(h(Y, V))` and `h(k({name}), V) =
/// m2(q({name}, V, s(d)))`. By the axioms `f(m(m2(c))) = f(m(m2(q(c, s(d), s(d))))) =
/// f(m(h(k(c), s(d)))) = f(p(k(k(c)), s(d))) = mk(1 /Int 0)`, undefined. Reading `f`'s
/// argument `p(A, s(Z))`, the `h` equation's step leaves its own variable unbound beside the `f`
/// equation's `Z`; named alike (`VarZ`), the two must still be read apart.
#[test]
fn a_reduct_keeps_a_variable_narrowing_leaves_unbound_apart_from_the_left_hand_sides() {
    for name in ["VarZ", "VarU"] {
        let definition = chained_reducts_definition(
            "c{}()",
            &[
                binary_anywhere_equation(
                    "p",
                    ("SortA{}", "SortA{}"),
                    "SortA{}",
                    ("k{}(VarY:SortA{})", "VarV:SortA{}"),
                    "m{}(h{}(VarY:SortA{}, VarV:SortA{}))",
                ),
                binary_anywhere_equation(
                    "h",
                    ("SortA{}", "SortA{}"),
                    "SortA{}",
                    (&format!("k{{}}({name}:SortA{{}})"), "VarV:SortA{}"),
                    &format!("m2{{}}(q{{}}({name}:SortA{{}}, VarV:SortA{{}}, s{{}}(d{{}}())))"),
                ),
            ],
        );
        assert_ceil_kept(&definition, CHAINED_SUBJECT, "SortS{}", CHAINED_SUBJECT);
    }
}

/// [`chained_reducts_definition`] with `q(k(c), X, X) = c`, `p(k(Y), V) = m(h(c, V))`, `h(v(X), V) =
/// m2(q(X, V, s(d)))` and `v(k({name})) = c`. `c` is the value of `v(k(c))`, so by the axioms
/// `f(m(m2(c))) = f(m(m2(q(k(c), s(d), s(d))))) = f(m(h(v(k(c)), s(d)))) = f(m(h(c, s(d)))) =
/// f(p(k(Y), s(d))) = mk(1 /Int 0)`, undefined. Reading `h(c, s(Z))` through the `v`
/// equation binds the `h` equation's `X` to `k({name})` with `{name}` unbound; named like the
/// `f` equation's `Z` (`VarZ`), the two must still be read apart.
#[test]
fn a_composed_reduct_keeps_a_variable_narrowing_leaves_unbound_apart_from_the_left_hand_sides() {
    for name in ["VarZ", "VarU"] {
        let definition = chained_reducts_definition(
            "k{}(c{}())",
            &[
                binary_anywhere_equation(
                    "p",
                    ("SortA{}", "SortA{}"),
                    "SortA{}",
                    ("k{}(VarY:SortA{})", "VarV:SortA{}"),
                    "m{}(h{}(c{}(), VarV:SortA{}))",
                ),
                binary_anywhere_equation(
                    "h",
                    ("SortA{}", "SortA{}"),
                    "SortA{}",
                    ("v{}(VarX:SortA{})", "VarV:SortA{}"),
                    "m2{}(q{}(VarX:SortA{}, VarV:SortA{}, s{}(d{}())))",
                ),
                anywhere_equation(
                    "v",
                    "SortA{}",
                    "SortA{}",
                    &format!("k{{}}({name}:SortA{{}})"),
                    "c{}()",
                ),
            ],
        );
        assert_ceil_kept(&definition, CHAINED_SUBJECT, "SortS{}", CHAINED_SUBJECT);
    }
}

const EQ_INT: [&str; 2] = [
    r#"hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]"#,
    r#"hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]"#,
];

/// `f(m(X), c) = mk(X /Int 0) requires X ==Int 3` (or `f(m(X)) = …` for a unary `f`), with `m`'s
/// argument and `f`'s other arguments given.
fn conditional_f_m(arguments: &str, sorts: &str) -> String {
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}(\equals{{SortBool{{}}, R}}(eqInt{{}}(VarX:SortInt{{}}, \dv{{SortInt{{}}}}("3")), \dv{{SortBool{{}}}}("true")), {arguments}),
            \equals{{SortS{{}}, R}}(f{{}}({sorts}), \and{{SortS{{}}}}(mk{{}}(divInt{{}}(VarX:SortInt{{}}, \dv{{SortInt{{}}}}("0"))), \top{{SortS{{}}}}()))
        ) [anywhere{{}}()]"#
    )
}

/// Review 5, F1. `n, k : A -> A`, `j : A x A -> A`, `m : Int -> A` and `c, d : A` constructors;
/// `q : A x A x A -> Int` and `f : A x A -> S` value productions; `q(c, n(n(c)), d) = 0`,
/// `f(V, k(Y)) = f(V, j(V, Y))`, `f(n(Y), k(W)) = mk(1 /Int 0)` and `f(n(n({name})), j(W, Y2)) =
/// f(m(q({name}, W, Y2)), c)`, and with `discharge` also `f(m(X), c) = mk(X /Int 0) requires
/// X ==Int 3`. By the axioms `f(m(0), c) = f(m(q(c, n(n(c)), d)), c) = f(n(n(c)), j(n(n(c)), d)) =
/// f(n(n(c)), k(d)) = mk(1 /Int 0)`, undefined. The overlap representative of the `f(n(Y), k(W))`
/// equation that reaches `f(m(q(Y', W', Y2)), c)` holds variables of three copies; stored apart,
/// they cover `f(m(q(c, n(n(c)), d)), c)`, whose `q` the first equation rewrites.
fn stored_names_definition(name: &str, discharge: bool) -> BackendDefinition {
    let mut rest = EQ_INT
        .iter()
        .map(|line| (*line).to_string())
        .collect::<Vec<_>>();
    rest.extend(
        [
            "sort SortA{} []",
            "symbol n{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]",
            "symbol k{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]",
            "symbol j{}(SortA{}, SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]",
            "symbol m{}(SortInt{}) : SortA{} [constructor{}(), functional{}(), injective{}()]",
            "symbol c{}() : SortA{} [constructor{}(), functional{}(), injective{}()]",
            "symbol d{}() : SortA{} [constructor{}(), functional{}(), injective{}()]",
            "symbol q{}(SortA{}, SortA{}, SortA{}) : SortInt{} [anywhere{}(), function{}(), value-production{}()]",
            "symbol f{}(SortA{}, SortA{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]",
        ]
        .map(String::from),
    );
    rest.push(
        r#"axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortA{}, R}(X0:SortA{}, c{}()), \and{R}(\in{SortA{}, R}(X1:SortA{}, n{}(n{}(c{}()))), \and{R}(\in{SortA{}, R}(X2:SortA{}, d{}()), \top{R}())))),
            \equals{SortInt{}, R}(q{}(X0:SortA{}, X1:SortA{}, X2:SortA{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))
        ) [anywhere{}()]"#
            .into(),
    );
    let f = |first: &str, second: &str, right: &str| {
        binary_anywhere_equation(
            "f",
            ("SortA{}", "SortA{}"),
            "SortS{}",
            (first, second),
            right,
        )
    };
    rest.push(f(
        "VarV:SortA{}",
        "k{}(VarY:SortA{})",
        "f{}(VarV:SortA{}, j{}(VarV:SortA{}, VarY:SortA{}))",
    ));
    rest.push(f("n{}(VarY:SortA{})", "k{}(VarW:SortA{})", UNDEFINED_MK));
    rest.push(f(
        &format!("n{{}}(n{{}}({name}:SortA{{}}))"),
        "j{}(VarW:SortA{}, VarY2:SortA{})",
        &format!("f{{}}(m{{}}(q{{}}({name}:SortA{{}}, VarW:SortA{{}}, VarY2:SortA{{}})), c{{}}())"),
    ));
    if discharge {
        rest.push(conditional_f_m(
            r"\and{R}(\in{SortA{}, R}(X0:SortA{}, m{}(VarX:SortInt{})), \and{R}(\in{SortA{}, R}(X1:SortA{}, c{}()), \top{R}()))",
            "X0:SortA{}, X1:SortA{}",
        ));
    }
    narrowing_definition(&rest)
}

/// Review 5, F1: a stored overlap representative keeps every variable it holds apart, whatever
/// the equations name them, with or without the conditional equation the discharge reads.
#[test]
fn a_stored_representative_keeps_apart_the_variables_of_every_copy_it_holds() {
    let subject = r#"f{}(m{}(\dv{SortInt{}}("0")), c{}())"#;
    for name in ["VarY", "VarU"] {
        for discharge in [false, true] {
            let definition = stored_names_definition(name, discharge);
            assert_ceil_kept(&definition, subject, "SortS{}", subject);
        }
    }
}

/// Review 5, F2. `n_i, s_i : A -> A` for `i < count`, `m : Int -> A` and `c1, c2 : A`
/// constructors; `v : A -> A`, `p : A x A -> A`, `r : A x A -> Int` and `f : A -> S` value
/// productions; `v(n_i(Z)) = s_i(Z)`, `p(s0(A), s0(B)) = m(r(A, B))`, `r(c1, c2) = 0` and
/// `f(p(v(W1), v(W2))) = mk(1 /Int 0)`, and with `discharge` also `f(m(X)) = mk(X /Int 0) requires
/// X ==Int 3`. By the axioms `f(m(0)) = f(m(r(c1, c2))) = f(p(s0(c1), s0(c2))) =
/// f(p(v(n0(c1)), v(n0(c2)))) = mk(1 /Int 0)`, undefined. With 70 `v` equations each `v(Wi)` has
/// more reducts than the representatives kept, and both fall back to every right-hand side `v`
/// reaches; read as one copy, the `s0(Z)` of the two positions would share `Z`.
fn bound_fallback_definition(count: usize, discharge: bool) -> BackendDefinition {
    let constructor = |name: &str, arguments: &str| {
        format!(
            "symbol {name}{{}}({arguments}) : SortA{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]"
        )
    };
    let mut rest = EQ_INT
        .iter()
        .map(|line| (*line).to_string())
        .collect::<Vec<_>>();
    rest.push("sort SortA{} []".into());
    rest.push(constructor("m", "SortInt{}"));
    rest.push(constructor("c1", ""));
    rest.push(constructor("c2", ""));
    for index in 0..count {
        rest.push(constructor(&format!("n{index}"), "SortA{}"));
        rest.push(constructor(&format!("s{index}"), "SortA{}"));
        rest.push(anywhere_equation(
            "v",
            "SortA{}",
            "SortA{}",
            &format!("n{index}{{}}(VarZ:SortA{{}})"),
            &format!("s{index}{{}}(VarZ:SortA{{}})"),
        ));
    }
    rest.extend(
        [
            "symbol v{}(SortA{}) : SortA{} [anywhere{}(), function{}(), value-production{}()]",
            "symbol p{}(SortA{}, SortA{}) : SortA{} [anywhere{}(), function{}(), value-production{}()]",
            "symbol r{}(SortA{}, SortA{}) : SortInt{} [anywhere{}(), function{}(), value-production{}()]",
            "symbol f{}(SortA{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]",
        ]
        .map(String::from),
    );
    rest.push(binary_anywhere_equation(
        "p",
        ("SortA{}", "SortA{}"),
        "SortA{}",
        ("s0{}(VarA:SortA{})", "s0{}(VarB:SortA{})"),
        "m{}(r{}(VarA:SortA{}, VarB:SortA{}))",
    ));
    rest.push(binary_anywhere_equation(
        "r",
        ("SortA{}", "SortA{}"),
        "SortInt{}",
        ("c1{}()", "c2{}()"),
        r#"\dv{SortInt{}}("0")"#,
    ));
    rest.push(anywhere_equation(
        "f",
        "SortA{}",
        "SortS{}",
        "p{}(v{}(VarW1:SortA{}), v{}(VarW2:SortA{}))",
        UNDEFINED_MK,
    ));
    if discharge {
        rest.push(conditional_f_m(
            r"\and{R}(\in{SortA{}, R}(X0:SortA{}, m{}(VarX:SortInt{})), \top{R}())",
            "X0:SortA{}",
        ));
    }
    narrowing_definition(&rest)
}

/// Review 5, F2: past the bound on representatives, each argument position reads the
/// right-hand sides it falls back to as fresh copies, so two positions do not share a variable.
#[test]
fn the_representatives_past_the_bound_are_fresh_copies_of_the_right_hand_sides() {
    let subject = r#"f{}(m{}(\dv{SortInt{}}("0")))"#;
    for count in [3, 70] {
        for discharge in [false, true] {
            let definition = bound_fallback_definition(count, discharge);
            assert_ceil_kept(&definition, subject, "SortS{}", subject);
        }
    }
}

/// `v(d) = c` and `v(d) = k(v(s(c)))` do not meet at `v(d)`: they identify `c` with
/// `k(v(s(c)))`, so `v(s(c))` is undefined (a constructor is functional, so for a value
/// `v(s(c))` the two sides would be distinct values), although no equation reaches it. Its
/// obligation, and that of `k(v(s(c)))`, stay.
#[test]
fn an_overlap_that_identifies_a_constructor_term_keeps_the_obligation_of_the_application_it_holds()
{
    let definition = internalize(
        r#"[]
        module MAIN
        sort SortA{} []
        symbol c{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol d{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol k{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol s{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol v{}(SortA{}) : SortA{} [anywhere{}(), function{}(), value-production{}()]
        axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortA{}, R}(X0:SortA{}, d{}()), \top{R}())), \equals{SortA{}, R}(v{}(X0:SortA{}), \and{SortA{}}(c{}(), \top{SortA{}}()))) [anywhere{}()]
        axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortA{}, R}(X0:SortA{}, d{}()), \top{R}())), \equals{SortA{}, R}(v{}(X0:SortA{}), \and{SortA{}}(k{}(v{}(s{}(c{}()))), \top{SortA{}}()))) [anywhere{}()]
        endmodule []"#,
    )
    .expect("the definition should internalize");
    for term in [r"v{}(s{}(c{}()))", r"k{}(v{}(s{}(c{}())))"] {
        assert_ceil_kept(&definition, term, "SortA{}", r"v{}(s{}(c{}()))");
    }
}

/// `c, d : A`, `k, s : A -> A` and `m : Int -> A` constructors; `e : A -> A` a total equation
/// head (`anywhere`, `total`), `g : A -> A` a value production and, where `{second}` uses it,
/// `sz : A -> Int` a total function; `g(d) = m(1 /Int 0)` and `g(d) = {second}`, and with
/// `conditional` also `g(m(I)) = c requires I ==Int 0`.
fn total_head_definition(second: &str, conditional: bool) -> BackendDefinition {
    let mut source = r#"[]
        module MAIN
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
            [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
        hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
            [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
        sort SortA{} []
        symbol c{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol d{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol k{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol s{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol m{}(SortInt{}) : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol e{}(SortA{}) : SortA{} [anywhere{}(), total{}()]
        symbol g{}(SortA{}) : SortA{} [anywhere{}(), function{}(), value-production{}()]
        {sz}
        axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortA{}, R}(X0:SortA{}, d{}()), \top{R}())), \equals{SortA{}, R}(g{}(X0:SortA{}), \and{SortA{}}(m{}(divInt{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0"))), \top{SortA{}}()))) [anywhere{}()]
        "#
    .replace(
        "{sz}",
        if second.contains("sz{}") {
            "symbol sz{}(SortA{}) : SortInt{} [function{}(), total{}()]"
        } else {
            ""
        },
    );
    writeln!(
        source,
        r"axiom{{R}} \implies{{R}}(\and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortA{{}}, R}}(X0:SortA{{}}, d{{}}()), \top{{R}}())), \equals{{SortA{{}}, R}}(g{{}}(X0:SortA{{}}), \and{{SortA{{}}}}({second}, \top{{SortA{{}}}}()))) [anywhere{{}}()]"
    )
    .unwrap();
    if conditional {
        source.push_str(
            r#"axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(eqInt{}(VarI:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \and{R}(\in{SortA{}, R}(X0:SortA{}, m{}(VarI:SortInt{})), \top{R}())), \equals{SortA{}, R}(g{}(X0:SortA{}), \and{SortA{}}(c{}(), \top{SortA{}}()))) [anywhere{}()]
            "#,
        );
    }
    source.push_str("endmodule []");
    internalize(&source).expect("the total-head definition should internalize")
}

/// The second right-hand sides of `g(d)` that hold `{held}` below total symbols only: a
/// constructor and a total equation head, a total equation head, a constructor and a total
/// function into another sort, and a constructor.
fn total_contexts(held: &str) -> [String; 4] {
    [
        format!("k{{}}(e{{}}({held}))"),
        format!("e{{}}({held})"),
        format!("m{{}}(sz{{}}({held}))"),
        format!("k{{}}({held})"),
    ]
}

/// Review 6, F1. `g(d) = m(1 /Int 0)` makes `g(d)` undefined, so `g(d) = C[g(m(1))]`, with
/// `C` built from constructors and total symbols only, makes `C[g(m(1))]` undefined. A total
/// symbol applied to defined arguments is defined, so `g(m(1))` is undefined. The conditional
/// `g(m(I)) = c requires I ==Int 0` is refuted at `I = 1`, which must not discharge
/// `\ceil(g(m(1)))`: the theory has models (`g(m(0)) = c`, `g(d)` and `g(m(1))` undefined),
/// in each of which the obligation is false.
#[test]
fn a_refuted_requires_does_not_discharge_an_application_an_overlap_holds_below_total_symbols() {
    let held = r#"g{}(m{}(\dv{SortInt{}}("1")))"#;
    for second in total_contexts(held) {
        let definition = total_head_definition(&second, true);
        assert_ceil_kept(&definition, held, "SortA{}", held);
    }
}

/// Review 6, F2: the same overlaps without a `requires`. `g(s(c))` is undefined in every model
/// for each total context, while `g(s(d))`, which no overlap holds, stays a value (the
/// `value-production` marker) where the context reads it apart.
#[test]
fn an_overlap_that_holds_an_application_below_total_symbols_keeps_its_obligation() {
    let held = "g{}(s{}(c{}()))";
    let apart = "g{}(s{}(d{}()))";
    for (index, second) in total_contexts(held).into_iter().enumerate() {
        let definition = total_head_definition(&second, false);
        assert_ceil_kept(&definition, held, "SortA{}", held);
        // With `sz`, `Int` terms can hold `A` terms below a total symbol, so the other
        // representative `m(1 /Int 0)`, whose argument is a function application the overlap
        // reading does not see through, may hold `g(s(d))`: a precision limit, not asserted.
        if index != 2 {
            assert_eq!(
                simplified_predicate_under(
                    &definition,
                    &format!(r"\ceil{{SortA{{}}, SortA{{}}}}({apart})"),
                    &[]
                ),
                Predicate::True,
                "{second}"
            );
        }
    }
}
