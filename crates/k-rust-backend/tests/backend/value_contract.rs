//! The regression probes of the value contract (`value-contract-design.md`, section 2.4): each
//! definition a review or critique of the per-query value analysis found, with the verdict of the
//! load-time critical-pair check (`k_rust_backend::confluence`) and the claims the backend keeps
//! or withholds under it.
//!
//! An application of a value production is defined wherever its arguments are only where the
//! definition's normal-form model is a model of it. Each probe below whose pair does not join
//! makes the application undefined in every model of its axioms; the check names the pair and
//! withdraws the head's claims, so `\ceil` of the application keeps its obligation. The probes
//! whose pairs join keep the claims the contract makes.

use k_rust_backend::{
    confluence::{CheckScope, UnjoinedReason, UnresolvedShape},
    definition::BackendDefinition,
    rule::Predicate,
    simplify::SimplificationOptions,
    smt::NoSolver,
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::unstopped::simplify_predicate_with_solver;

const PRELUDE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
    sort SortS{} []
    symbol mk{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
"#;

/// A definition: the prelude, then `declarations` and `axioms`, in module `MAIN`.
fn definition(declarations: &str, axioms: &[String]) -> BackendDefinition {
    let source = format!(
        "[] module MAIN {PRELUDE} {declarations} {} endmodule []",
        axioms.join("\n")
    );
    let syntax = parse_definition(&source).expect("the probe parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the probe internalizes")
}

/// The equation `head(X0, ..., Xn) = right`, each `Xi` bound to `patterns[i]` of sort
/// `sorts[i]`, with `requires` (a KORE predicate over the patterns' variables, or `\top`) and
/// the axiom attributes `attributes`.
fn equation(
    head: &str,
    sorts: &[&str],
    result: &str,
    patterns: &[&str],
    right: &str,
    requires: &str,
    attributes: &str,
) -> String {
    let memberships = sorts.iter().zip(patterns).enumerate().rev().fold(
        r"\top{R}()".to_owned(),
        |rest, (index, (sort, pattern))| {
            format!(r"\and{{R}}(\in{{{sort}, R}}(X{index}:{sort}, {pattern}), {rest})")
        },
    );
    let parameters = sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| format!("X{index}:{sort}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        r"axiom{{R}} \implies{{R}}(\and{{R}}({requires}, {memberships}), \equals{{{result}, R}}({head}{{}}({parameters}), \and{{{result}}}({right}, \top{{{result}}}()))) [{attributes}]"
    )
}

/// An unconditional `anywhere` equation.
fn anywhere(head: &str, sorts: &[&str], result: &str, patterns: &[&str], right: &str) -> String {
    equation(
        head,
        sorts,
        result,
        patterns,
        right,
        r"\top{R}()",
        "anywhere{}()",
    )
}

/// `variable ==Int value` as a `requires`.
fn int_equals(variable: &str, value: i64) -> String {
    format!(
        r#"\equals{{SortBool{{}}, R}}(eqInt{{}}({variable}:SortInt{{}}, \dv{{SortInt{{}}}}("{value}")), \dv{{SortBool{{}}}}("true"))"#
    )
}

const UNDEFINED: &str = r#"mk{}(divInt{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0")))"#;

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

fn simplified_ceil(definition: &BackendDefinition, term: &str, sort: &str) -> Predicate {
    let query = format!(r"\ceil{{{sort}, {sort}}}({term})");
    let syntax = k_rust_kore::kore::parser::parse_pattern(&query).expect("the query parses");
    let (predicate, _) = definition
        .admit_unverified(&syntax, &[])
        .internalize_predicate()
        .expect("the query internalizes");
    simplify_predicate_with_solver(
        definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("the query simplifies")
}

/// `\ceil(term)` keeps its obligation: the backend makes no definedness claim about `term`.
fn assert_obligation_kept(definition: &BackendDefinition, term: &str, sort: &str) {
    assert_ne!(
        simplified_ceil(definition, term, sort),
        Predicate::True,
        "\\ceil({term}) was discharged"
    );
}

/// The check names a relevant pair, for the reason `reason` when given, and withdraws the claims
/// of each of `heads`.
fn assert_withdrawn(
    definition: &BackendDefinition,
    heads: &[&str],
    reason: Option<UnjoinedReason>,
) {
    let claims = definition.value_claims();
    let relevant = claims
        .unjoined()
        .iter()
        .filter(|pair| pair.relevant())
        .collect::<Vec<_>>();
    assert!(
        !relevant.is_empty(),
        "no relevant pair: {:?}",
        claims.unjoined()
    );
    if let Some(reason) = reason {
        assert!(
            relevant.iter().any(|pair| pair.reason == reason),
            "no pair for {reason:?}: {relevant:?}"
        );
    }
    let tainted = claims.tainted_symbols();
    for head in heads {
        assert!(
            tainted.iter().any(|symbol| symbol.as_ref() == *head),
            "{head} is not withdrawn: {tainted:?}"
        );
    }
}

/// The check names no pair at all: every critical pair is separated, refuted or joined.
fn assert_confluent(definition: &BackendDefinition) {
    let claims = definition.value_claims();
    assert!(claims.unjoined().is_empty(), "{:?}", claims.unjoined());
    assert!(claims.tainted_symbols().is_empty());
}

const HEADS: &str = r"
    sort SortH{} []
    sort SortG{} []
    symbol h{}(SortInt{}) : SortH{} [anywhere{}(), value-production{}()]
    symbol w{}(SortH{}) : SortS{} [anywhere{}(), value-production{}()]
";

/// Review 1, F1: `h(3) = h(1)` and `w(h(X)) = mk(X /Int 0) requires X ==Int 3`. Then
/// `w(h(1)) = w(h(3)) = mk(3 /Int 0)`, undefined. The inner pair at `h(X)` is conditional and
/// does not join.
#[test]
fn review_1_f1_an_inner_pair_under_a_requires_withdraws_both_heads() {
    let definition = definition(
        HEADS,
        &[
            anywhere(
                "h",
                &["SortInt{}"],
                "SortH{}",
                &[&int(3)],
                &format!("h{{}}({})", int(1)),
            ),
            equation(
                "w",
                &["SortH{}"],
                "SortS{}",
                &["h{}(VarX:SortInt{})"],
                r#"mk{}(divInt{}(VarX:SortInt{}, \dv{SortInt{}}("0")))"#,
                &int_equals("VarX", 3),
                "anywhere{}()",
            ),
        ],
    );
    assert_withdrawn(&definition, &["h", "w"], None);
    assert_obligation_kept(&definition, &format!("w{{}}(h{{}}({}))", int(1)), "SortS{}");
}

/// Review 1, F2: `h(3) = h(1)` and `w(h(3)) = mk(1 /Int 0)`: `w(h(1))` is undefined.
#[test]
fn review_1_f2_an_inner_pair_at_a_ground_argument_withdraws_both_heads() {
    let definition = definition(
        HEADS,
        &[
            anywhere(
                "h",
                &["SortInt{}"],
                "SortH{}",
                &[&int(3)],
                &format!("h{{}}({})", int(1)),
            ),
            anywhere(
                "w",
                &["SortH{}"],
                "SortS{}",
                &[&format!("h{{}}({})", int(3))],
                UNDEFINED,
            ),
        ],
    );
    assert_withdrawn(
        &definition,
        &["h", "w"],
        Some(UnjoinedReason::DifferentResults),
    );
    assert_obligation_kept(&definition, &format!("w{{}}(h{{}}({}))", int(1)), "SortS{}");
}

/// The pre-existing root pair of review 2: `g(1) = f(0)` and `g(X) = mk(1 /Int 0)`. Then
/// `f(0) = g(1)` is undefined.
#[test]
fn a_root_pair_with_an_undefined_side_withdraws_both_heads() {
    let definition = definition(
        r"
        symbol f{}(SortInt{}) : SortS{} [anywhere{}(), value-production{}()]
        symbol g{}(SortInt{}) : SortS{} [anywhere{}(), value-production{}()]
        ",
        &[
            anywhere(
                "g",
                &["SortInt{}"],
                "SortS{}",
                &[&int(1)],
                &format!("f{{}}({})", int(0)),
            ),
            anywhere(
                "g",
                &["SortInt{}"],
                "SortS{}",
                &["VarX:SortInt{}"],
                UNDEFINED,
            ),
        ],
    );
    assert_withdrawn(
        &definition,
        &["f", "g"],
        Some(UnjoinedReason::DifferentResults),
    );
    assert_obligation_kept(&definition, &format!("f{{}}({})", int(0)), "SortS{}");
}

/// Review 3, F2: `f(X, Z) = mk(X /Int 0) requires X ==Int 3` and `f(3, Z) = f(1, Z)`. The root
/// pair at `X = 3` is not refuted (its condition holds there) and its sides `mk(3 /Int 0)` and
/// `f(1, Z)` do not join, so `f(1, Y)`, the undefined value of `f(3, Y)`, keeps its obligation.
#[test]
fn review_3_f2_a_root_pair_whose_condition_is_not_refuted_withdraws_the_head() {
    let definition = definition(
        "symbol f{}(SortInt{}, SortInt{}) : SortS{} [anywhere{}(), value-production{}()]",
        &[
            equation(
                "f",
                &["SortInt{}", "SortInt{}"],
                "SortS{}",
                &["VarX:SortInt{}", "VarZ:SortInt{}"],
                r#"mk{}(divInt{}(VarX:SortInt{}, \dv{SortInt{}}("0")))"#,
                &int_equals("VarX", 3),
                "anywhere{}()",
            ),
            anywhere(
                "f",
                &["SortInt{}", "SortInt{}"],
                "SortS{}",
                &[&int(3), "VarZ:SortInt{}"],
                &format!("f{{}}({}, VarZ:SortInt{{}})", int(1)),
            ),
        ],
    );
    assert_withdrawn(&definition, &["f"], Some(UnjoinedReason::ConditionOpen));
    assert_obligation_kept(
        &definition,
        &format!("f{{}}({}, Y:SortInt{{}})", int(1)),
        "SortS{}",
    );
}

/// Review 9: two equations `f(k(c)) = c` with different `ensures` meet at one instance, where
/// they need not hold together; the pair is not joined.
#[test]
fn review_9_two_equations_with_different_ensures_withdraw_the_head() {
    let ensures = |value: i64| {
        format!(
            r#"\and{{SortA{{}}}}(c{{}}(), \equals{{SortBool{{}}, SortA{{}}}}(eqInt{{}}({}, {}), \dv{{SortBool{{}}}}("true")))"#,
            int(value),
            int(value)
        )
    };
    let declarations = r"
        sort SortA{} []
        symbol c{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol k{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol f{}(SortA{}) : SortA{} [anywhere{}(), value-production{}()]
    ";
    let axiom = |right: &str| {
        format!(
            r"axiom{{R}} \implies{{R}}(\and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortA{{}}, R}}(X0:SortA{{}}, k{{}}(c{{}}())), \top{{R}}())), \equals{{SortA{{}}, R}}(f{{}}(X0:SortA{{}}), {right})) [anywhere{{}}()]"
        )
    };
    let definition = definition(declarations, &[axiom(&ensures(1)), axiom(&ensures(2))]);
    assert_withdrawn(&definition, &["f"], Some(UnjoinedReason::EnsuresDiffer));
}

/// Review 10, F1 (`PENDING.md`): `f(k(c)) = c requires P(f(c))` beside `f(k(c)) = d`, with `P`
/// true on every value of `f(c)`. The root pair's condition is not refuted, and its sides `c`
/// and `d` are distinct constructors: in every model the condition fails, so `f(c)` is
/// undefined. The check names the pair and `\ceil(f(c))` keeps its obligation.
#[test]
fn review_10_f1_a_root_pair_whose_condition_mentions_the_application_withdraws_the_head() {
    let declarations = r"
        sort SortA{} []
        symbol c{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol d{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol k{}(SortA{}) : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol f{}(SortA{}) : SortA{} [anywhere{}(), value-production{}()]
        symbol sz{}(SortA{}) : SortInt{} [function{}(), total{}()]
    ";
    let requires = r#"\equals{SortBool{}, R}(eqInt{}(sz{}(f{}(c{}())), sz{}(f{}(c{}()))), \dv{SortBool{}}("true"))"#;
    let definition = definition(
        declarations,
        &[
            equation(
                "f",
                &["SortA{}"],
                "SortA{}",
                &["k{}(c{}())"],
                "c{}()",
                requires,
                "anywhere{}()",
            ),
            anywhere("f", &["SortA{}"], "SortA{}", &["k{}(c{}())"], "d{}()"),
        ],
    );
    assert_withdrawn(&definition, &["f"], None);
    assert_obligation_kept(&definition, "f{}(c{}())", "SortA{}");
}

/// Critique CS C1: `w(Z) = p(1)`, `g(5, Y) = w(Y /Int 0)` and `g(X, Y) = p(1)`, with `p` a value
/// production (`p(2) = p(1)` makes it an equation head that does not reach `p(1)`). The root pair
/// of `g` at `X = 5` has the sides `w(Y /Int 0)` and `p(1)`. `w(Z) = p(1)` would erase the
/// partial `Y /Int 0`, which is undefined, so the join refuses that step; in every model
/// `g(5, Y) = w(\bottom)` is undefined, hence so is `p(1)`.
#[test]
fn critique_cs_c1_a_join_step_erasing_an_undefined_subterm_is_refused() {
    let declarations = r"
        symbol p{}(SortInt{}) : SortS{} [anywhere{}(), value-production{}()]
        symbol w{}(SortInt{}) : SortS{} [anywhere{}(), value-production{}()]
        symbol g{}(SortInt{}, SortInt{}) : SortS{} [anywhere{}(), value-production{}()]
    ";
    let definition = definition(
        declarations,
        &[
            anywhere(
                "p",
                &["SortInt{}"],
                "SortS{}",
                &[&int(2)],
                &format!("p{{}}({})", int(1)),
            ),
            anywhere(
                "w",
                &["SortInt{}"],
                "SortS{}",
                &["VarZ:SortInt{}"],
                &format!("p{{}}({})", int(1)),
            ),
            anywhere(
                "g",
                &["SortInt{}", "SortInt{}"],
                "SortS{}",
                &[&int(5), "VarY:SortInt{}"],
                r#"w{}(divInt{}(VarY:SortInt{}, \dv{SortInt{}}("0")))"#,
            ),
            anywhere(
                "g",
                &["SortInt{}", "SortInt{}"],
                "SortS{}",
                &["VarX:SortInt{}", "VarY:SortInt{}"],
                &format!("p{{}}({})", int(1)),
            ),
        ],
    );
    assert_withdrawn(
        &definition,
        &["g", "w", "p"],
        Some(UnjoinedReason::JoinRefused),
    );
    assert_obligation_kept(&definition, &format!("p{{}}({})", int(1)), "SortS{}");
}

/// Critique CV C1: `foo(Y) = Y /Int 0 requires Y ==Int 3`, `v(0) = v(1)`, `f(m(Y)) = w(foo(Y))`,
/// `f(m(3)) = v(1)` and `w(X) = v(1)`. At `f(m(3))` the sides are `w(foo(3))` and `v(1)`;
/// `foo(3)` is undefined, so `w(foo(3))` is, and the axioms make `v(1)` undefined. The join
/// must not erase `foo(3)` through `w(X) = v(1)`.
#[test]
fn critique_cv_c1_a_join_step_past_an_undefined_redex_is_not_taken() {
    let declarations = r"
        sort SortA{} []
        symbol m{}(SortInt{}) : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol foo{}(SortInt{}) : SortInt{} [function{}()]
        symbol v{}(SortInt{}) : SortA{} [anywhere{}(), value-production{}()]
        symbol w{}(SortInt{}) : SortA{} [anywhere{}(), value-production{}()]
        symbol f{}(SortA{}) : SortA{} [anywhere{}(), value-production{}()]
    ";
    let definition = definition(
        declarations,
        &[
            equation(
                "foo",
                &["SortInt{}"],
                "SortInt{}",
                &["VarY:SortInt{}"],
                r#"divInt{}(VarY:SortInt{}, \dv{SortInt{}}("0"))"#,
                &int_equals("VarY", 3),
                "",
            ),
            anywhere(
                "v",
                &["SortInt{}"],
                "SortA{}",
                &[&int(0)],
                &format!("v{{}}({})", int(1)),
            ),
            anywhere(
                "f",
                &["SortA{}"],
                "SortA{}",
                &["m{}(VarY:SortInt{})"],
                "w{}(foo{}(VarY:SortInt{}))",
            ),
            anywhere(
                "f",
                &["SortA{}"],
                "SortA{}",
                &[&format!("m{{}}({})", int(3))],
                &format!("v{{}}({})", int(1)),
            ),
            anywhere(
                "w",
                &["SortInt{}"],
                "SortA{}",
                &["VarX:SortInt{}"],
                &format!("v{{}}({})", int(1)),
            ),
        ],
    );
    assert_withdrawn(&definition, &["f", "w", "v"], None);
    assert_obligation_kept(&definition, &format!("v{{}}({})", int(1)), "SortA{}");
}

/// Finding N1 of the design: `g(X:A) = c1` and `g(X:A) = c2` with distinct constructors, where
/// every element of `A` is an application of the value production `v`. Every model makes `A`
/// empty, so `v(1)` is undefined, though `v` occurs in neither equation: the closure follows the
/// pair's variable into the heads its sort holds (T-obs).
#[test]
fn finding_n1_a_pair_withdraws_the_heads_its_variables_range_over() {
    let declarations = r"
        sort SortA{} []
        sort SortB{} []
        symbol c1{}() : SortB{} [constructor{}(), functional{}(), injective{}()]
        symbol c2{}() : SortB{} [constructor{}(), functional{}(), injective{}()]
        symbol v{}(SortInt{}) : SortA{} [anywhere{}(), value-production{}()]
        symbol g{}(SortA{}) : SortB{} [function{}()]
    ";
    let definition = definition(
        declarations,
        &[
            equation(
                "g",
                &["SortA{}"],
                "SortB{}",
                &["VarX:SortA{}"],
                "c1{}()",
                r"\top{R}()",
                "",
            ),
            equation(
                "g",
                &["SortA{}"],
                "SortB{}",
                &["VarX:SortA{}"],
                "c2{}()",
                r"\top{R}()",
                "",
            ),
        ],
    );
    assert_withdrawn(&definition, &["v"], Some(UnjoinedReason::DifferentResults));
    assert_obligation_kept(&definition, &format!("v{{}}({})", int(1)), "SortA{}");
}

/// Finding N1 with the value production hooked (review 2 of the load's scope, N1): `v` is still
/// an equation head (`anywhere`, not a declared function), partial, and the only one, so every
/// model makes `A` empty and `v(N)` undefined. The closure reaches `v` through the pair's
/// variable (T-obs), which no hook exempts; the check must not skip the pairs because `v` is
/// hooked. Its hook never applies to a `Nat` (inhabited by `z`), so no hook evaluation decides
/// `\ceil(v(N))`.
#[test]
fn finding_n1_holds_when_the_value_production_is_hooked() {
    let declarations = r#"
        sort SortA{} []
        sort SortB{} []
        sort SortNat{} []
        symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
        symbol c1{}() : SortB{} [constructor{}(), functional{}(), injective{}()]
        symbol c2{}() : SortB{} [constructor{}(), functional{}(), injective{}()]
        hooked-symbol v{}(SortNat{}) : SortA{}
            [anywhere{}(), value-production{}(), hook{}("INT.abs")]
        symbol g{}(SortA{}) : SortB{} [function{}()]
    "#;
    let definition = definition(
        declarations,
        &[
            equation(
                "g",
                &["SortA{}"],
                "SortB{}",
                &["VarX:SortA{}"],
                "c1{}()",
                r"\top{R}()",
                "",
            ),
            equation(
                "g",
                &["SortA{}"],
                "SortB{}",
                &["VarX:SortA{}"],
                "c2{}()",
                r"\top{R}()",
                "",
            ),
        ],
    );
    assert_withdrawn(&definition, &["v"], Some(UnjoinedReason::DifferentResults));
    assert_obligation_kept(&definition, "v{}(N:SortNat{})", "SortA{}");
}

/// A pair whose `requires` could be refuted only through a claim on a head the pair itself
/// withdraws: `f(X) = c1 requires X ==K h(1)` and `f(X) = c2 requires X ==K h(2)`. Refuting the
/// conjunction needs `h(1)` and `h(2)` to be distinct values, a free claim about `h`; the check
/// runs with every claim withheld, so the pair is not refuted, and `h` (mentioned by both
/// equations) is withdrawn.
#[test]
fn a_condition_refutable_only_through_a_withdrawn_claim_is_not_refuted() {
    let declarations = r#"
        sort SortA{} []
        sort SortB{} []
        symbol c1{}() : SortB{} [constructor{}(), functional{}(), injective{}()]
        symbol c2{}() : SortB{} [constructor{}(), functional{}(), injective{}()]
        symbol h{}(SortInt{}) : SortA{} [anywhere{}(), value-production{}()]
        symbol f{}(SortA{}) : SortB{} [function{}()]
        hooked-symbol eqA{}(SortA{}, SortA{}) : SortBool{}
            [function{}(), total{}(), hook{}("KEQUAL.eq")]
    "#;
    let requires = |value: i64| {
        format!(
            r#"\equals{{SortBool{{}}, R}}(eqA{{}}(VarX:SortA{{}}, h{{}}({})), \dv{{SortBool{{}}}}("true"))"#,
            int(value)
        )
    };
    let definition = definition(
        declarations,
        &[
            equation(
                "f",
                &["SortA{}"],
                "SortB{}",
                &["VarX:SortA{}"],
                "c1{}()",
                &requires(1),
                "",
            ),
            equation(
                "f",
                &["SortA{}"],
                "SortB{}",
                &["VarX:SortA{}"],
                "c2{}()",
                &requires(2),
                "",
            ),
        ],
    );
    assert_withdrawn(&definition, &["h"], None);
}

/// Critique CS M1: `b() = a()`, `f(a) = c [priority(40)]` and `f(X) = d [priority(50)]`. The
/// root pair of `f` is separated by priority and `b`'s equation has no non-variable position
/// below its root: the definition is accepted, and innermost evaluation gives `f(b())` the one
/// normal form `c`.
#[test]
fn critique_cs_m1_a_priority_separated_pair_is_no_pair() {
    let declarations = r"
        sort SortA{} []
        sort SortB{} []
        symbol a{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol c{}() : SortB{} [constructor{}(), functional{}(), injective{}()]
        symbol d{}() : SortB{} [constructor{}(), functional{}(), injective{}()]
        symbol b{}() : SortA{} [anywhere{}(), value-production{}()]
        symbol f{}(SortA{}) : SortB{} [function{}()]
    ";
    let definition = definition(
        declarations,
        &[
            anywhere("b", &[], "SortA{}", &[], "a{}()"),
            equation(
                "f",
                &["SortA{}"],
                "SortB{}",
                &["a{}()"],
                "c{}()",
                r"\top{R}()",
                r#"priority{}("40")"#,
            ),
            equation(
                "f",
                &["SortA{}"],
                "SortB{}",
                &["VarX:SortA{}"],
                "d{}()",
                r"\top{R}()",
                r#"priority{}("50")"#,
            ),
        ],
    );
    assert_confluent(&definition);
}

/// Review 2, F3 (the stack overflow of the per-query analysis): `f(f(inj{K,F}(k(X)))) = c`. An
/// injection never meets an application at the inner position, so there is no pair, and no
/// claim of `f` is withdrawn.
#[test]
fn review_2_f3_an_injection_against_an_application_is_no_pair() {
    let declarations = r"
        sort SortF{} []
        sort SortK{} []
        symbol inj{From, To}(From) : To [sortInjection{}()]
        axiom{R} \exists{R}(V:SortF{}, \equals{SortF{}, R}(V:SortF{}, inj{SortK{}, SortF{}}(From:SortK{}))) [subsort{SortK{}, SortF{}}()]
        symbol k{}(SortInt{}) : SortK{} [constructor{}(), functional{}(), injective{}()]
        symbol c{}() : SortF{} [constructor{}(), functional{}(), injective{}()]
        symbol f{}(SortF{}) : SortF{} [anywhere{}(), value-production{}()]
    ";
    let definition = definition(
        declarations,
        &[anywhere(
            "f",
            &["SortF{}"],
            "SortF{}",
            &["f{}(inj{SortK{}, SortF{}}(k{}(VarX:SortInt{})))"],
            "c{}()",
        )],
    );
    assert_confluent(&definition);
}

/// A `concrete` equation applies only to ground terms, yet it is an axiom about every instance
/// (precondition P4). The instance-normal scan therefore counts it as reaching every application
/// it unifies with: `f(Y)` under `f(X) = mk(1) [concrete]` is not instance-normal, and
/// `\ceil(f(Y))` keeps its obligation although the check names no pair.
#[test]
fn a_concrete_equation_counts_as_reaching_in_the_instance_normal_scan() {
    let definition = definition(
        "symbol f{}(SortInt{}) : SortS{} [anywhere{}(), value-production{}()]",
        &[equation(
            "f",
            &["SortInt{}"],
            "SortS{}",
            &["VarX:SortInt{}"],
            &format!("mk{{}}({})", int(1)),
            r"\top{R}()",
            "anywhere{}(), concrete{}()",
        )],
    );
    assert_confluent(&definition);
    assert_obligation_kept(&definition, "f{}(VarY:SortInt{})", "SortS{}");
}

/// A `symbolic` equation never applies to a ground term, so the simplifier leaves `f(1)` under
/// `f(X) = mk(1) [symbolic]` unevaluated; the equation matched, so its scan is no failed match,
/// and `f(1)` gets no certificate. Nor is it instance-normal (the equation unifies with it), so
/// `\ceil(f(1))` keeps its obligation.
#[test]
fn a_symbolic_equation_that_matches_withholds_the_certificate() {
    let definition = definition(
        "symbol f{}(SortInt{}) : SortS{} [anywhere{}(), value-production{}()]",
        &[equation(
            "f",
            &["SortInt{}"],
            "SortS{}",
            &["VarX:SortInt{}"],
            &format!("mk{{}}({})", int(1)),
            r"\top{R}()",
            "anywhere{}(), symbolic{}()",
        )],
    );
    assert_confluent(&definition);
    assert_obligation_kept(&definition, &format!("f{{}}({})", int(1)), "SortS{}");
}

/// Review 1 of the check, F2: a total function's stuck application is a normal form (`->E` rule
/// 3 reads only partial functions as `\bottom`), so a join case whose values hold `tw(Y)` is not
/// vacuous. `f(Y) = h(g(Y), Y)` and `f(Y) = v(Y)` with `g(tw(Y)) = mk(1 /Int 0)`: at `Y = tw(1)`
/// the first side is undefined, so every model makes `v(tw(1))` undefined.
#[test]
fn review_1_f2_a_stuck_total_application_in_a_case_is_a_normal_form() {
    let declarations = r"
        sort SortW{} []
        symbol tw{}(SortInt{}) : SortW{} [function{}(), total{}()]
        symbol g{}(SortW{}) : SortS{} [anywhere{}()]
        symbol h{}(SortS{}, SortW{}) : SortS{} [anywhere{}()]
        symbol v{}(SortW{}) : SortS{} [anywhere{}(), value-production{}()]
        symbol f{}(SortW{}) : SortS{} [anywhere{}()]
    ";
    let definition = definition(
        declarations,
        &[
            anywhere(
                "g",
                &["SortW{}"],
                "SortS{}",
                &["tw{}(VarY:SortInt{})"],
                UNDEFINED,
            ),
            anywhere(
                "h",
                &["SortS{}", "SortW{}"],
                "SortS{}",
                &["VarZ:SortS{}", "VarY:SortW{}"],
                "v{}(VarY:SortW{})",
            ),
            anywhere(
                "f",
                &["SortW{}"],
                "SortS{}",
                &["VarY:SortW{}"],
                "h{}(g{}(VarY:SortW{}), VarY:SortW{})",
            ),
            anywhere(
                "f",
                &["SortW{}"],
                "SortS{}",
                &["VarY:SortW{}"],
                "v{}(VarY:SortW{})",
            ),
        ],
    );
    assert_withdrawn(&definition, &["f", "v"], None);
    assert_obligation_kept(&definition, "v{}(VarX:SortW{})", "SortS{}");
    assert_obligation_kept(
        &definition,
        &format!("v{{}}(tw{{}}({}))", int(1)),
        "SortS{}",
    );
}

/// N1 with the elements of the pair's variable sort `A` built from `B` by `wrapper`, and `B`
/// built only by the value production `v`: `g(X:A) = c1` and `g(X:A) = c2` make `A` empty in
/// every model, so `B` too (the wrapper is total), and `v(1)` is undefined.
fn n1_through(wrapper: &str, extra: &str) -> BackendDefinition {
    let declarations = format!(
        r"
        sort SortA{{}} []
        sort SortB{{}} []
        sort SortC{{}} []
        symbol c1{{}}() : SortC{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
        symbol c2{{}}() : SortC{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
        symbol v{{}}(SortInt{{}}) : SortB{{}} [anywhere{{}}(), value-production{{}}()]
        symbol u{{}}(SortB{{}}) : SortA{{}} [{wrapper}]
        symbol g{{}}(SortA{{}}) : SortC{{}} [function{{}}()]
        {extra}
    "
    );
    definition(
        &declarations,
        &[
            equation(
                "g",
                &["SortA{}"],
                "SortC{}",
                &["VarX:SortA{}"],
                "c1{}()",
                r"\top{R}()",
                "",
            ),
            equation(
                "g",
                &["SortA{}"],
                "SortC{}",
                &["VarX:SortA{}"],
                "c2{}()",
                r"\top{R}()",
                "",
            ),
        ],
    )
}

/// Review 1 of the check, F1: the model cannot collapse `u`'s applications into an old element
/// of `A`, because no model has one, so `A`'s elements hold `v`'s applications.
#[test]
fn review_1_f1_n1_through_a_total_function() {
    let definition = n1_through("function{}(), total{}()", "");
    assert_withdrawn(
        &definition,
        &["g", "v"],
        Some(UnjoinedReason::DifferentResults),
    );
    assert_obligation_kept(&definition, &format!("v{{}}({})", int(1)), "SortB{}");
}

/// Review 1 of the check, F1: the same through a `functional` symbol that is neither a
/// constructor nor a function.
#[test]
fn review_1_f1_n1_through_an_uninterpreted_symbol() {
    let definition = n1_through("functional{}()", "");
    assert_withdrawn(
        &definition,
        &["g", "v"],
        Some(UnjoinedReason::DifferentResults),
    );
    assert_obligation_kept(&definition, &format!("v{{}}({})", int(1)), "SortB{}");
}

/// Review 1 of the check, the control: the same through a constructor.
#[test]
fn review_1_n1_through_a_constructor() {
    let definition = n1_through("constructor{}(), functional{}(), injective{}()", "");
    assert_withdrawn(
        &definition,
        &["g", "v"],
        Some(UnjoinedReason::DifferentResults),
    );
    assert_obligation_kept(&definition, &format!("v{{}}({})", int(1)), "SortB{}");
}

/// Where `A` has an element in every model (a constant constructor `a0`), the model collapses
/// `u`'s applications holding a new element into it, and `v` keeps its claims. (This definition
/// has no model at all, `g(a0)` being both `c1` and `c2`; the claim is vacuously true, and the
/// test pins that the collapse is still taken where it is valid.) The pair of the function `g`
/// then reaches no symbol the gate is asked about, so the load's scope does not classify it:
/// the full check names it and taints `g`, and neither verdict taints `v`.
#[test]
fn n1_through_a_total_function_into_a_surely_inhabited_sort_keeps_the_claims() {
    let definition = n1_through(
        "function{}(), total{}()",
        "symbol a0{}() : SortA{} [constructor{}(), functional{}(), injective{}()]",
    );
    let full = definition.value_claims_in_scope(CheckScope::All);
    let tainted = full.tainted_symbols();
    assert!(
        tainted.iter().any(|symbol| symbol.as_ref() == "g"),
        "{tainted:?}"
    );
    assert!(
        !tainted.iter().any(|symbol| symbol.as_ref() == "v"),
        "{tainted:?}"
    );
    let loaded = definition.value_claims();
    assert!(loaded.unjoined().is_empty(), "{:?}", loaded.unjoined());
    assert!(loaded.tainted_symbols().is_empty());
    assert_eq!(loaded.counts().skipped, 1);
    assert!(
        loaded.claim_differences(&full, &definition).is_empty(),
        "{:?}",
        loaded.claim_differences(&full, &definition)
    );
}

/// Review 1 of the check (seeded-defect control): `A`'s elements come only from its subsort `B`,
/// built by `v`. `A` has a normal form through the subsort, so the overlap is not vacuous.
#[test]
fn review_1_n1_through_a_subsort() {
    let declarations = r"
        sort SortA{} []
        sort SortB{} []
        sort SortC{} []
        symbol c1{}() : SortC{} [constructor{}(), functional{}(), injective{}()]
        symbol c2{}() : SortC{} [constructor{}(), functional{}(), injective{}()]
        symbol v{}(SortInt{}) : SortB{} [anywhere{}(), value-production{}()]
        symbol g{}(SortA{}) : SortC{} [function{}()]
        symbol inj{From, To}(From) : To [sortInjection{}()]
        axiom{R} \exists{R}(Val:SortA{}, \equals{SortA{}, R}(Val:SortA{}, inj{SortB{}, SortA{}}(From:SortB{}))) [subsort{SortB{}, SortA{}}()]
    ";
    let definition = definition(
        declarations,
        &[
            equation(
                "g",
                &["SortA{}"],
                "SortC{}",
                &["VarX:SortA{}"],
                "c1{}()",
                r"\top{R}()",
                "",
            ),
            equation(
                "g",
                &["SortA{}"],
                "SortC{}",
                &["VarX:SortA{}"],
                "c2{}()",
                r"\top{R}()",
                "",
            ),
        ],
    );
    assert_withdrawn(&definition, &["v"], Some(UnjoinedReason::DifferentResults));
    assert_obligation_kept(&definition, &format!("v{{}}({})", int(1)), "SortB{}");
}

/// Review 1 of the check, F4: the verdict is cached with the definition, so a definition loaded
/// inside a cancelled request gets the verdict it gets outside one.
#[test]
fn review_1_f4_a_cancelled_request_gets_the_same_verdict() {
    let build = || {
        definition(
            "symbol f{}(SortInt{}) : SortS{} [anywhere{}(), value-production{}()]",
            &[
                equation(
                    "f",
                    &["SortInt{}"],
                    "SortS{}",
                    &["VarX:SortInt{}"],
                    "mk{}(VarX:SortInt{})",
                    &int_equals("VarX", 1),
                    "anywhere{}()",
                ),
                equation(
                    "f",
                    &["SortInt{}"],
                    "SortS{}",
                    &["VarX:SortInt{}"],
                    &format!("mk{{}}({})", int(7)),
                    &int_equals("VarX", 2),
                    "anywhere{}()",
                ),
            ],
        )
    };
    let plain = build();
    assert_confluent(&plain);
    let token = k_rust_backend::stop::CancellationToken::new();
    token.cancel();
    let cancelled = token.scope(build);
    assert_confluent(&cancelled);
}

/// A total injective function into a builtin carrier cannot be interpreted on new elements (it
/// would need a fresh literal for each), so the heads its argument sort can hold are withdrawn.
#[test]
fn a_total_injective_function_into_a_builtin_sort_pins_what_its_arguments_hold() {
    let declarations = r"
        sort SortB{} []
        symbol v{}(SortInt{}) : SortB{} [anywhere{}(), value-production{}()]
        symbol toInt{}(SortB{}) : SortInt{} [function{}(), total{}(), injective{}()]
        symbol w{}(SortInt{}) : SortS{} [anywhere{}(), value-production{}()]
    ";
    let definition = definition(
        declarations,
        &[anywhere(
            "w",
            &["SortInt{}"],
            "SortS{}",
            &["VarX:SortInt{}"],
            "mk{}(VarX:SortInt{})",
        )],
    );
    let claims = definition.value_claims();
    assert!(
        claims.violations().iter().any(|violation| matches!(
            &violation.kind,
            k_rust_backend::confluence::ViolationKind::PinnedByInjectiveTotal(symbol)
                if symbol.as_ref() == "toInt"
        )),
        "{:?}",
        claims.violations()
    );
    let tainted = claims.tainted_symbols();
    assert!(
        tainted.iter().any(|symbol| symbol.as_ref() == "v"),
        "{tainted:?}"
    );
    assert!(
        !tainted.iter().any(|symbol| symbol.as_ref() == "w"),
        "{tainted:?}"
    );
}

/// Review 2 of the check: a hooked `Map` of `Int` keys and `B` values and a `Set` of `B`, where
/// `B` is built only by the value production `v`.
const REVIEW_2_COLLECTIONS: &str = r#"
    sort SortB{} []
    hooked-sort SortMap{} [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
    hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol mapItem{}(SortInt{}, SortB{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}(), unit{}(mapUnit{}())]
    hooked-symbol mapSize{}(SortMap{}) : SortInt{} [function{}(), total{}(), hook{}("MAP.size")]
    hooked-sort SortSet{} [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
    hooked-symbol setUnit{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
    hooked-symbol setItem{}(SortB{}) : SortSet{} [function{}(), total{}(), hook{}("SET.element")]
    hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{} [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}(), unit{}(setUnit{}())]
    symbol v{}(SortInt{}) : SortB{} [anywhere{}(), value-production{}()]
    symbol pick{}(SortMap{}) : SortS{} [function{}()]
    symbol wrapB{}(SortB{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol pickW{}(SortSet{}) : SortS{} [function{}()]
    symbol g{}(SortMap{}) : SortS{} [function{}()]
"#;

/// Review 2 of the check, F1, probe 1: `pick(K |-> V M) = mk(K)` matches `{1 |-> b, 2 |-> b}`
/// with `K = 1` and with `K = 2`, so `mk(1) = mk(2)` for every element `b` of `B`: every model
/// has `B` empty and `v(1)` undefined. The equation is a peak with itself.
#[test]
fn review_2_f1_a_map_pattern_matching_in_two_ways_withdraws_its_values() {
    let definition = definition(
        REVIEW_2_COLLECTIONS,
        &[equation(
            "pick",
            &["SortMap{}"],
            "SortS{}",
            &["mapConcat{}(mapItem{}(VarK:SortInt{}, VarV:SortB{}), VarM:SortMap{})"],
            "mk{}(VarK:SortInt{})",
            r"\top{R}()",
            "",
        )],
    );
    assert_withdrawn(
        &definition,
        &["pick", "v"],
        Some(UnjoinedReason::Unresolved(UnresolvedShape::SeveralMatches)),
    );
    assert_obligation_kept(&definition, &format!("v{{}}({})", int(1)), "SortB{}");
}

/// Review 2 of the check, F1, probe 2: `pickW(SetItem(X) S) = wrapB(X)` on `{v(1), v(2)}` gives
/// `wrapB(v(1)) = wrapB(v(2))`, so every model has `v(1) = v(2)` or one of them undefined (and
/// has a model: identify every `v(n)`). The backend must neither discharge `\ceil(v(1))` nor
/// refute `v(1) = v(2)`.
#[test]
fn review_2_f1_a_set_pattern_matching_in_two_ways_withdraws_its_elements() {
    let definition = definition(
        REVIEW_2_COLLECTIONS,
        &[equation(
            "pickW",
            &["SortSet{}"],
            "SortS{}",
            &["setConcat{}(setItem{}(VarX:SortB{}), VarS:SortSet{})"],
            "wrapB{}(VarX:SortB{})",
            r"\top{R}()",
            "",
        )],
    );
    assert_withdrawn(
        &definition,
        &["pickW", "v"],
        Some(UnjoinedReason::Unresolved(UnresolvedShape::SeveralMatches)),
    );
    assert_obligation_kept(&definition, &format!("v{{}}({})", int(1)), "SortB{}");
    let query = format!(
        r"\equals{{SortB{{}}, SortB{{}}}}(v{{}}({}), v{{}}({}))",
        int(1),
        int(2)
    );
    let syntax = k_rust_kore::kore::parser::parse_pattern(&query).expect("the query parses");
    let (predicate, _) = definition
        .admit_unverified(&syntax, &[])
        .internalize_predicate()
        .expect("the query internalizes");
    let simplified = simplify_predicate_with_solver(
        &definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("the query simplifies");
    assert_ne!(simplified, Predicate::False, "v(1) = v(2) was refuted");
}

/// Review 2 of the check, F2 (the reviewer's control): `g(M) = mk(1) requires size(M) ==Int 1`
/// beside `g(M) = mk(2)`. No model has a singleton map, so `B`, the sort of the map's values, is
/// empty: the pair withdraws `v` through `SortReach`'s map-value edge.
#[test]
fn review_2_f2_a_pair_withdraws_the_heads_its_map_values_hold() {
    let definition = definition(
        REVIEW_2_COLLECTIONS,
        &[
            equation(
                "g",
                &["SortMap{}"],
                "SortS{}",
                &["VarM:SortMap{}"],
                &format!("mk{{}}({})", int(1)),
                &format!(
                    r#"\equals{{SortBool{{}}, R}}(eqInt{{}}(mapSize{{}}(VarM:SortMap{{}}), {}), \dv{{SortBool{{}}}}("true"))"#,
                    int(1)
                ),
                "",
            ),
            equation(
                "g",
                &["SortMap{}"],
                "SortS{}",
                &["VarM:SortMap{}"],
                &format!("mk{{}}({})", int(2)),
                r"\top{R}()",
                "",
            ),
        ],
    );
    assert_withdrawn(
        &definition,
        &["g", "v"],
        Some(UnjoinedReason::ConditionOpen),
    );
    assert_obligation_kept(&definition, &format!("v{{}}({})", int(1)), "SortB{}");
}

/// Review 3 of the check, probe P2: `pick(K |-> V M) = mk(1) ensures K ==Int 1`. The right-hand
/// side reads no variable, but the `ensures` reads `K`, which the matching chooses: on
/// `{1 |-> b, 2 |-> b}` the matching `K = 1` gives `mk(1)` and the matching `K = 2` asserts
/// `2 ==Int 1`, so the application is both `mk(1)` and `\bottom`. Every model therefore has no
/// two-entry map of `B` values, so `B` is empty and `v(1)` undefined. The self pair reads the
/// `ensures`, does not join, and withdraws `pick` and `v`.
#[test]
fn review_3_p2_a_self_pair_whose_ensures_reads_the_matched_key_withdraws_its_values() {
    let right = format!(
        r#"\and{{SortS{{}}}}(mk{{}}({}), \equals{{SortBool{{}}, SortS{{}}}}(eqInt{{}}(VarK:SortInt{{}}, {}), \dv{{SortBool{{}}}}("true")))"#,
        int(1),
        int(1)
    );
    let definition = definition(
        REVIEW_2_COLLECTIONS,
        &[equation(
            "pick",
            &["SortMap{}"],
            "SortS{}",
            &["mapConcat{}(mapItem{}(VarK:SortInt{}, VarV:SortB{}), VarM:SortMap{})"],
            &right,
            r"\top{R}()",
            "",
        )],
    );
    assert_withdrawn(
        &definition,
        &["pick", "v"],
        Some(UnjoinedReason::Unresolved(UnresolvedShape::SeveralMatches)),
    );
    assert_obligation_kept(&definition, &format!("v{{}}({})", int(1)), "SortB{}");
}

/// Review 3 of the check, probe P7: `pick(K |-> V M) = mk(K) \/ mk(K)`. The check does not read
/// a disjunctive right-hand side, so it counts it as reading every variable, the matched key
/// `K` among them: on `{1 |-> b, 2 |-> b}` the two matchings give `mk(1)` and `mk(2)`. The self
/// pair does not join and withdraws `pick` and `v`.
#[test]
fn review_3_p7_a_self_pair_with_a_disjunctive_right_hand_side_withdraws_its_values() {
    let definition = definition(
        REVIEW_2_COLLECTIONS,
        &[equation(
            "pick",
            &["SortMap{}"],
            "SortS{}",
            &["mapConcat{}(mapItem{}(VarK:SortInt{}, VarV:SortB{}), VarM:SortMap{})"],
            r"\or{SortS{}}(mk{}(VarK:SortInt{}), mk{}(VarK:SortInt{}))",
            r"\top{R}()",
            "",
        )],
    );
    assert_withdrawn(
        &definition,
        &["pick", "v"],
        Some(UnjoinedReason::Unresolved(UnresolvedShape::SeveralMatches)),
    );
    assert_obligation_kept(&definition, &format!("v{{}}({})", int(1)), "SortB{}");
}

/// The simplifier's result for the ground term `term`, printed with the conditions it carries.
fn simplified(definition: &BackendDefinition, term: &str) -> String {
    let result = crate::support::unstopped::simplify(
        definition,
        &crate::support::internal_term(definition, term),
        SimplificationOptions::default(),
    )
    .expect("the term simplifies");
    let printed = k_rust_kore::kore::printer::Printer::compact()
        .print_pattern(&k_rust_backend::externalize::term(&result.term));
    format!("{printed} with {:?}", result.constraints())
}

/// Sorts `C1, C2 < A, B < Top` (two maximal common subsorts of `A` and `B`), so that
/// `inj{A,Top}(Z)` and `inj{B,Top}(Y)` unify in two ways. `g(inj{B,Top}(Y)) = k()
/// requires p(Y)`, with `p` false on `C1` and true on `C2`: the `requires` is refuted on the
/// `C1` unifier only. `fr(k()) = hi`, `fr(X) = lo [owise]`. `q`'s two equations
/// `q(Z) = fr(g(inj{A,Top}(Z)))` and `q(Z) = lo` overlap at the root and join on `C1` but not
/// on `C2`: `q(inj{C2,A}(c2()))` is `hi` or `lo` depending on which applies.
const TWO_UNIFIERS: &str = r"
    sort SortTop{} []
    sort SortA{} []
    sort SortB{} []
    sort SortC1{} []
    sort SortC2{} []
    sort SortK{} []
    sort SortR{} []
    symbol inj{From, To}(From) : To [sortInjection{}()]
    axiom{R} \exists{R}(V:SortA{}, \equals{SortA{}, R}(V:SortA{}, inj{SortC1{}, SortA{}}(F:SortC1{}))) [subsort{SortC1{}, SortA{}}()]
    axiom{R} \exists{R}(V:SortB{}, \equals{SortB{}, R}(V:SortB{}, inj{SortC1{}, SortB{}}(F:SortC1{}))) [subsort{SortC1{}, SortB{}}()]
    axiom{R} \exists{R}(V:SortA{}, \equals{SortA{}, R}(V:SortA{}, inj{SortC2{}, SortA{}}(F:SortC2{}))) [subsort{SortC2{}, SortA{}}()]
    axiom{R} \exists{R}(V:SortB{}, \equals{SortB{}, R}(V:SortB{}, inj{SortC2{}, SortB{}}(F:SortC2{}))) [subsort{SortC2{}, SortB{}}()]
    axiom{R} \exists{R}(V:SortTop{}, \equals{SortTop{}, R}(V:SortTop{}, inj{SortA{}, SortTop{}}(F:SortA{}))) [subsort{SortA{}, SortTop{}}()]
    axiom{R} \exists{R}(V:SortTop{}, \equals{SortTop{}, R}(V:SortTop{}, inj{SortB{}, SortTop{}}(F:SortB{}))) [subsort{SortB{}, SortTop{}}()]
    axiom{R} \exists{R}(V:SortTop{}, \equals{SortTop{}, R}(V:SortTop{}, inj{SortC1{}, SortTop{}}(F:SortC1{}))) [subsort{SortC1{}, SortTop{}}()]
    axiom{R} \exists{R}(V:SortTop{}, \equals{SortTop{}, R}(V:SortTop{}, inj{SortC2{}, SortTop{}}(F:SortC2{}))) [subsort{SortC2{}, SortTop{}}()]
    symbol c1{}() : SortC1{} [constructor{}(), functional{}(), injective{}()]
    symbol c2{}() : SortC2{} [constructor{}(), functional{}(), injective{}()]
    symbol k{}() : SortK{} [constructor{}(), functional{}(), injective{}()]
    symbol hi{}() : SortR{} [constructor{}(), functional{}(), injective{}()]
    symbol lo{}() : SortR{} [constructor{}(), functional{}(), injective{}()]
    symbol p{}(SortB{}) : SortBool{} [function{}(), functional{}()]
    symbol g{}(SortTop{}) : SortK{} [anywhere{}(), value-production{}()]
    symbol fr{}(SortK{}) : SortR{} [function{}(), functional{}()]
    symbol q{}(SortA{}) : SortR{} [anywhere{}(), value-production{}()]
";

/// The axioms of [`TWO_UNIFIERS`], in the order its documentation lists them.
fn two_unifier_axioms() -> Vec<String> {
    let boolean = |value: bool| format!(r#"\dv{{SortBool{{}}}}("{value}")"#);
    vec![
        equation(
            "p",
            &["SortB{}"],
            "SortBool{}",
            &["inj{SortC1{}, SortB{}}(VarZ:SortC1{})"],
            &boolean(false),
            r"\top{R}()",
            "",
        ),
        equation(
            "p",
            &["SortB{}"],
            "SortBool{}",
            &["inj{SortC2{}, SortB{}}(VarZ:SortC2{})"],
            &boolean(true),
            r"\top{R}()",
            "",
        ),
        equation(
            "g",
            &["SortTop{}"],
            "SortK{}",
            &["inj{SortB{}, SortTop{}}(VarY:SortB{})"],
            "k{}()",
            &format!(
                r"\equals{{SortBool{{}}, R}}(p{{}}(VarY:SortB{{}}), {})",
                boolean(true)
            ),
            "anywhere{}()",
        ),
        equation(
            "fr",
            &["SortK{}"],
            "SortR{}",
            &["k{}()"],
            "hi{}()",
            r"\top{R}()",
            "",
        ),
        equation(
            "fr",
            &["SortK{}"],
            "SortR{}",
            &["VarX:SortK{}"],
            "lo{}()",
            r"\top{R}()",
            "owise{}()",
        ),
        equation(
            "q",
            &["SortA{}"],
            "SortR{}",
            &["VarZ:SortA{}"],
            "fr{}(g{}(inj{SortA{}, SortTop{}}(VarZ:SortA{})))",
            r"\top{R}()",
            "anywhere{}()",
        ),
        equation(
            "q",
            &["SortA{}"],
            "SortR{}",
            &["VarZ:SortA{}"],
            "lo{}()",
            r"\top{R}()",
            "anywhere{}()",
        ),
    ]
}

/// `refuted_at` (`confluence/join.rs:402`) settles an application only when the `requires` of
/// the equation it tries is refuted on every unifier of the application with the equation's
/// left-hand side. In [`TWO_UNIFIERS`] the `requires` of `g`'s equation is refuted on the `C1`
/// unifier of `g(inj{A,Top}(Z))` with `g(inj{B,Top}(Y))` and holds on the `C2` one, so the
/// root pair of `q` does not join: the check names it and withdraws `q`. Settling the
/// application when one unifier is refuted would join the pair and leave `q`'s claims, although
/// `q(inj{C2,A}(c2()))` is `hi` or `lo` depending on which of `q`'s equations applies.
#[test]
fn a_requires_refuted_on_one_of_two_unifiers_does_not_settle_the_application() {
    let forward = definition(TWO_UNIFIERS, &two_unifier_axioms());
    // Control: the two orders really disagree at `C2`.
    let first_wins = simplified(&forward, "q{}(inj{SortC2{}, SortA{}}(c2{}()))");
    let reversed = two_unifier_axioms().into_iter().rev().collect::<Vec<_>>();
    let last_wins = simplified(
        &definition(TWO_UNIFIERS, &reversed),
        "q{}(inj{SortC2{}, SortA{}}(c2{}()))",
    );
    assert_ne!(
        first_wins, last_wins,
        "the control does not separate the orders"
    );
    let tainted = forward.value_claims().tainted_symbols();
    assert!(
        tainted.iter().any(|symbol| symbol.as_ref() == "q"),
        "q keeps its claims: {:?}",
        forward.value_claims().unjoined()
    );
}

/// Whether the full check (`CheckScope::All`) accepts the definition: no pair it does not
/// join, no precondition row violated.
fn accepted(definition: &BackendDefinition) -> bool {
    let claims = definition.value_claims_in_scope(CheckScope::All);
    claims.unjoined().is_empty() && claims.violations().is_empty()
}

/// A definition the full check accepts gives every ground term one normal form (every peak
/// joins), so the order in which its axioms are written, which decides the order the evaluator
/// tries the equations of one priority group in, changes no ground result. On
/// [`TWO_UNIFIERS`] the check names `q`'s pair, so the premise is false here; a `refuted_at` that
/// settled an application on any refuted unifier would accept the definition, and the two
/// orders give `hi` and `lo` at `q(inj{C2,A}(c2()))`.
#[test]
fn an_accepted_definition_evaluates_alike_in_every_equation_order() {
    let forward_axioms = two_unifier_axioms();
    let backward_axioms = forward_axioms.iter().rev().cloned().collect::<Vec<_>>();
    let forward = definition(TWO_UNIFIERS, &forward_axioms);
    let backward = definition(TWO_UNIFIERS, &backward_axioms);
    if !(accepted(&forward) && accepted(&backward)) {
        return;
    }
    for query in [
        "q{}(inj{SortC1{}, SortA{}}(c1{}()))",
        "q{}(inj{SortC2{}, SortA{}}(c2{}()))",
    ] {
        assert_eq!(
            simplified(&forward, query),
            simplified(&backward, query),
            "the check accepts the definition, but {query} depends on the equation order"
        );
    }
}

/// The two sides of an equation at one ground instance, with the instance of its `requires`
/// (`None` for `\top`).
struct Instance {
    left: String,
    right: String,
    requires: Option<String>,
}

/// A term the backend claims as a value: an application or literal with the claim, or a
/// collection without a rest whose entries are claimed values.
fn is_claimed_value(term: &k_rust_backend::term::Term) -> bool {
    use k_rust_backend::term::TermKind;
    match term.kind() {
        TermKind::List {
            heads, rest: None, ..
        } => heads.iter().all(is_claimed_value),
        TermKind::Set {
            elements,
            rest: None,
            ..
        } => elements.iter().all(is_claimed_value),
        TermKind::Map {
            entries,
            rest: None,
            ..
        } => entries
            .iter()
            .all(|(key, value)| is_claimed_value(key) && is_claimed_value(value)),
        _ => term.attributes().value_claimed(),
    }
}

/// Whether `term` holds an application of a symbol other than a constructor.
fn holds_a_claimed_head(term: &k_rust_backend::term::Term) -> bool {
    use k_rust_backend::term::{SymbolType, TermKind};
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            !matches!(symbol.attributes.symbol_type, SymbolType::Constructor)
                || arguments.iter().any(holds_a_claimed_head)
        }
        TermKind::Injection { term, .. } => holds_a_claimed_head(term),
        TermKind::List { heads, .. } => heads.iter().any(holds_a_claimed_head),
        TermKind::Set { elements, .. } => elements.iter().any(holds_a_claimed_head),
        TermKind::Map { entries, .. } => entries
            .iter()
            .any(|(key, value)| holds_a_claimed_head(key) || holds_a_claimed_head(value)),
        TermKind::And(..) | TermKind::DomainValue { .. } | TermKind::Variable(_) => false,
    }
}

/// The failures of "no axiom equates two values the backend keeps apart" on `instances`. An
/// instance whose `requires` evaluates to `true` and whose two sides evaluate to two different
/// claimed values contradicts the claims, unless the values are built from constructors and
/// literals only, whose distinctness is the definition's own axiom: then the definition has no
/// model, and the load must warn about it.
fn equated_values_kept_apart(
    definition: &BackendDefinition,
    instances: &[Instance],
) -> Vec<String> {
    let evaluate = |term: &str| {
        crate::support::unstopped::simplify(
            definition,
            &crate::support::internal_term(definition, term),
            SimplificationOptions::default(),
        )
        .expect("the term simplifies")
    };
    let claims = definition.value_claims();
    let warns = !claims.unjoined().is_empty() || !claims.violations().is_empty();
    let mut failures = Vec::new();
    for instance in instances {
        if let Some(requires) = &instance.requires
            && !simplified(definition, requires).starts_with(r#"\dv{SortBool{}}("true")"#)
        {
            continue;
        }
        let (left, right) = (evaluate(&instance.left), evaluate(&instance.right));
        let claimed = |result: &k_rust_backend::simplify::Simplification| {
            is_claimed_value(&result.term) && result.constraints().is_empty()
        };
        if !(claimed(&left) && claimed(&right)) || left.term == right.term {
            continue;
        }
        let constructors_only =
            !holds_a_claimed_head(&left.term) && !holds_a_claimed_head(&right.term);
        if !(constructors_only && warns) {
            failures.push(format!(
                "{} = {}: the sides evaluate to {} and {}, two values the backend keeps apart \
                 (constructors only: {constructors_only}; the load warns: {warns})",
                instance.left,
                instance.right,
                simplified(definition, &instance.left),
                simplified(definition, &instance.right),
            ));
        }
    }
    failures
}

/// No axiom equates two values the backend keeps apart. A claim says that the evaluator's
/// normal forms are a model of the definition at the heads that keep their claims, and every
/// executable equation is an axiom of that model. Checked on [`TWO_UNIFIERS`] at its two ground
/// instances: the check names `q`'s pair, so the load warns about the definition, which has no
/// model (`hi` and `lo` are both `q(inj{C2,A}(c2()))`). A `refuted_at` that settled an
/// application on any refuted unifier would accept the definition, and one of `q`'s equations
/// would evaluate to `hi` on one side and `lo` on the other, in one build, whatever the order.
#[test]
fn no_axiom_equates_two_values_the_backend_keeps_apart() {
    let two_unifiers = definition(TWO_UNIFIERS, &two_unifier_axioms());
    let instances = [
        "inj{SortC1{}, SortA{}}(c1{}())",
        "inj{SortC2{}, SortA{}}(c2{}())",
    ]
    .into_iter()
    .flat_map(|argument| {
        let left = format!("q{{}}({argument})");
        [
            Instance {
                left: left.clone(),
                right: format!("fr{{}}(g{{}}(inj{{SortA{{}}, SortTop{{}}}}({argument})))"),
                requires: None,
            },
            Instance {
                left,
                right: "lo{}()".to_owned(),
                requires: None,
            },
        ]
    })
    .collect::<Vec<_>>();
    let failures = equated_values_kept_apart(&two_unifiers, &instances);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// An equation rooted at a hooked symbol must agree with the hook wherever the hook is defined:
/// otherwise the definition equates the hook's value with the equation's, and a claim that keeps
/// them apart holds in no model. `L ++ .List = ListItem(g(2)) requires size(L) ==Int 1` is
/// indexed at the bare variable `L` (the unit law normalizes its left-hand side to `L`). At
/// `L := ListItem(g(1))` the hook's value of the left-hand side is `ListItem(g(1))` (the unit
/// law), and the right-hand side evaluates to `ListItem(g(2))`; `g` (equation `g(0) = c`) keeps
/// its claims, so the backend holds `g(1)` and `g(2)` apart: `bar(g(1))` is `rb` and `bar(g(2))`
/// is `ra`. The hook's value is stated here by the unit law, because evaluating `ListItem(g(1))`
/// applies the equation itself.
#[test]
fn an_equation_on_a_hooked_symbol_agrees_with_the_hook_where_claims_are_kept() {
    let declarations = r#"
        hooked-sort SortList{}
            [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
        sort SortA{} []
        sort SortR{} []
        hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
        hooked-symbol listItem{}(SortA{}) : SortList{} [function{}(), total{}(), hook{}("LIST.element")]
        hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
            [function{}(), hook{}("LIST.concat"), assoc{}()]
        hooked-symbol sizeList{}(SortList{}) : SortInt{}
            [function{}(), total{}(), hook{}("LIST.size")]
        symbol c{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol ra{}() : SortR{} [constructor{}(), functional{}(), injective{}()]
        symbol rb{}() : SortR{} [constructor{}(), functional{}(), injective{}()]
        symbol g{}(SortInt{}) : SortA{} [anywhere{}(), value-production{}()]
        symbol bar{}(SortA{}) : SortR{} [function{}()]
    "#;
    let g = |value: i64| format!("g{{}}({})", int(value));
    let variable_indexed = definition(
        declarations,
        &[
            anywhere("g", &["SortInt{}"], "SortA{}", &[&int(0)], "c{}()"),
            equation(
                "bar",
                &["SortA{}"],
                "SortR{}",
                &[&g(2)],
                "ra{}()",
                r"\top{R}()",
                "",
            ),
            equation(
                "bar",
                &["SortA{}"],
                "SortR{}",
                &["VarX:SortA{}"],
                "rb{}()",
                r"\top{R}()",
                "owise{}()",
            ),
            equation(
                "listConcat",
                &["SortList{}", "SortList{}"],
                "SortList{}",
                &["VarL:SortList{}", "listUnit{}()"],
                &format!("listItem{{}}({})", g(2)),
                &format!(
                    r#"\equals{{SortBool{{}}, R}}(eqInt{{}}(sizeList{{}}(VarL:SortList{{}}), {}), \dv{{SortBool{{}}}}("true"))"#,
                    int(1)
                ),
                "",
            ),
        ],
    );
    let item = |value: i64| format!("listItem{{}}({})", g(value));
    let requires = simplified(
        &variable_indexed,
        &format!("eqInt{{}}(sizeList{{}}({}), {})", item(1), int(1)),
    );
    assert!(
        requires.starts_with(r#"\dv{SortBool{}}("true")"#),
        "{requires}"
    );
    let hook_value = format!("{} with []", {
        k_rust_kore::kore::printer::Printer::compact().print_pattern(
            &k_rust_backend::externalize::term(&crate::support::internal_term(
                &variable_indexed,
                &item(1),
            )),
        )
    });
    let right = simplified(&variable_indexed, &item(2));
    let kept = !variable_indexed
        .value_claims()
        .tainted_symbols()
        .iter()
        .any(|symbol| symbol.as_ref() == "g");
    assert!(
        hook_value == right || !kept,
        "at L := {}, the hook gives {hook_value} and the equation {right}, while g keeps its \
         claims: bar(g(1)) is {} and bar(g(2)) is {}",
        item(1),
        simplified(&variable_indexed, &format!("bar{{}}({})", g(1))),
        simplified(&variable_indexed, &format!("bar{{}}({})", g(2))),
    );
}

// Ticket K12: a pattern reads a ground equation-head application with the evidence a subject
// does. Whether two ground normal forms the backend certifies are one value or two is a symmetric
// relation, so it cannot depend on which of them an equation writes and which the query holds;
// and reading a pattern up to equations is the identity on a certified normal form.

/// `k` and `k2` constructors of `A`; `h` and `j` `anywhere` value productions of `A` with no
/// equation, so every application of either on an integer is a normal form of `A`, distinct from
/// every other.
const GROUND_VALUES: &str = r"
    sort SortA{} []
    symbol k{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
    symbol k2{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
    symbol h{}(SortInt{}) : SortA{} [anywhere{}(), value-production{}()]
    symbol j{}(SortInt{}) : SortA{} [anywhere{}(), value-production{}()]
    symbol f{}(SortA{}) : SortS{} [function{}()]
";

/// `f(pattern) = mk(1)` beside `f(X) = mk(2) [owise]`, with `extra` axioms first.
fn first_or_owise(declarations: &str, extra: &[String], pattern: &str) -> BackendDefinition {
    let mut axioms = extra.to_vec();
    axioms.push(equation(
        "f",
        &["SortA{}"],
        "SortS{}",
        &[pattern],
        &format!("mk{{}}({})", int(1)),
        r"\top{R}()",
        "",
    ));
    axioms.push(equation(
        "f",
        &["SortA{}"],
        "SortS{}",
        &["VarX:SortA{}"],
        &format!("mk{{}}({})", int(2)),
        r"\top{R}()",
        "owise{}()",
    ));
    definition(declarations, &axioms)
}

/// Invariant 1 of K12, metamorphic: for two distinct ground normal forms `a` and `b`,
/// `f(a) = mk(1)` beside `f(X) = mk(2) [owise]` queried at `f(b)`, and the same definition with
/// `a` and `b` exchanged, give one answer. Invariant 2 decides which: both are normal forms the
/// backend certifies, so they are two values, the first equation fails and the `owise` one gives
/// `mk(2)` (losing precision on both sides would keep the answers equal, and fails here).
#[test]
fn exchanging_the_ground_value_of_a_pattern_and_of_the_query_changes_no_answer() {
    let h = |value: i64| format!("h{{}}({})", int(value));
    let pairs = [
        ("k{}()".to_owned(), "k2{}()".to_owned()),
        ("k{}()".to_owned(), h(1)),
        (h(1), h(2)),
        (h(1), format!("j{{}}({})", int(1))),
    ];
    let mut failures = Vec::new();
    for (left, right) in &pairs {
        let forward = first_or_owise(GROUND_VALUES, &[], left);
        let backward = first_or_owise(GROUND_VALUES, &[], right);
        for definition in [&forward, &backward] {
            assert!(
                definition.value_claims().unjoined().is_empty()
                    && definition.value_claims().violations().is_empty(),
                "the definition keeps every claim"
            );
        }
        let expected = simplified(&forward, &format!("mk{{}}({})", int(2)));
        let one = simplified(&forward, &format!("f{{}}({right})"));
        let other = simplified(&backward, &format!("f{{}}({left})"));
        if one != expected || other != expected {
            failures.push(format!(
                "pattern {left}, query {right}: {one}\npattern {right}, query {left}: {other}\n\
                 expected {expected}"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// The reproducer of the item (FOLLOWUPS 2.2 "Value-claim precision limits", second bullet):
/// `f(h(1)) = mk(1)` beside `f(X) = mk(2) [owise]`, where `h(1)` is a normal form other than
/// `k()`, so `f(k())` fails the first equation and the `owise` one applies. The control writes
/// the constructor `k2()` in the pattern.
#[test]
fn an_equation_head_pattern_against_a_constructor_fails_to_match() {
    let control = first_or_owise(GROUND_VALUES, &[], "k2{}()");
    let mk2 = format!("mk{{}}({})", int(2));
    assert_eq!(
        simplified(&control, "f{}(k{}())"),
        simplified(&control, &mk2)
    );
    let definition = first_or_owise(GROUND_VALUES, &[], &format!("h{{}}({})", int(1)));
    assert!(
        definition
            .value_claims()
            .unjoined()
            .iter()
            .all(|pair| !pair.relevant()),
        "the definition has no relevant pair"
    );
    assert_eq!(
        simplified(&definition, "f{}(k{}())"),
        simplified(&definition, &mk2),
        "f(k()) is not evaluated by its owise equation"
    );
}

/// A left-hand side may name a ground subterm with a variable to reuse it on its right-hand side,
/// `f(h(\and(1, G))) = mk(G)`: an instance of the conjunction is an instance of `1`, so the
/// pattern denotes the one normal form `h(1)` and reads as it does written ground.
#[test]
fn a_pattern_that_names_a_ground_subterm_reads_as_its_value() {
    let pattern = format!(r"h{{}}(\and{{SortInt{{}}}}({}, VarG:SortInt{{}}))", int(1));
    let definition = definition(
        GROUND_VALUES,
        &[
            equation(
                "f",
                &["SortA{}"],
                "SortS{}",
                &[&pattern],
                "mk{}(VarG:SortInt{})",
                r"\top{R}()",
                "",
            ),
            equation(
                "f",
                &["SortA{}"],
                "SortS{}",
                &["VarX:SortA{}"],
                &format!("mk{{}}({})", int(2)),
                r"\top{R}()",
                "owise{}()",
            ),
        ],
    );
    for (query, value) in [("k{}()".to_owned(), 2), (format!("h{{}}({})", int(1)), 1)] {
        assert_eq!(
            simplified(&definition, &format!("f{{}}({query})")),
            simplified(&definition, &format!("mk{{}}({})", int(value))),
            "f({query})"
        );
    }
}

/// A ground left-hand-side application whose normality the scan shows only through another
/// recorded one. `b1` a constructor of `B`, `g` an `anywhere` value production of `B` with no
/// equation, and the lemma `h(g(2)) = k()`: the scan of `h(b1())` meets the pattern `g(2)` against
/// `b1()`, which only `g(2)`'s own token refutes. So `h(b1())` is recorded in a round after
/// `g(2)`, and `f(h(b1())) = mk(1)` fails on `f(k())` as the exchanged definition does.
#[test]
fn a_ground_pattern_normal_through_another_recorded_pattern_reads_as_its_value() {
    let declarations = format!(
        r"{GROUND_VALUES}
        sort SortB{{}} []
        symbol b1{{}}() : SortB{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
        symbol g{{}}(SortInt{{}}) : SortB{{}} [anywhere{{}}(), value-production{{}}()]
        symbol hb{{}}(SortB{{}}) : SortA{{}} [anywhere{{}}(), value-production{{}}()]
    "
    );
    let lemma = format!(
        r"axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{SortA{{}}, R}}(hb{{}}(g{{}}({})), \and{{SortA{{}}}}(k{{}}(), \top{{SortA{{}}}}()))) [simplification{{}}()]",
        int(2)
    );
    let normal = "hb{}(b1{}())";
    let forward = first_or_owise(&declarations, std::slice::from_ref(&lemma), normal);
    let backward = first_or_owise(&declarations, std::slice::from_ref(&lemma), "k{}()");
    let expected = simplified(&forward, &format!("mk{{}}({})", int(2)));
    assert_eq!(simplified(&forward, "f{}(k{}())"), expected);
    assert_eq!(simplified(&backward, &format!("f{{}}({normal})")), expected);
}

/// FOLLOWUPS 2.2 "Value-claim precision limits", third bullet (K12 bullet 3, a root range per
/// equation head): `f(f(inj{K,F}(k(X)))) = c` with `K < F`. Up to equations, an `f` application
/// denotes a normal form rooted at `f` or the value of one of `f`'s right-hand sides, here `c`;
/// neither is the injection `inj{K,F}(k(c))`, so no equation reaches `f(inj{K,F}(k(c)))` and the
/// value production's application is defined. The left-hand side's argument is not ground, so
/// K12's reading (a ground normal form) does not apply to it.
#[test]
#[ignore = "acceptance test of K12 bullet 3 (a root range per equation head), a new precision rule parked under the precision freeze (TQ27)"]
fn a_self_nested_left_hand_side_does_not_reach_an_injection() {
    let declarations = r"
        sort SortK{} []
        sort SortF{} []
        symbol inj{From, To}(From) : To [sortInjection{}()]
        axiom{R} \exists{R}(V:SortF{}, \equals{SortF{}, R}(V:SortF{}, inj{SortK{}, SortF{}}(From:SortK{}))) [subsort{SortK{}, SortF{}}()]
        symbol c{}() : SortF{} [constructor{}(), functional{}(), injective{}()]
        symbol k{}(SortF{}) : SortK{} [constructor{}(), functional{}(), injective{}()]
        symbol f{}(SortF{}) : SortF{} [anywhere{}(), function{}(), value-production{}()]
    ";
    let definition = definition(
        declarations,
        &[anywhere(
            "f",
            &["SortF{}"],
            "SortF{}",
            &["f{}(inj{SortK{}, SortF{}}(k{}(VarX:SortF{})))"],
            "c{}()",
        )],
    );
    assert_eq!(
        simplified_ceil(
            &definition,
            "f{}(inj{SortK{}, SortF{}}(k{}(c{}())))",
            "SortF{}"
        ),
        Predicate::True,
        "the definedness of f(inj(k(c))) is kept as an obligation"
    );
}

/// Invariant 1 of K12 read for every ground term, not only for normal forms. `h2` has the
/// equation `h2(0) = k()`, so the pattern `h2(0)` is not a normal form: `f(h2(0)) = mk(1)` says
/// `f(k()) = mk(1)`, and the check names its inner pair with `h2(0) = k()` and withdraws `h2`.
/// The pairs `(k(), h2(0))` and `(k2(), h2(0))` ask whether a non-normal ground subterm of a
/// left-hand side should denote its value (evaluated at load), an owner decision (TQ6), not
/// K12's acceptance test; the pattern `h2(1)`, a normal form, reads as its value under K12, and
/// its pair with `h2(0)` stays asymmetric only through `h2(0)`'s withdrawal.
#[test]
#[ignore = "evidence for the owner decision TQ6 (a non-normal ground left-hand-side subterm denoting its value): fails on (k(), h2(0)), (k2(), h2(0)) and (h2(1), h2(0)), each through the pattern h2(0)"]
fn exchanging_a_ground_pattern_with_equations_and_the_query_changes_no_answer() {
    let declarations = r"
        sort SortA{} []
        symbol k{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol k2{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
        symbol h2{}(SortInt{}) : SortA{} [anywhere{}(), value-production{}()]
        symbol f{}(SortA{}) : SortS{} [function{}()]
    ";
    let h2_equation = anywhere("h2", &["SortInt{}"], "SortA{}", &[&int(0)], "k{}()");
    let h2 = |value: i64| format!("h2{{}}({})", int(value));
    let mut asymmetric = Vec::new();
    for (left, right) in [
        ("k{}()".to_owned(), h2(0)),
        ("k2{}()".to_owned(), h2(0)),
        (h2(1), h2(0)),
    ] {
        let forward = first_or_owise(declarations, std::slice::from_ref(&h2_equation), &left);
        let backward = first_or_owise(declarations, std::slice::from_ref(&h2_equation), &right);
        let one = simplified(&forward, &format!("f{{}}({right})"));
        let other = simplified(&backward, &format!("f{{}}({left})"));
        let tainted = |definition: &BackendDefinition| {
            definition
                .value_claims()
                .tainted_symbols()
                .iter()
                .any(|symbol| symbol.as_ref() == "h2")
        };
        if one != other {
            asymmetric.push(format!(
                "pattern {left} (h2 withdrawn: {}), query {right}: {one}\npattern {right} (h2 \
                 withdrawn: {}), query {left}: {other}",
                tainted(&forward),
                tainted(&backward)
            ));
        }
    }
    assert!(asymmetric.is_empty(), "{}", asymmetric.join("\n\n"));
}
