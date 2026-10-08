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
    confluence::UnjoinedReason, definition::BackendDefinition, rule::Predicate,
    simplify::SimplificationOptions, smt::NoSolver,
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
