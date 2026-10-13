//! A function equation that the evaluator sets aside (a `concrete` or `symbolic` attribute
//! rejects its binding, or its right-hand side is `\top`) still holds of the application it
//! matched. An `owise` equation's premise, and an explicit lower priority, state that the lower
//! equation applies only where no higher-priority equation does, so neither may apply in the
//! set-aside equation's place: the application stays unevaluated. Only where every higher
//! equation is refuted (its left-hand side does not match, or its `requires` is refuted, whether
//! or not an attribute set its binding aside) does a lower-priority equation apply. A
//! simplification lemma states no such premise, so a set-aside lemma only lets the next one be
//! tried.

use k_rust_backend::{definition::BackendDefinition, simplify::SimplificationOptions, term::Term};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::{internal_term, unstopped::simplify};

const PRELUDE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
    hooked-symbol ltInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.lt"), smt-hook{}("<")]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
    sort SortExp{} []
    symbol pair{}(SortInt{}, SortInt{}) : SortExp{} [constructor{}(), functional{}(), injective{}()]
    symbol mk{}(SortInt{}) : SortExp{} [constructor{}(), functional{}(), injective{}()]
"#;

/// A definition: the prelude, then `declarations` and `axioms`, in module `MAIN`.
fn definition(declarations: &str, axioms: &[String]) -> BackendDefinition {
    let source = format!(
        "[] module MAIN {PRELUDE} {declarations} {} endmodule []",
        axioms.join("\n")
    );
    let syntax = parse_definition(&source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

/// The equation `head(X0, ..., Xn) = right requires requires`, each `Xi` bound to
/// `patterns[i]` of sort `sorts[i]`, with the axiom attributes `attributes`.
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

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// `left op right` holds, for a Boolean Int hook `op`, as a `requires`.
fn holds(op: &str, left: &str, right: &str) -> String {
    format!(r#"\equals{{SortBool{{}}, R}}({op}{{}}({left}, {right}), \dv{{SortBool{{}}}}("true"))"#)
}

const TOP: &str = r"\top{R}()";

/// The function `g(Int) : Int` with `g(X) = 1` under the attribute `attribute` (`concrete` or
/// `symbolic`) and an unconstrained `owise` equation `g(_) = 0`.
fn g_beside_an_unconstrained_owise(attribute: &str) -> BackendDefinition {
    definition(
        "symbol g{}(SortInt{}) : SortInt{} [function{}()]",
        &[
            equation(
                "g",
                &["SortInt{}"],
                "SortInt{}",
                &["VarX:SortInt{}"],
                &int(1),
                TOP,
                &format!(r#"label{{}}("one"), {attribute}{{}}()"#),
            ),
            equation(
                "g",
                &["SortInt{}"],
                "SortInt{}",
                &["VarY:SortInt{}"],
                &int(0),
                TOP,
                r#"label{}("zero"), owise{}()"#,
            ),
        ],
    )
}

/// The result of simplifying `source` in `definition` without a path condition.
fn simplified(definition: &BackendDefinition, source: &str) -> (Term, Vec<String>) {
    let result = simplify(
        definition,
        &internal_term(definition, source),
        SimplificationOptions::default(),
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    (result.term, result.applied_rules.to_vec())
}

/// `source` is left as it is: no equation applies to it.
fn assert_kept(definition: &BackendDefinition, source: &str) {
    let (term, applied) = simplified(definition, source);
    assert_eq!(term, internal_term(definition, source), "{source}");
    assert!(applied.is_empty(), "{source}: {applied:?}");
}

/// `source` simplifies to `expected` by the equation labelled `rule`.
fn assert_evaluates(definition: &BackendDefinition, source: &str, expected: &str, rule: &str) {
    let (term, applied) = simplified(definition, source);
    assert_eq!(term, internal_term(definition, expected), "{source}");
    assert_eq!(applied, [rule], "{source}");
}

/// (a) A `concrete` equation set aside on a symbolic argument still holds of `g(N)`, so the
/// `owise` equation, whose premise excludes every argument the first equation matches, does not
/// apply: `g(N)` stays. On a ground argument the `concrete` equation applies.
#[test]
fn a_concrete_equation_set_aside_keeps_the_owise_equation_from_applying() {
    let definition = g_beside_an_unconstrained_owise("concrete");
    assert_kept(&definition, "g{}(VarN:SortInt{})");
    assert_evaluates(&definition, &format!("g{{}}({})", int(3)), &int(1), "one");
}

/// (b) The mirror of (a): a `symbolic` equation set aside on a ground argument keeps `g(3)`,
/// and applies to a symbolic one.
#[test]
fn a_symbolic_equation_set_aside_keeps_the_owise_equation_from_applying() {
    let definition = g_beside_an_unconstrained_owise("symbolic");
    assert_kept(&definition, &format!("g{{}}({})", int(3)));
    assert_evaluates(&definition, "g{}(VarN:SortInt{})", &int(1), "one");
}

/// (c) An anywhere head: `w(X) = mk(1) [anywhere, concrete]` above `w(_) = mk(0)
/// [anywhere, owise]` keeps `w(N)`, which the first equation equates with `mk(1)`.
#[test]
fn a_concrete_anywhere_equation_set_aside_keeps_the_owise_equation_from_applying() {
    let definition = definition(
        "symbol w{}(SortInt{}) : SortExp{} [anywhere{}(), functional{}()]",
        &[
            equation(
                "w",
                &["SortInt{}"],
                "SortExp{}",
                &["VarX:SortInt{}"],
                &format!("mk{{}}({})", int(1)),
                TOP,
                r#"label{}("one"), anywhere{}(), concrete{}()"#,
            ),
            equation(
                "w",
                &["SortInt{}"],
                "SortExp{}",
                &["VarY:SortInt{}"],
                &format!("mk{{}}({})", int(0)),
                TOP,
                r#"label{}("zero"), anywhere{}(), owise{}()"#,
            ),
        ],
    );
    assert_kept(&definition, "w{}(VarN:SortInt{})");
    assert_evaluates(
        &definition,
        &format!("w{{}}({})", int(3)),
        &format!("mk{{}}({})", int(1)),
        "one",
    );
}

/// (d) An equation whose right-hand side is `\top`, at priority 40, matches `fp(pair(1, 2))`;
/// the evaluator cannot rewrite the application to it, and the priority-50 equation, which the
/// priority reading confines to arguments no priority-40 equation matches, does not apply in
/// its place. An argument the first equation does not match takes the second.
#[test]
fn a_top_equation_keeps_a_lower_priority_equation_from_applying() {
    let definition = definition(
        "symbol fp{}(SortExp{}) : SortInt{} [function{}()]",
        &[
            equation(
                "fp",
                &["SortExp{}"],
                "SortInt{}",
                &["pair{}(VarA:SortInt{}, VarB:SortInt{})"],
                r"\top{SortInt{}}()",
                TOP,
                r#"label{}("top"), priority{}("40")"#,
            ),
            equation(
                "fp",
                &["SortExp{}"],
                "SortInt{}",
                &["VarE:SortExp{}"],
                &int(0),
                TOP,
                r#"label{}("zero"), priority{}("50")"#,
            ),
        ],
    );
    assert_kept(
        &definition,
        &format!("fp{{}}(pair{{}}({}, {}))", int(1), int(2)),
    );
    assert_evaluates(
        &definition,
        &format!("fp{{}}(mk{{}}({}))", int(1)),
        &int(0),
        "zero",
    );
}

/// (e) One priority group holds a `concrete` equation, set aside on `h(N, 0)`, and an equation
/// whose `requires` is refuted there. The refuted one says nothing about `h(N, 0)`, but the
/// set-aside one still equates it with 1, so the group keeps the application and the `owise`
/// equation does not apply.
#[test]
fn a_set_aside_equation_is_not_hidden_by_a_refuted_sibling() {
    let definition = definition(
        "symbol h{}(SortInt{}, SortInt{}) : SortInt{} [function{}()]",
        &[
            equation(
                "h",
                &["SortInt{}", "SortInt{}"],
                "SortInt{}",
                &["VarX:SortInt{}", "VarY:SortInt{}"],
                &int(1),
                TOP,
                r#"label{}("concrete"), concrete{}()"#,
            ),
            equation(
                "h",
                &["SortInt{}", "SortInt{}"],
                "SortInt{}",
                &["VarX:SortInt{}", "VarY:SortInt{}"],
                &int(2),
                &holds("eqInt", "VarY:SortInt{}", &int(1)),
                r#"label{}("refuted")"#,
            ),
            equation(
                "h",
                &["SortInt{}", "SortInt{}"],
                "SortInt{}",
                &["VarX:SortInt{}", "VarY:SortInt{}"],
                &int(0),
                TOP,
                r#"label{}("zero"), owise{}()"#,
            ),
        ],
    );
    assert_kept(&definition, &format!("h{{}}(VarN:SortInt{{}}, {})", int(0)));
    assert_evaluates(
        &definition,
        &format!("h{{}}({}, {})", int(5), int(0)),
        &int(1),
        "concrete",
    );
}

/// (e2) A `concrete` equation with `requires X >Int 10`, set aside on a symbolic argument, above
/// an `owise` equation. The `owise` premise excludes only the arguments where that `requires`
/// holds: under `N <Int 5` it is refuted and the `owise` equation applies; under `N <Int 50` it
/// may hold, and `g(N)` stays.
#[cfg(feature = "z3")]
#[test]
fn a_set_aside_equation_whose_requires_is_refuted_lets_the_owise_equation_apply() {
    use k_rust_backend::{rule::Predicate, smt::Z3Solver};
    use k_rust_kore::kore::parser::parse_pattern;

    use crate::support::unstopped::simplify_with_solver;

    let definition = definition(
        "symbol g{}(SortInt{}) : SortInt{} [function{}()]",
        &[
            equation(
                "g",
                &["SortInt{}"],
                "SortInt{}",
                &["VarX:SortInt{}"],
                &int(1),
                &holds("gtInt", "VarX:SortInt{}", &int(10)),
                r#"label{}("one"), concrete{}()"#,
            ),
            equation(
                "g",
                &["SortInt{}"],
                "SortInt{}",
                &["VarY:SortInt{}"],
                &int(0),
                TOP,
                r#"label{}("zero"), owise{}()"#,
            ),
        ],
    );
    let solver = Z3Solver::new(&definition).unwrap();
    let subject = internal_term(&definition, "g{}(VarN:SortInt{})");
    let below = |bound: i64| {
        let syntax = parse_pattern(&format!(
            r#"\equals{{SortBool{{}}, SortInt{{}}}}(ltInt{{}}(VarN:SortInt{{}}, {}), \dv{{SortBool{{}}}}("true"))"#,
            int(bound)
        ))
        .expect("the path condition parses");
        let (predicate, _) = definition
            .admit_unverified(&syntax, &[])
            .internalize_predicate()
            .expect("the path condition internalizes");
        let known: Vec<Predicate> = vec![predicate];
        simplify_with_solver(
            &definition,
            &subject,
            &known,
            SimplificationOptions::default(),
            &solver,
        )
        .unwrap_or_else(|error| panic!("N < {bound}: {error:?}"))
    };

    let refuted = below(5);
    assert_eq!(refuted.term, internal_term(&definition, &int(0)));
    assert_eq!(refuted.applied_rules, ["zero"]);

    let open = below(50);
    assert_eq!(open.term, subject);
    assert!(open.applied_rules.is_empty(), "{:?}", open.applied_rules);
}

/// (f) Controls. A function equation whose `requires` is refuted says nothing about `q(0)`, so
/// the `owise` equation applies. A simplification lemma states no premise about the lemmas
/// after it, so one set aside by `concrete` lets the next lemma apply.
#[test]
fn a_refuted_requires_and_a_set_aside_lemma_still_let_the_next_equation_apply() {
    let definition = definition(
        "symbol q{}(SortInt{}) : SortInt{} [function{}()]
         symbol k{}(SortInt{}) : SortInt{} [function{}()]",
        &[
            equation(
                "q",
                &["SortInt{}"],
                "SortInt{}",
                &["VarX:SortInt{}"],
                &int(1),
                &holds("gtInt", "VarX:SortInt{}", &int(0)),
                r#"label{}("positive")"#,
            ),
            equation(
                "q",
                &["SortInt{}"],
                "SortInt{}",
                &["VarY:SortInt{}"],
                &int(0),
                TOP,
                r#"label{}("zero"), owise{}()"#,
            ),
            format!(
                r#"axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{SortInt{{}}, R}}(k{{}}(X:SortInt{{}}), \and{{SortInt{{}}}}({}, \top{{SortInt{{}}}}()))) [label{{}}("concrete-lemma"), concrete{{}}(), simplification{{}}("10")]"#,
                int(1)
            ),
            format!(
                r#"axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{SortInt{{}}, R}}(k{{}}(X:SortInt{{}}), \and{{SortInt{{}}}}({}, \top{{SortInt{{}}}}()))) [label{{}}("later-lemma"), simplification{{}}("20")]"#,
                int(2)
            ),
        ],
    );
    assert_evaluates(&definition, &format!("q{{}}({})", int(0)), &int(0), "zero");
    assert_evaluates(
        &definition,
        &format!("q{{}}({})", int(1)),
        &int(1),
        "positive",
    );
    assert_evaluates(&definition, "k{}(VarN:SortInt{})", &int(2), "later-lemma");
}
