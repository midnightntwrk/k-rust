//! Run coverage (`crate::coverage`): an execution that asks for it reports every rule and
//! equation it applied, wherever the backend applied it, and every one whose condition it began
//! to decide for a matched instance.
//!
//! The axioms carry labels and no `UNIQUE_ID`, so each one's id is its label.

use std::{collections::BTreeSet, panic::AssertUnwindSafe};

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    coverage::{
        ConditionAtom, ConditionCollection, ConditionNode, ConditionRecord, RecordedValue,
        RuleConditions, RunCoverage, Truth, Verdict, collect, collect_offering, collect_recording,
        note_applied, note_matched, note_offered, offer, replay, suspend,
    },
    definition::BackendDefinition,
    rewrite::{
        ExecutionMode, ExecutionOptions, ExecutionResult, HaltReason, Pattern, execute,
        execute_with_io_state, execute_with_solver,
    },
    rule::Predicate,
    search::ResultModality,
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    stop::Stoppable,
    substitution::Substitution,
    term::{Sort, Term, Variable},
    transition::ExecutionIoState,
};

const TRUE: &str = r#"\dv{SortBool{}}("true")"#;

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// A function equation `head(X) = rhs requires requires` over one `Int` argument `X`.
fn equation(label: &str, head: &str, sort: &str, rhs: &str, requires: &str, attrs: &str) -> String {
    let requires = if requires.is_empty() {
        r"\top{R}()".to_owned()
    } else {
        format!(r"\equals{{SortBool{{}}, R}}({requires}, {TRUE})")
    };
    format!(
        r#"
            axiom{{R}} \implies{{R}}(
                \and{{R}}({requires}, \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, X:SortInt{{}}), \top{{R}}())),
                \equals{{{sort}, R}}({head}{{}}(X0:SortInt{{}}), \and{{{sort}}}({rhs}, \top{{{sort}}}()))
            ) [label{{}}("{label}"){attrs}]"#
    )
}

/// A rewrite rule `lhs => rhs requires requires ensures ensures` of sort `SortS`; a condition is
/// a Boolean term, or a matching-logic equality written out.
fn rule(label: &str, lhs: &str, rhs: &str, requires: &str, ensures: &str, attrs: &str) -> String {
    let condition = |condition: &str| {
        if condition.is_empty() {
            r"\top{SortS{}}()".to_owned()
        } else if condition.starts_with(r"\equals") {
            condition.to_owned()
        } else {
            format!(r"\equals{{SortBool{{}}, SortS{{}}}}({condition}, {TRUE})")
        }
    };
    format!(
        r#"
            axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}({lhs}, {requires}),
                \and{{SortS{{}}}}({rhs}, {ensures})
            ) [label{{}}("{label}"){attrs}]"#,
        requires = condition(requires),
        ensures = condition(ensures),
    )
}

const A: &str = "A:SortInt{}";
const X: &str = "X:SortInt{}";

fn definition() -> BackendDefinition {
    let zero = int(0);
    let one = int(1);
    let two = int(2);
    let axioms = vec![
        // Equations.
        equation("norm", "norm", "SortInt{}", X, "", ""),
        equation("normE", "normE", "SortInt{}", X, "", ""),
        equation(
            "part",
            "part",
            "SortInt{}",
            &format!("tot{{}}({X})"),
            &format!("geInt{{}}({X}, {zero})"),
            "",
        ),
        equation(
            "tot",
            "tot",
            "SortInt{}",
            &format!("plus{{}}({X}, {X})"),
            "",
            "",
        ),
        equation("inner", "inner", "SortInt{}", X, "", ""),
        equation(
            "outer",
            "outer",
            "SortInt{}",
            &one,
            &format!("geInt{{}}(inner{{}}({X}), {zero})"),
            "",
        ),
        equation("outerow", "outer", "SortInt{}", &zero, "", r#", owise{}()"#),
        equation("normR", "normR", "SortInt{}", X, "", ""),
        equation("owg", "owg", "SortInt{}", X, "", ""),
        equation(
            "owf1",
            "owf",
            "SortInt{}",
            &one,
            &format!("eqInt{{}}(owg{{}}({X}), {zero})"),
            "",
        ),
        equation("owf2", "owf", "SortInt{}", &two, "", r#", owise{}()"#),
        equation("unused", "unused", "SortInt{}", X, "", ""),
        // Ceil and predicate equations.
        format!(
            r#"
            axiom{{R}} \implies{{R}}(
                \top{{R}}(),
                \equals{{R, R}}(
                    \ceil{{SortInt{{}}, R}}(pu{{}}({X})),
                    \and{{R}}(\equals{{SortBool{{}}, R}}(geInt{{}}({X}, {zero}), {TRUE}), \top{{R}}())
                )
            ) [label{{}}("puCeil"), simplification{{}}()]"#
        ),
        format!(
            r#"
            axiom{{R}} \implies{{R}}(
                \top{{R}}(),
                \equals{{R, R}}(\ceil{{SortInt{{}}, R}}(pv{{}}({X})), \and{{R}}(\top{{R}}(), \top{{R}}()))
            ) [label{{}}("pvCeil"), simplification{{}}()]"#
        ),
        format!(
            r#"
            axiom{{R}} \implies{{R}}(
                \and{{R}}(\equals{{SortBool{{}}, R}}(geInt{{}}({X}, {zero}), {TRUE}), \top{{R}}()),
                \equals{{R, R}}(\ceil{{SortInt{{}}, R}}(pc{{}}({X})), \and{{R}}(\top{{R}}(), \top{{R}}()))
            ) [label{{}}("pcCeil"), simplification{{}}()]"#
        ),
        format!(
            r#"
            axiom{{R, Q}} \implies{{R}}(
                \top{{R}}(),
                \equals{{Q, R}}(
                    \equals{{SortInt{{}}, Q}}(pi{{}}({X}), {zero}),
                    \and{{Q}}(\top{{Q}}(), \top{{Q}}())
                )
            ) [label{{}}("piZero"), simplification{{}}()]"#
        ),
        // Rewrite rules.
        rule(
            "load",
            &format!("load{{}}({A})"),
            "halt{}()",
            &format!("eqInt{{}}(norm{{}}({A}), {A})"),
            "",
            "",
        ),
        rule(
            "ens",
            &format!("ens{{}}({A})"),
            "halt{}()",
            "",
            &format!("eqInt{{}}(normE{{}}({A}), {A})"),
            "",
        ),
        rule(
            "rhsp",
            &format!("rhsp{{}}({A})"),
            &format!("val{{}}(part{{}}({A}))"),
            "",
            "",
            "",
        ),
        rule(
            "rhst",
            &format!("rhst{{}}({A})"),
            &format!("val{{}}(tot{{}}({A}))"),
            "",
            "",
            "",
        ),
        rule(
            "eqreq",
            &format!("eqreq{{}}({A})"),
            &format!("val{{}}(outer{{}}({A}))"),
            "",
            "",
            "",
        ),
        rule(
            "rejHigh",
            &format!("rej{{}}({A})"),
            "fault{}()",
            &format!("ltInt{{}}(normR{{}}({A}), {zero})"),
            "",
            r#", priority{}("40")"#,
        ),
        rule("rej", &format!("rej{{}}({A})"), "halt{}()", "", "", ""),
        // `hop(A)` steps to `ow(A)`; on a state whose variable is spelled like the rules' `A`,
        // the step and the probe of `hopLow` both rename the rule apart, and the observed
        // bindings of the next step name its renamed variable.
        rule(
            "hop",
            &format!("hop{{}}({A})"),
            &format!("ow{{}}({A})"),
            "",
            "",
            "",
        ),
        rule(
            "hopLow",
            &format!("hop{{}}({A})"),
            "fault{}()",
            "",
            "",
            r#", priority{}("60")"#,
        ),
        // A rule below the productive group of `rej(A)`, never tried (`offered`).
        rule(
            "rejLow",
            &format!("rej{{}}({A})"),
            "fault{}()",
            "",
            "",
            r#", priority{}("60")"#,
        ),
        rule(
            "ow",
            &format!("ow{{}}({A})"),
            &format!("val{{}}(owf{{}}({A}))"),
            "",
            "",
            "",
        ),
        rule(
            "ru",
            &format!("ru{{}}({A})"),
            &format!("val{{}}(pu{{}}({A}))"),
            "",
            "",
            "",
        ),
        rule(
            "rv",
            &format!("rv{{}}({A})"),
            &format!("val{{}}(pv{{}}({A}))"),
            "",
            "",
            "",
        ),
        rule(
            "rc",
            &format!("rc{{}}({A})"),
            &format!("val{{}}(pc{{}}({A}))"),
            "",
            "",
            "",
        ),
        rule(
            "rp",
            &format!("rp{{}}({A})"),
            "halt{}()",
            &format!(r"\equals{{SortInt{{}}, SortS{{}}}}(pi{{}}({A}), {zero})"),
            "",
            "",
        ),
        rule("ndA", "nd{}()", "mid1{}()", "", "", ""),
        rule("ndB", "nd{}()", "mid2{}()", "", "", ""),
        rule("mid1", "mid1{}()", "halt{}()", "", "", ""),
        rule("mid2", "mid2{}()", "halt{}()", "", "", ""),
        rule(
            "nar",
            &format!("nw{{}}(wp{{}}({A}))"),
            "halt{}()",
            &format!("geInt{{}}({A}, {zero})"),
            "",
            "",
        ),
        // Definedness decisions about an operand a conditional does not evaluate.
        equation(
            "pdEq",
            "pd",
            "SortInt{}",
            X,
            &format!("geInt{{}}({X}, {zero})"),
            "",
        ),
        format!(
            r#"
            axiom{{R}} \implies{{R}}(
                \top{{R}}(),
                \equals{{R, R}}(
                    \ceil{{SortInt{{}}, R}}(pq{{}}({X})),
                    \and{{R}}(\equals{{SortBool{{}}, R}}(geInt{{}}({X}, {zero}), {TRUE}), \top{{R}}())
                )
            ) [label{{}}("pqCeil"), simplification{{}}()]"#
        ),
        equation("prEq", "pr", "SortInt{}", X, "", ""),
        rule(
            "d1",
            &format!("d1{{}}({A})"),
            &format!("val{{}}(ite{{}}(geInt{{}}({A}, {zero}), {A}, pd{{}}({A})))"),
            "",
            "",
            "",
        ),
        rule(
            "d2",
            &format!("d2{{}}({A})"),
            &format!("val{{}}(ite{{}}(ltInt{{}}({A}, {zero}), {zero}, pq{{}}({A})))"),
            "",
            "",
            "",
        ),
        rule(
            "d4",
            &format!("d4{{}}({A})"),
            &format!("val{{}}(ite{{}}({TRUE}, {zero}, pr{{}}({A})))"),
            "",
            "",
            "",
        ),
        // A discharge that decides one equation's condition and applies another.
        format!(
            r#"
            axiom{{R}} \implies{{R}}(
                \top{{R}}(),
                \equals{{R, R}}(
                    \ceil{{SortInt{{}}, R}}(pw{{}}({X})),
                    \and{{R}}(\equals{{SortBool{{}}, R}}(gate{{}}({X}), {TRUE}), \top{{R}}())
                )
            ) [label{{}}("pwCeil"), simplification{{}}()]"#
        ),
        equation(
            "gateNo",
            "gate",
            "SortBool{}",
            r#"\dv{SortBool{}}("false")"#,
            r#"\dv{SortBool{}}("false")"#,
            "",
        ),
        equation("gateYes", "gate", "SortBool{}", TRUE, "", r#", owise{}()"#),
        rule(
            "rw",
            &format!("rw{{}}({A})"),
            &format!("val{{}}(pw{{}}({A}))"),
            "",
            "",
            "",
        ),
    ];
    let unary = [
        "val", "load", "ens", "rhsp", "rhst", "eqreq", "rej", "ow", "ru", "rv", "rc", "rp", "d1",
        "d2", "d4", "rw", "hop",
    ]
    .map(|name| {
        format!(
            "symbol {name}{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]"
        )
    })
    .join("\n");
    let nullary = ["halt", "fault", "nd", "mid1", "mid2"]
        .map(|name| {
            format!("symbol {name}{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]")
        })
        .join("\n");
    let total = [
        "norm", "normE", "tot", "inner", "outer", "normR", "owg", "owf", "unused", "pi",
    ]
    .map(|name| {
        format!("symbol {name}{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]")
    })
    .join("\n");
    let partial = ["part", "pu", "pv", "pc", "pd", "pq", "pr", "pw"]
        .map(|name| format!("symbol {name}{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]"))
        .join("\n");
    let source = format!(
        r#"[]
        module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            sort SortS{{}} []
            sort SortW{{}} []
            hooked-symbol plus{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
            hooked-symbol geInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.ge"), smt-hook{{}}(">=")]
            hooked-symbol ltInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.lt"), smt-hook{{}}("<")]
            hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.eq"), smt-hook{{}}("=")]
            hooked-symbol ite{{}}(SortBool{{}}, SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), total{{}}(), hook{{}}("KEQUAL.ite")]
            symbol gate{{}}(SortInt{{}}) : SortBool{{}} [function{{}}(), total{{}}()]
            symbol wp{{}}(SortInt{{}}) : SortW{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol nw{{}}(SortW{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            {unary}
            {nullary}
            {total}
            {partial}
            {axioms}
        endmodule []"#,
        axioms = axioms.join("\n"),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
        .expect("term should internalize")
}

fn ground(definition: &BackendDefinition, source: &str) -> Pattern {
    Pattern {
        term: term(definition, source),
        constraints: Vec::new(),
    }
}

fn collecting() -> ExecutionOptions {
    ExecutionOptions {
        collect_coverage: true,
        ..ExecutionOptions::default()
    }
}

fn ids(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|name| (*name).to_owned()).collect()
}

/// The coverage the run reported.
fn coverage(result: &ExecutionResult) -> &RunCoverage {
    result
        .coverage
        .as_ref()
        .expect("the run collected its coverage")
}

/// Run `program` with coverage, and check that collecting changed nothing else: the result
/// without the option is the same, with no coverage (j).
fn covered(definition: &BackendDefinition, program: &str) -> (ExecutionResult, RunCoverage) {
    let initial = ground(definition, program);
    let mut result = execute(definition, initial.clone(), collecting());
    let plain = execute(definition, initial, ExecutionOptions::default());
    assert_eq!(
        plain.coverage, None,
        "{program}: coverage was not asked for"
    );
    let coverage = result
        .coverage
        .take()
        .expect("the run collected its coverage");
    assert_eq!(result, plain, "{program}: collecting changed the result");
    (result, coverage)
}

fn assert_coverage(coverage: &RunCoverage, applied: &[&str], matched: &[&str], program: &str) {
    assert_eq!(coverage.applied, ids(applied), "{program}: applied");
    assert_eq!(coverage.matched, ids(matched), "{program}: matched");
    assert!(
        !coverage.matched.contains("unused"),
        "{program}: an equation the run never reaches is in no set (h)"
    );
}

fn halt_reasons(result: &ExecutionResult) -> Vec<&HaltReason> {
    result.leaves.iter().map(|leaf| &leaf.halt_reason).collect()
}

/// (a) An equation used only in a rule's `requires`.
#[test]
fn an_equation_of_a_rule_requires_is_applied() {
    let definition = definition();
    let program = format!("load{{}}({})", int(1));
    let (_, coverage) = covered(&definition, &program);
    assert_coverage(&coverage, &["load", "norm"], &["load", "norm"], &program);
}

/// (b) An equation used only in a rule's `ensures`.
#[test]
fn an_equation_of_a_rule_ensures_is_applied() {
    let definition = definition();
    let program = format!("ens{{}}({})", int(1));
    let (_, coverage) = covered(&definition, &program);
    assert_coverage(&coverage, &["ens", "normE"], &["ens", "normE"], &program);
}

/// (c) A partial function in a right-hand side is evaluated during the step: its equation and
/// the equation it calls are applied.
#[test]
fn the_equations_of_a_partial_right_hand_side_are_applied() {
    let definition = definition();
    let program = format!("rhsp{{}}({})", int(1));
    let (result, coverage) = covered(&definition, &program);
    assert_eq!(
        result.leaves[0].pattern.term,
        term(&definition, &format!("val{{}}({})", int(2)))
    );
    assert_coverage(
        &coverage,
        &["rhsp", "part", "tot"],
        &["rhsp", "part", "tot"],
        &program,
    );
}

/// (c) A total function in a right-hand side is evaluated during the step when the step runs
/// with execution I/O.
#[test]
fn the_equation_of_a_right_hand_side_evaluated_with_execution_io_is_applied() {
    let definition = definition();
    let program = format!("rhst{{}}({})", int(1));
    let initial = ground(&definition, &program);
    let result = execute_with_io_state(
        &definition,
        initial,
        collecting(),
        ExecutionIoState::new(Vec::new()),
    );
    assert_eq!(
        result.leaves[0].pattern.term,
        term(&definition, &format!("val{{}}({})", int(2)))
    );
    assert_coverage(
        coverage(&result),
        &["rhst", "tot"],
        &["rhst", "tot"],
        &program,
    );
}

/// (d) An equation used in another equation's `requires`, during state simplification.
#[test]
fn an_equation_of_another_equations_requires_is_applied() {
    let definition = definition();
    let program = format!("eqreq{{}}({})", int(1));
    let (_, coverage) = covered(&definition, &program);
    assert_coverage(
        &coverage,
        &["eqreq", "outer", "inner"],
        &["eqreq", "outer", "inner"],
        &program,
    );
}

/// (e) A higher-priority rule whose `requires` is refuted is matched, not applied; the equation
/// its condition evaluated is applied.
#[test]
fn a_refuted_higher_priority_rule_is_matched_only() {
    let definition = definition();
    let program = format!("rej{{}}({})", int(5));
    let (_, coverage) = covered(&definition, &program);
    assert_coverage(
        &coverage,
        &["rej", "normR"],
        &["rejHigh", "rej", "normR"],
        &program,
    );
}

/// (f) The refuted competitor of an `owise` equation is matched only.
#[test]
fn a_refuted_competitor_of_an_owise_equation_is_matched_only() {
    let definition = definition();
    let program = format!("ow{{}}({})", int(5));
    let (_, coverage) = covered(&definition, &program);
    assert_coverage(
        &coverage,
        &["ow", "owf2", "owg"],
        &["ow", "owf1", "owf2", "owg"],
        &program,
    );
}

/// (g1) An unconditional ceil equation of an uninterpreted partial function decides whether the
/// step is defined, through the definedness analysis, and is applied either way.
#[test]
fn an_unconditional_ceil_equation_deciding_a_step_is_applied() {
    let definition = definition();
    let defined = format!("ru{{}}({})", int(1));
    let (result, coverage) = covered(&definition, &defined);
    assert!(
        matches!(halt_reasons(&result)[..], [HaltReason::Stuck]),
        "{:?}",
        halt_reasons(&result)
    );
    assert_coverage(&coverage, &["ru", "puCeil"], &["ru", "puCeil"], &defined);

    let undefined = format!("ru{{}}({})", int(-1));
    let (result, coverage) = covered(&definition, &undefined);
    assert!(
        matches!(
            halt_reasons(&result)[..],
            [HaltReason::Trivial { rule_id: Some(rule), .. }] if rule == "ru"
        ),
        "{:?}",
        halt_reasons(&result)
    );
    assert_coverage(&coverage, &["ru", "puCeil"], &["ru", "puCeil"], &undefined);
}

/// (g2) A ceil equation that discharged a rule's definedness at load is carried on the rule and
/// applied by a run that tries the rule.
#[test]
fn a_ceil_equation_that_discharged_a_rule_at_load_is_applied() {
    let definition = definition();
    let discharged_by = |label: &str| {
        definition
            .rewrite_theory()
            .values()
            .flat_map(|groups| groups.values().flatten())
            .find(|rule| rule.rule.attributes.label.as_deref() == Some(label))
            .map(|rule| (*rule.rule.computed_attributes.discharged_by).clone())
            .map(|discharge| (discharge.applied, discharge.matched))
            .expect("the rule is in the definition")
    };
    assert_eq!(discharged_by("rv"), (ids(&["pvCeil"]), ids(&["pvCeil"])));
    // `puCeil` leaves `ru` an obligation, so the load does not discharge it; `rhst` has no
    // partial symbol, so there was nothing to discharge.
    assert_eq!(discharged_by("ru"), Default::default());
    assert_eq!(discharged_by("rhst"), Default::default());
    // The discharge of `rw` decided `gateNo`'s condition (refuted) and applied `gateYes`.
    assert_eq!(
        discharged_by("rw"),
        (
            ids(&["pwCeil", "gateYes"]),
            ids(&["pwCeil", "gateYes", "gateNo"])
        )
    );

    let program = format!("rv{{}}({})", int(-1));
    let (result, coverage) = covered(&definition, &program);
    assert!(
        matches!(halt_reasons(&result)[..], [HaltReason::Stuck]),
        "{:?}",
        halt_reasons(&result)
    );
    assert_coverage(&coverage, &["rv", "pvCeil"], &["rv", "pvCeil"], &program);

    let program = format!("rw{{}}({})", int(1));
    let (_, coverage) = covered(&definition, &program);
    assert_coverage(
        &coverage,
        &["rw", "pwCeil", "gateYes"],
        &["rw", "pwCeil", "gateYes", "gateNo"],
        &program,
    );
}

/// D1: the value of one function-equation step decides the definedness of an operand that
/// `KEQUAL.ite` does not evaluate (`deferred::decide_defined`).
#[test]
fn an_equation_step_deciding_a_deferred_operand_is_applied() {
    let definition = definition();
    let program = format!("d1{{}}({})", int(5));
    let (result, coverage) = covered(&definition, &program);
    assert!(
        matches!(halt_reasons(&result)[..], [HaltReason::Stuck]),
        "{:?}",
        halt_reasons(&result)
    );
    assert_coverage(&coverage, &["d1", "pdEq"], &["d1", "pdEq"], &program);
}

/// D2: an unconditional ceil equation refutes the definedness of an operand that `KEQUAL.ite`
/// does not evaluate.
#[test]
fn a_ceil_equation_deciding_a_deferred_operand_is_applied() {
    let definition = definition();
    let program = format!("d2{{}}({})", int(-5));
    let (result, coverage) = covered(&definition, &program);
    assert!(
        halt_reasons(&result)
            .iter()
            .all(|reason| matches!(reason, HaltReason::Trivial { .. })),
        "{:?}",
        halt_reasons(&result)
    );
    assert_coverage(&coverage, &["d2", "pqCeil"], &["d2", "pqCeil"], &program);
}

/// D4: one function-equation step establishes the definedness of a symbolic operand that
/// `KEQUAL.ite` does not evaluate.
#[test]
fn a_single_equation_step_deciding_a_deferred_operand_is_applied() {
    let definition = definition();
    let initial = ground(&definition, &format!("d4{{}}({A})"));
    let result = execute(&definition, initial, collecting());
    assert!(
        matches!(halt_reasons(&result)[..], [HaltReason::Stuck]),
        "{:?}",
        halt_reasons(&result)
    );
    assert_coverage(coverage(&result), &["d4", "prEq"], &["d4", "prEq"], "d4(A)");
}

/// (g2) A conditional ceil equation, which the definedness analysis does not use, is applied by
/// the predicate simplifier on a symbolic input whose path condition holds its `requires`.
#[test]
fn a_conditional_ceil_equation_on_a_symbolic_input_is_applied() {
    let definition = definition();
    let initial = Pattern {
        term: term(&definition, &format!("rc{{}}({A})")),
        constraints: vec![Predicate::Equals(
            term(&definition, &format!("geInt{{}}({A}, {})", int(0))),
            term(&definition, TRUE),
        )],
    };
    let result = execute(&definition, initial, collecting());
    assert!(
        matches!(halt_reasons(&result)[..], [HaltReason::Stuck]),
        "{:?}",
        halt_reasons(&result)
    );
    assert_coverage(
        coverage(&result),
        &["rc", "pcCeil"],
        &["rc", "pcCeil"],
        "rc(A)",
    );
}

/// (g2) A predicate equation that decides a rule's matching-logic `requires` is applied.
#[test]
fn a_predicate_equation_is_applied() {
    let definition = definition();
    let program = format!("rp{{}}({})", int(1));
    let (result, coverage) = covered(&definition, &program);
    assert_eq!(result.leaves[0].pattern.term, term(&definition, "halt{}()"));
    assert_coverage(&coverage, &["rp", "piZero"], &["rp", "piZero"], &program);
}

/// The sets cover the whole explored tree: the rules of a path whose leaf a state-set merge
/// drops are in them, and they are the path-set run's.
#[test]
fn the_sets_cover_paths_a_state_set_merge_drops() {
    let definition = definition();
    let initial = ground(&definition, "nd{}()");
    let state_set = execute(&definition, initial.clone(), collecting());
    let path_set = execute(
        &definition,
        initial,
        ExecutionOptions {
            result_modality: ResultModality::PathSet,
            ..collecting()
        },
    );
    assert_eq!(state_set.leaves.len(), 1);
    assert_eq!(path_set.leaves.len(), 2);
    let every = ["ndA", "ndB", "mid1", "mid2"];
    assert_coverage(coverage(&state_set), &every, &every, "nd");
    assert_eq!(coverage(&state_set), coverage(&path_set));
}

/// A solver that finds every query satisfiable and decides no validity: narrowing conditions
/// are not refuted, and an unclear `requires` stays undecided.
struct SatisfiableSolver;

impl SmtSolver for SatisfiableSolver {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        Ok(Ok(Satisfiability::Sat))
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        Ok(if checked.is_empty() {
            Ok(Validity::Valid)
        } else {
            Err(SmtError::Unavailable)
        })
    }
}

/// (k) A rule matched through unification with a narrowing condition the solver does not
/// refute, whose `requires` is left undecided, is matched and not applied.
#[test]
fn a_narrowed_rule_with_an_undecided_requires_is_matched_only() {
    let definition = definition();
    let initial = ground(&definition, "nw{}(Y:SortW{})");
    let result = execute_with_solver(&definition, initial, collecting(), &SatisfiableSolver);
    assert!(
        matches!(halt_reasons(&result)[..], [HaltReason::Indeterminate(_)]),
        "{:?}",
        halt_reasons(&result)
    );
    assert_coverage(coverage(&result), &[], &["nar"], "nw(Y)");
}

/// A solver that refutes every satisfiability query: a narrowing condition ends the attempt.
struct UnsatisfiableSolver;

impl SmtSolver for UnsatisfiableSolver {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        Ok(Ok(Satisfiability::Unsat))
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        Ok(if checked.is_empty() {
            Ok(Validity::Valid)
        } else {
            Err(SmtError::Unavailable)
        })
    }
}

/// A rule whose left-hand side matched the state but whose attempt ended before its `requires`,
/// here at a narrowing condition the solver refutes, competed at the state: it is offered, and
/// in neither other list, since no condition of it was decided.
#[test]
fn a_rule_refuted_before_its_requires_is_offered_only() {
    let definition = definition();
    let initial = ground(&definition, "nw{}(Y:SortW{})");
    let options = ExecutionOptions {
        collect_offered: true,
        ..collecting()
    };
    let result = execute_with_solver(&definition, initial, options, &UnsatisfiableSolver);
    let coverage = coverage(&result);
    assert_eq!(coverage.applied, ids(&[]));
    assert_eq!(coverage.matched, ids(&[]));
    assert_eq!(coverage.offered, Some(ids(&["nar"])));
}

/// (i) A nested collection feeds the outer one; `suspend` hides what is reported inside it.
#[test]
fn a_nested_collection_feeds_the_outer_one_and_suspend_hides_reports() {
    let ((), outer) = collect(|| {
        note_applied("a");
        let ((), inner) = collect(|| {
            note_matched("b");
            note_applied("c");
            suspend(|| note_applied("hidden-inner"));
        });
        assert_eq!(inner.applied, ids(&["c"]));
        assert_eq!(inner.matched, ids(&["b", "c"]));
        suspend(|| {
            note_applied("hidden");
            note_matched("hidden");
        });
        note_matched("d");
    });
    assert_eq!(outer.applied, ids(&["a", "c"]));
    assert_eq!(outer.matched, ids(&["a", "b", "c", "d"]));
}

/// (i) A collection whose action unwinds restores the flag and the outer collection: nothing
/// the action reported reaches the outer one, and nothing is collected once every collection
/// is closed.
#[test]
fn a_collection_restores_the_state_when_its_action_unwinds() {
    let ((), outer) = collect(|| {
        note_applied("before");
        let unwound = std::panic::catch_unwind(AssertUnwindSafe(|| {
            collect(|| {
                note_applied("lost");
                panic!("unwinds");
            })
        }));
        assert!(unwound.is_err());
        note_applied("after");
        let unwound = std::panic::catch_unwind(AssertUnwindSafe(|| {
            suspend(|| panic!("unwinds"));
        }));
        assert!(unwound.is_err());
        note_matched("after-suspend");
    });
    assert_eq!(outer.applied, ids(&["after", "before"]));
    assert_eq!(outer.matched, ids(&["after", "after-suspend", "before"]));

    note_applied("outside");
    let ((), empty) = collect(|| {});
    assert_eq!(empty, RunCoverage::default());
}

/// `replay` reports each set of a stored coverage to the set it was collected in.
#[test]
fn a_replayed_coverage_feeds_each_set_it_holds() {
    let ((), stored) = collect(|| {
        note_matched("tried");
        note_applied("used");
    });
    let ((), replayed) = collect(|| replay(&stored));
    assert_eq!(replayed, stored);
    assert_eq!(replayed.applied, ids(&["used"]));
    assert_eq!(replayed.matched, ids(&["tried", "used"]));
}

/// A counting collection reports, beside the sets, how many times each id was reported to
/// `applied`: its keys are `applied`; reports under `suspend` and in an unwound collection
/// count nothing, a nested collection's counts are added when it closes, and a replay counts
/// one report of each id it replays. A collection that does not count has the same sets and no
/// counts.
#[test]
fn a_counting_collection_counts_each_report_to_applied() {
    let action = || {
        note_applied("a");
        note_applied("a");
        note_applied("b");
        note_matched("m");
        note_matched("m");
        suspend(|| note_applied("a"));
        let ((), inner) = collect(|| {
            note_applied("a");
            note_applied("c");
            note_applied("c");
        });
        assert_eq!(inner.applied_counts, None);
        let unwound = std::panic::catch_unwind(AssertUnwindSafe(|| {
            collect(|| {
                note_applied("a");
                panic!("unwinds");
            })
        }));
        assert!(unwound.is_err());
        replay(&inner);
    };
    let ((), counted) = collect_recording(false, true, false, None, action);
    assert_eq!(counted.applied, ids(&["a", "b", "c"]));
    assert_eq!(counted.matched, ids(&["a", "b", "c", "m"]));
    assert_eq!(
        counted.applied_counts,
        Some(
            [("a", 4), ("b", 1), ("c", 3)]
                .into_iter()
                .map(|(id, count)| (id.to_owned(), count))
                .collect()
        )
    );
    let ((), plain) = collect(action);
    assert_eq!(plain.applied_counts, None);
    assert_eq!(
        plain,
        RunCoverage {
            applied_counts: None,
            ..counted
        }
    );
}

/// An execution that asks for counts receives them keyed by `applied`, and asking changes
/// nothing else in the result; without `collect_counts` it receives none.
#[test]
fn an_execution_reports_counts_only_when_asked_and_asking_changes_nothing_else() {
    let definition = definition();
    let program = format!("rhsp{{}}({})", int(1));
    let initial = ground(&definition, &program);
    let mut counted = execute(
        &definition,
        initial.clone(),
        ExecutionOptions {
            collect_counts: true,
            ..collecting()
        },
    );
    let mut plain = execute(&definition, initial, collecting());
    let counted_coverage = counted
        .coverage
        .take()
        .expect("the run collected its coverage");
    let plain_coverage = plain
        .coverage
        .take()
        .expect("the run collected its coverage");
    assert_eq!(counted, plain, "asking for counts changed the result");
    assert_eq!(plain_coverage.applied_counts, None);
    let counts = counted_coverage
        .applied_counts
        .clone()
        .expect("the run counted");
    assert_eq!(
        counts.keys().cloned().collect::<BTreeSet<_>>(),
        counted_coverage.applied
    );
    assert!(counts.values().all(|count| *count >= 1));
    assert_eq!(counts["rhsp"], 1);
    assert_eq!(
        RunCoverage {
            applied_counts: None,
            ..counted_coverage
        },
        plain_coverage
    );
}

/// The offered level is collected only by a collection that offers: `note_offered` reports
/// nothing elsewhere, and an offering collection unions `matched` (with `applied`) into it.
#[test]
fn offered_is_collected_only_by_an_offering_collection() {
    let ((), plain) = collect(|| {
        note_offered("ignored");
        note_matched("m");
    });
    assert_eq!(plain.offered, None);
    let ((), offering) = collect_offering(true, || {
        note_offered("o");
        note_matched("m");
        note_applied("a");
        // A collection opened inside, such as a rule's load-time discharge, does not offer, and
        // its other sets feed the outer one.
        let ((), inner) = collect(|| {
            note_offered("inner-offered");
            note_applied("inner");
        });
        assert_eq!(inner.offered, None);
        suspend(|| note_offered("hidden"));
    });
    assert_eq!(offering.applied, ids(&["a", "inner"]));
    assert_eq!(offering.matched, ids(&["a", "inner", "m"]));
    assert_eq!(offering.offered, Some(ids(&["a", "inner", "m", "o"])));
    let ((), replayed) = collect_offering(true, || replay(&offering));
    assert_eq!(replayed, offering);
}

/// An offer's probe runs isolated from the run: it reports to no set, counts no work but one
/// `Counter::CoverageOfferMatches`, and an axiom already in a set is not probed again.
#[test]
fn an_offer_probe_is_isolated_and_runs_once_per_axiom() {
    use k_rust_kore::measure::{self, Counter};
    let before = measure::snapshot();
    let ((), coverage) = collect_offering(true, || {
        offer("hit", || {
            note_applied("leaked");
            note_matched("leaked");
            measure::bump(Counter::RewriteSteps);
            true
        });
        offer("miss", || false);
        offer("hit", || panic!("an offered axiom is not probed again"));
        note_matched("seen");
        offer("seen", || panic!("a matched axiom is not probed"));
    });
    let delta = measure::snapshot().delta(&before);
    assert_eq!(coverage.applied, ids(&[]));
    assert_eq!(coverage.matched, ids(&["seen"]));
    assert_eq!(coverage.offered, Some(ids(&["hit", "seen"])));
    assert_eq!(delta.get(Counter::RewriteSteps), 0);
    assert_eq!(delta.get(Counter::CoverageOfferMatches), 2);
    // Without an offering collection no probe runs.
    let ((), _) = collect(|| offer("never", || panic!("not offering")));
    offer("never", || panic!("no collection"));
}

/// (a) A rule of a priority group below the productive one, whose left-hand side matches the
/// state, is offered; asking for it changes nothing else in the result, under either mode.
#[test]
fn a_lower_priority_rule_is_offered_and_asking_changes_nothing_else() {
    let definition = definition();
    let program = format!("rej{{}}({})", int(5));
    for mode in [ExecutionMode::All, ExecutionMode::Any] {
        let options = ExecutionOptions {
            mode,
            ..collecting()
        };
        let mut offered = execute(
            &definition,
            ground(&definition, &program),
            ExecutionOptions {
                collect_offered: true,
                ..options.clone()
            },
        );
        let mut plain = execute(&definition, ground(&definition, &program), options);
        let levels = offered.coverage.take().unwrap();
        let without = plain.coverage.take().unwrap();
        assert_eq!(without.offered, None);
        assert_eq!(
            offered, plain,
            "{mode:?}: asking for offered changed the result"
        );
        assert_eq!(levels.applied, without.applied);
        assert_eq!(levels.matched, without.matched);
        assert_eq!(levels.applied, ids(&["normR", "rej"]), "{mode:?}");
        assert_eq!(
            levels.matched,
            ids(&["normR", "rej", "rejHigh"]),
            "{mode:?}"
        );
        assert_eq!(
            levels.offered,
            Some(ids(&["normR", "rej", "rejHigh", "rejLow"])),
            "{mode:?}"
        );
    }
}

/// Asking for `offered` changes nothing else (the probes are isolated): every program of this
/// file's definition, ground and symbolic, under both modes and both result modalities, bounded,
/// gives the same result and the same counters (but `Counter::CoverageOfferMatches`) with the
/// option on and off. `crates/k-rust/tests/offered_inertness.rs` is the same oracle over the
/// facade's fixtures and the light IMP corpus.
#[test]
fn asking_for_offered_changes_no_result_and_no_counter() {
    use k_rust_kore::measure::{self, Counter};
    let definition = definition();
    let unary = [
        "val", "load", "ens", "rhsp", "rhst", "eqreq", "rej", "ow", "ru", "rv", "rc", "rp", "d1",
        "d2", "d4", "rw", "hop",
    ];
    let mut programs = vec!["nd{}()".to_owned(), "halt{}()".to_owned()];
    for name in unary {
        for argument in [int(5), int(-1), int(0), A.to_owned()] {
            programs.push(format!("{name}{{}}({argument})"));
        }
    }
    let mut inputs = programs
        .iter()
        .map(|program| (program.clone(), term(&definition, program)))
        .collect::<Vec<_>>();
    // A state whose variable is spelled like the rules' internalized `A`: every attempt and
    // every probe of a rule over `A` renames it apart, and the observed bindings name the
    // renamed variables, so a probe that took a renamed-apart name from the run would show.
    let rule_a = crate::substitution::Substitution::from([(
        crate::term::Variable::new("A", crate::term::Sort::simple("SortInt")),
        Term::variable(crate::term::Variable::new(
            "Rule#A",
            crate::term::Sort::simple("SortInt"),
        )),
    )]);
    for name in ["hop", "rej", "ow", "d1"] {
        let program = format!("{name}{{}}({A})");
        let renamed = crate::substitution::substitute(&term(&definition, &program), &rule_a);
        inputs.push((format!("{name}(Rule#A)"), renamed));
    }
    let mut probing = 0;
    for (program, subject) in &inputs {
        let initial = Pattern {
            term: subject.clone(),
            constraints: Vec::new(),
        };
        for mode in [ExecutionMode::All, ExecutionMode::Any] {
            for result_modality in [ResultModality::PathSet, ResultModality::StateSet] {
                let options = ExecutionOptions {
                    mode,
                    result_modality,
                    max_work: Some(200),
                    max_depth: 200,
                    max_breadth: Some(16),
                    ..collecting()
                };
                let run = |offered: bool, observed: bool| {
                    let before = measure::snapshot();
                    let options = ExecutionOptions {
                        collect_offered: offered,
                        ..options.clone()
                    };
                    let result = if observed {
                        // The observed bindings name the rules' renamed-apart variables.
                        crate::rewrite::execute_observed(
                            &definition,
                            initial.clone(),
                            options,
                            &crate::transition::ObservationOptions::all(),
                        )
                    } else {
                        execute(&definition, initial.clone(), options)
                    };
                    (result, measure::snapshot().delta(&before))
                };
                for observed in [false, true] {
                    let (mut on, on_counters) = run(true, observed);
                    let (mut off, off_counters) = run(false, observed);
                    let context = format!(
                        "{program} under {mode:?} {result_modality:?}, observed {observed}"
                    );
                    let on_coverage = on.coverage.as_mut().unwrap();
                    let offered = on_coverage.offered.take().expect("offered was asked for");
                    assert!(on_coverage.matched.is_subset(&offered), "{context}");
                    probing += usize::from(offered.len() > on_coverage.matched.len());
                    assert_eq!(off.coverage.as_ref().unwrap().offered, None, "{context}");
                    off.coverage.as_mut().unwrap().offered = None;
                    assert_eq!(on, off, "{context}: offered on, then off");
                    let differing = on_counters
                        .iter()
                        .zip(off_counters.iter())
                        .filter(|((name, on), (_, off))| {
                            *name != Counter::CoverageOfferMatches.name() && on != off
                        })
                        .collect::<Vec<_>>();
                    assert!(differing.is_empty(), "{context}: counters {differing:?}");
                }
            }
        }
    }
    assert!(probing > 0, "some run offers an axiom it never tried");
}

/// The options of a run that records the condition entries of `rules`, with the default caps.
fn recording(rules: &[&str]) -> ExecutionOptions {
    ExecutionOptions {
        collect_conditions: Some(ConditionCollection::new(rules.iter().copied())),
        ..collecting()
    }
}

/// The condition records the run reported.
fn conditions(result: &ExecutionResult) -> &[RuleConditions] {
    coverage(result)
        .conditions
        .as_deref()
        .expect("the run recorded condition entries")
}

/// The one record of the one rule the run recorded.
fn only_record(result: &ExecutionResult) -> &ConditionRecord {
    let [rule] = conditions(result) else {
        panic!("{:?}", conditions(result))
    };
    let [record] = &rule.records[..] else {
        panic!("{rule:?}")
    };
    record
}

fn int_value(definition: &BackendDefinition, value: i64) -> RecordedValue {
    RecordedValue::Value(term(definition, &int(value)))
}

fn variable_a() -> Variable {
    Variable::new("A", Sort::simple("SortInt"))
}

/// An atom that reads the record's one binding, `A`.
fn atom(
    head: &str,
    hook: Option<&str>,
    operands: Vec<RecordedValue>,
    value: Truth,
) -> ConditionNode {
    ConditionNode::Atom(ConditionAtom {
        head: Some(head.to_owned()),
        hook: hook.map(str::to_owned),
        operands,
        reads: vec![0],
        value,
    })
}

/// The conjunct `\equals(child, true)` of a K `requires child`.
fn holds(child: ConditionNode) -> ConditionNode {
    let value = match child.value() {
        Truth::True => Truth::True,
        Truth::False | Truth::Undefined => Truth::False,
        Truth::Undecided => Truth::Undecided,
    };
    ConditionNode::Equals {
        literal: true,
        child: Box::new(child),
        value,
    }
}

/// G-7: the entry into a blocked rule's `requires` is recorded with the bindings of the
/// variables the condition reads, as the rule names them, the condition with every node's truth
/// (`rejHigh`'s `normR(A) <Int 0` at `A = 5` is `5 <Int 0`, false, so the conjunct is false),
/// and the attempt's verdict, refuted.
#[test]
fn a_blocked_rules_bindings_and_failing_atom_are_recorded() {
    let definition = definition();
    let initial = ground(&definition, &format!("rej{{}}({})", int(5)));
    let result = execute(&definition, initial, recording(&["rejHigh"]));
    assert_coverage(
        coverage(&result),
        &["rej", "normR"],
        &["rejHigh", "rej", "normR"],
        "rej(5)",
    );
    assert_eq!(
        conditions(&result),
        [RuleConditions {
            rule: "rejHigh".to_owned(),
            records: vec![ConditionRecord {
                bindings: vec![(variable_a(), int_value(&definition, 5))],
                condition: vec![holds(atom(
                    "ltInt",
                    Some("INT.lt"),
                    vec![int_value(&definition, 5), int_value(&definition, 0)],
                    Truth::False,
                ))],
                verdict: Some(Verdict::Refuted),
                chosen: false,
            }],
            truncated: false,
        }]
    );
}

/// A condition that holds is recorded alike, true, with the verdict held; a rule not asked for,
/// or whose condition was never entered, has no entry.
#[test]
fn a_holding_condition_is_recorded_and_unrequested_rules_are_not() {
    let definition = definition();
    let initial = ground(&definition, &format!("load{{}}({})", int(4)));
    let result = execute(&definition, initial, recording(&["load", "rejHigh", "ens"]));
    assert_eq!(
        conditions(&result),
        [RuleConditions {
            rule: "load".to_owned(),
            records: vec![ConditionRecord {
                bindings: vec![(variable_a(), int_value(&definition, 4))],
                condition: vec![holds(atom(
                    "eqInt",
                    Some("INT.eq"),
                    vec![int_value(&definition, 4), int_value(&definition, 4)],
                    Truth::True,
                ))],
                verdict: Some(Verdict::Held),
                chosen: false,
            }],
            truncated: false,
        }]
    );
}

/// A matching-logic atom of a condition (`\equals(pi(A), 0)`) is recorded with its operands and
/// its truth; an operand left as an application of a function is marked unevaluated.
#[test]
fn a_predicate_atom_is_recorded_with_its_operands() {
    let definition = definition();
    let initial = ground(&definition, &format!("rp{{}}({})", int(3)));
    let result = execute(&definition, initial, recording(&["rp"]));
    let record = only_record(&result);
    assert_eq!(
        record.condition,
        [atom(
            r"\equals",
            None,
            vec![
                RecordedValue::Unevaluated(term(&definition, &format!("pi{{}}({})", int(3)))),
                int_value(&definition, 0),
            ],
            Truth::True,
        )]
    );
    assert_eq!(record.verdict, Some(Verdict::Held));
}

/// On a symbolic state the bindings and operands are marked symbolic and the atom the
/// evaluation does not decide is undecided, as is the attempt without a solver; the rule's
/// variable is named as the rule names it, also where the attempt renamed it apart from a state
/// variable spelled like it (`Rule#A`).
#[test]
fn symbolic_values_are_marked_and_variables_named_as_written() {
    let definition = definition();
    let int_sort = Sort::simple("SortInt");
    for state_variable in ["A", "Rule#A"] {
        let subject = Term::variable(Variable::new(state_variable, int_sort));
        let program = term(&definition, &format!("rej{{}}({A})"));
        let initial = Pattern {
            term: crate::substitution::substitute(
                &program,
                &crate::substitution::Substitution::from([(
                    Variable::new("A", int_sort),
                    subject.clone(),
                )]),
            ),
            constraints: Vec::new(),
        };
        let result = execute(&definition, initial, recording(&["rejHigh"]));
        let record = only_record(&result);
        assert_eq!(
            record.bindings,
            [(variable_a(), RecordedValue::Symbolic(subject.clone()))],
            "{state_variable}"
        );
        assert_eq!(
            record.condition,
            [holds(atom(
                "ltInt",
                Some("INT.lt"),
                vec![
                    RecordedValue::Symbolic(subject.clone()),
                    int_value(&definition, 0)
                ],
                Truth::Undecided,
            ))],
            "{state_variable}"
        );
        assert_eq!(record.verdict, Some(Verdict::Undecided), "{state_variable}");
    }
}

/// A value larger than `max_value_size` nodes is omitted; the truths are still recorded.
#[test]
fn values_above_the_size_cap_are_omitted() {
    let definition = definition();
    let initial = ground(&definition, &format!("rej{{}}({})", int(5)));
    let mut options = recording(&["rejHigh"]);
    options.collect_conditions.as_mut().unwrap().max_value_size = 0;
    let result = execute(&definition, initial, options);
    let record = only_record(&result);
    assert_eq!(record.bindings, [(variable_a(), RecordedValue::Omitted)]);
    assert_eq!(
        record.condition,
        [holds(atom(
            "ltInt",
            Some("INT.lt"),
            vec![RecordedValue::Omitted, RecordedValue::Omitted],
            Truth::False,
        ))]
    );
}

/// Without `collect_conditions` the coverage has no records, and without `collect_coverage`
/// the option records nothing.
#[test]
fn conditions_are_recorded_only_when_asked_with_coverage() {
    let definition = definition();
    let initial = ground(&definition, &format!("rej{{}}({})", int(5)));
    let plain = execute(&definition, initial.clone(), collecting());
    assert_eq!(coverage(&plain).conditions, None);
    let without_coverage = execute(
        &definition,
        initial,
        ExecutionOptions {
            collect_coverage: false,
            ..recording(&["rejHigh"])
        },
    );
    assert_eq!(without_coverage.coverage, None);
}

/// The definition of the stack-stop and budget regressions: `deep(N)` recurses `N` levels, not in
/// tail position, and `state => done(0) requires deep(depth) ==Int depth`.
fn deep_definition(depth: i64) -> BackendDefinition {
    let one = int(1);
    let zero = int(0);
    let requires = |requires: &str| format!(r"\equals{{SortBool{{}}, R}}({requires}, {TRUE})");
    let source = format!(
        r#"[]
        module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            hooked-symbol subInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.sub"), smt-hook{{}}("-")]
            hooked-symbol addInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
            hooked-symbol gtInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.gt"), smt-hook{{}}(">")]
            hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.eq"), smt-hook{{}}("=")]
            symbol deep{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            sort SortS{{}} []
            symbol state{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
            symbol done{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            axiom{{R}} \implies{{R}}(
                \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, {zero}), \top{{R}}())),
                \equals{{SortInt{{}}, R}}(deep{{}}(X0:SortInt{{}}), \and{{SortInt{{}}}}({zero}, \top{{SortInt{{}}}}()))
            ) [label{{}}("deep0")]
            axiom{{R}} \implies{{R}}(
                \and{{R}}({positive}, \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, N:SortInt{{}}), \top{{R}}())),
                \equals{{SortInt{{}}, R}}(
                    deep{{}}(X0:SortInt{{}}),
                    \and{{SortInt{{}}}}(addInt{{}}(deep{{}}(subInt{{}}(N:SortInt{{}}, {one})), {one}), \top{{SortInt{{}}}}())
                )
            ) [label{{}}("deepN")]
            {advance}
        endmodule []"#,
        positive = requires(&format!("gtInt{{}}(N:SortInt{{}}, {zero})")),
        advance = rule(
            "advance",
            "state{}()",
            &format!("done{{}}({zero})"),
            &format!("eqInt{{}}(deep{{}}({}), {})", int(depth), int(depth)),
            "",
            "",
        ),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

/// Run `state` on an 8 MiB thread, with the simplifier's stack segments allowed or not, recording
/// `advance`'s entries or not, with a poll budget per record.
fn run_deep(segments: bool, record_polls: Option<u64>) -> ExecutionResult {
    run_deep_with(100_000, segments, record_polls, None)
}

/// [`run_deep`] at `depth`, with a step timeout or none.
fn run_deep_with(
    depth: i64,
    segments: bool,
    record_polls: Option<u64>,
    step_timeout: Option<std::time::Duration>,
) -> ExecutionResult {
    std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || {
            let work = || {
                let definition = deep_definition(depth);
                let initial = ground(&definition, "state{}()");
                let options = ExecutionOptions {
                    max_depth: 1,
                    step_timeout,
                    collect_conditions: record_polls.map(|polls| {
                        let mut collection = ConditionCollection::new(["advance"]);
                        collection.record_polls = polls;
                        collection
                    }),
                    ..collecting()
                };
                execute(&definition, initial, options)
            };
            if segments {
                work()
            } else {
                crate::nesting::with_simplification_stack_budget(0, work)
            }
        })
        .expect("the thread starts")
        .join()
        .expect("the run does not panic")
}

/// FZ-G7 review B1: a stop the record's own evaluation meets (here a lack of stack, with no
/// segment budget) is dismissed and reported, not dropped (which panics in a debug build), and
/// changes nothing in the run: the result is the unrecorded one, with the same stack-stop count,
/// and the record says which operand and nodes the stop left unknown and that the attempt
/// stopped.
#[test]
fn a_stop_in_a_records_evaluation_is_reported_and_changes_nothing_else() {
    let definition = deep_definition(100_000);
    let mut on = run_deep(false, Some(crate::coverage::DEFAULT_RECORD_POLLS));
    let off = run_deep(false, None);
    assert!(
        matches!(
            halt_reasons(&off)[..],
            [HaltReason::Stopped(crate::stop::StopCause::StackExhausted(
                _
            ))]
        ),
        "{:?}",
        halt_reasons(&off)
    );
    let record = only_record(&on).clone();
    assert_eq!(
        record.condition,
        [holds(ConditionNode::Atom(ConditionAtom {
            head: Some("eqInt".to_owned()),
            hook: Some("INT.eq".to_owned()),
            operands: vec![RecordedValue::Stopped, int_value(&definition, 100_000)],
            reads: Vec::new(),
            value: Truth::Undecided,
        }))]
    );
    assert_eq!(record.verdict, Some(Verdict::Stopped));
    on.coverage.as_mut().unwrap().conditions = None;
    assert_eq!(on, off);
}

/// FZ-G7 review S2: the record's evaluation runs off the run's clock and is bounded by its own
/// budget of polls, a function of its work: a budget too small to evaluate the operand leaves it
/// stopped (and, a spent budget staying spent, every later operand too) and the node undecided,
/// while the run, which the budget does not bound, decides the condition and applies the rule
/// exactly as without the record.
#[test]
fn a_records_own_budget_bounds_it_and_not_the_run() {
    let definition = deep_definition(100_000);
    let mut on = run_deep(true, Some(10));
    let off = run_deep(true, None);
    let record = only_record(&on).clone();
    assert_eq!(
        record.condition,
        [holds(ConditionNode::Atom(ConditionAtom {
            head: Some("eqInt".to_owned()),
            hook: Some("INT.eq".to_owned()),
            operands: vec![RecordedValue::Stopped, RecordedValue::Stopped],
            reads: Vec::new(),
            value: Truth::Undecided,
        }))]
    );
    assert_eq!(record.verdict, Some(Verdict::Held));
    assert!(coverage(&off).applied.contains("advance"));
    on.coverage.as_mut().unwrap().conditions = None;
    assert_eq!(on, off);
    // With the default budget the record evaluates the operand.
    let full = run_deep(true, Some(crate::coverage::DEFAULT_RECORD_POLLS));
    assert_eq!(
        only_record(&full).condition,
        [holds(ConditionNode::Atom(ConditionAtom {
            head: Some("eqInt".to_owned()),
            hook: Some("INT.eq".to_owned()),
            operands: vec![
                int_value(&definition, 100_000),
                int_value(&definition, 100_000)
            ],
            reads: Vec::new(),
            value: Truth::True,
        }))]
    );
}

/// FZ-G7 review N13: where the condition completes an incomplete match (`re(plus(A, 1))` against
/// `re(3)` leaves `A` to the condition `\equals(A, 2)`), the attempt re-enters with the binding
/// it found: its first record, without `A`, is marked re-entered, and the re-entered attempt's
/// record has `A` and the attempt's own verdict.
#[test]
fn an_entry_completed_by_its_condition_is_marked_reentered() {
    let source = format!(
        r#"[]
        module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            hooked-symbol plus{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
            sort SortS{{}} []
            symbol re{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol done{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            {rule}
        endmodule []"#,
        rule = rule(
            "reent",
            &format!("re{{}}(plus{{}}({A}, {}))", int(1)),
            &format!("done{{}}({A})"),
            &format!(r"\equals{{SortInt{{}}, SortS{{}}}}({A}, {})", int(2)),
            "",
            "",
        ),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN").expect("internalizes");
    let initial = ground(&definition, &format!("re{{}}({})", int(3)));
    // The match condition `plus(A, 1) = 3` needs a satisfiability answer before the `requires`.
    let result = execute_with_solver(
        &definition,
        initial,
        recording(&["reent"]),
        &SatisfiableSolver,
    );
    let [rule] = conditions(&result) else {
        panic!("{:?}", conditions(&result))
    };
    let verdicts = rule
        .records
        .iter()
        .map(|record| (record.bindings.len(), record.verdict))
        .collect::<Vec<_>>();
    assert_eq!(
        verdicts,
        [(0, Some(Verdict::Reentered)), (1, Some(Verdict::Held))]
    );
}

/// FZ-G7 review S2 (the reviewer's probe): with a step timeout 1.6 times the unrecorded step's
/// time, the recorded run ends as the unrecorded one does, since the record's work is not charged
/// to the step. Timing-dependent, so ignored by default; run it in an optimized build on a quiet
/// host (`a_records_own_budget_bounds_it_and_not_the_run` and the `timeout` tests check the
/// mechanism deterministically).
#[test]
#[ignore = "timing-dependent: run on a quiet host"]
fn a_step_deadline_meets_the_same_work_with_or_without_records() {
    let depth = 200_000;
    let polls = Some(crate::coverage::DEFAULT_RECORD_POLLS);
    let timed = |record_polls: Option<u64>, timeout| {
        let started = std::time::Instant::now();
        let result = run_deep_with(depth, true, record_polls, timeout);
        (result, started.elapsed())
    };
    let (_, off_time) = timed(None, None);
    let timeout = off_time.mul_f64(1.6);
    for round in 0..3 {
        let (off, _) = timed(None, Some(timeout));
        let (mut on, _) = timed(polls, Some(timeout));
        on.coverage.as_mut().unwrap().conditions = None;
        assert_eq!(
            halt_reasons(&on),
            halt_reasons(&off),
            "round {round}, timeout {timeout:?}"
        );
    }
}

/// Recording the condition entries of every rule changes nothing else in any result, on the
/// programs, modes and modalities of the offered test (renamed-apart states included), counts
/// no other work, and is deterministic: two runs record the same entries.
#[test]
fn asking_for_conditions_changes_no_result_and_no_counter() {
    use k_rust_kore::measure;
    let definition = definition();
    let rules = [
        "load", "ens", "rhsp", "rhst", "eqreq", "rejHigh", "rej", "hop", "hopLow", "rejLow", "ow",
        "ru", "rv", "rc", "rp", "ndA", "ndB", "mid1", "mid2", "nar", "d1", "d2", "d4", "rw",
    ];
    let unary = [
        "val", "load", "ens", "rhsp", "rhst", "eqreq", "rej", "ow", "ru", "rv", "rc", "rp", "d1",
        "d2", "d4", "rw", "hop",
    ];
    let mut inputs = ["nd{}()", "halt{}()"]
        .map(|program| (program.to_owned(), term(&definition, program)))
        .to_vec();
    for name in unary {
        for argument in [int(5), int(-1), int(0), A.to_owned()] {
            let program = format!("{name}{{}}({argument})");
            inputs.push((program.clone(), term(&definition, &program)));
        }
    }
    let rule_a = crate::substitution::Substitution::from([(
        Variable::new("A", Sort::simple("SortInt")),
        Term::variable(Variable::new("Rule#A", Sort::simple("SortInt"))),
    )]);
    for name in ["hop", "rej", "ow", "d1"] {
        let program = format!("{name}{{}}({A})");
        let renamed = crate::substitution::substitute(&term(&definition, &program), &rule_a);
        inputs.push((format!("{name}(Rule#A)"), renamed));
    }
    let mut recorded = 0;
    for (program, subject) in &inputs {
        let initial = Pattern {
            term: subject.clone(),
            constraints: Vec::new(),
        };
        for mode in [ExecutionMode::All, ExecutionMode::Any] {
            for result_modality in [ResultModality::PathSet, ResultModality::StateSet] {
                let options = ExecutionOptions {
                    mode,
                    result_modality,
                    max_work: Some(200),
                    max_depth: 200,
                    max_breadth: Some(16),
                    collect_offered: true,
                    ..collecting()
                };
                let run = |conditions: bool| {
                    let before = measure::snapshot();
                    let options = ExecutionOptions {
                        collect_conditions: conditions
                            .then(|| ConditionCollection::new(rules.iter().copied())),
                        ..options.clone()
                    };
                    let result = execute(&definition, initial.clone(), options);
                    (result, measure::snapshot().delta(&before))
                };
                let context = format!("{program} under {mode:?} {result_modality:?}");
                let (mut on, on_counters) = run(true);
                let (again, _) = run(true);
                assert_eq!(on, again, "{context}: two runs record alike");
                let (off, off_counters) = run(false);
                let records = on.coverage.as_mut().unwrap().conditions.take();
                let records = records.expect("conditions were asked for");
                recorded += records.iter().map(|rule| rule.records.len()).sum::<usize>();
                assert_eq!(off.coverage.as_ref().unwrap().conditions, None, "{context}");
                assert_eq!(on, off, "{context}: conditions on, then off");
                let differing = on_counters
                    .iter()
                    .zip(off_counters.iter())
                    .filter(|((_, on), (_, off))| on != off)
                    .collect::<Vec<_>>();
                assert!(differing.is_empty(), "{context}: counters {differing:?}");
            }
        }
    }
    assert!(recorded > 0, "some run records a condition entry");
}

/// A [`crate::coverage::Selection`] offers exactly the candidates its site never took: after the
/// candidate the site stopped at, in its group and the later ones, the one it gave back, and
/// none that the site's filter excludes.
#[test]
fn a_selection_offers_the_candidates_its_site_never_took() {
    use std::{collections::BTreeMap, sync::Arc};

    use crate::coverage::{Candidate, Selection, by_priority, every, offer_all};

    struct Axiom(&'static str);
    impl Candidate for Axiom {
        fn coverage_id(&self) -> &str {
            self.0
        }
    }
    let groups = BTreeMap::from([
        (10, vec![Arc::new(Axiom("a1")), Arc::new(Axiom("a2"))]),
        (20, vec![Arc::new(Axiom("b1")), Arc::new(Axiom("skip"))]),
        (30, vec![Arc::new(Axiom("c1"))]),
    ]);
    let not_skipped = |axiom: &Axiom| axiom.0 != "skip";
    let offered = |site: &dyn Fn()| {
        let ((), coverage) = collect_offering(true, site);
        coverage.offered.unwrap().into_iter().collect::<Vec<_>>()
    };
    // Stops after taking `a1`: `a2` and every later candidate are offered, `skip` is not.
    assert_eq!(
        offered(&|| {
            let selection = Selection::new(by_priority(&groups), not_skipped, |_| true);
            let (_, mut group) = selection.groups().next().unwrap();
            assert_eq!(group.next().unwrap().0, "a1");
        }),
        ["a2", "b1", "c1"]
    );
    // Exhausts the first group, takes `b1` and gives it back: `b1` and `c1` are offered.
    assert_eq!(
        offered(&|| {
            let selection = Selection::new(by_priority(&groups), not_skipped, |_| true);
            let mut groups = selection.groups();
            let (_, first) = groups.next().unwrap();
            assert_eq!(first.map(|axiom| axiom.0).collect::<Vec<_>>(), ["a1", "a2"]);
            let (_, mut second) = groups.next().unwrap();
            assert_eq!(second.next().unwrap().0, "b1");
            assert!(second.is_exhausted());
            selection.give_back();
        }),
        ["b1", "c1"]
    );
    // Takes every candidate: nothing is offered; a probe that does not match offers nothing.
    assert!(
        offered(&|| {
            let selection = Selection::new(by_priority(&groups), every, |_| true);
            for (_, group) in selection.groups() {
                group.for_each(drop);
            }
        })
        .is_empty()
    );
    assert_eq!(
        offered(&|| offer_all(by_priority(&groups), every, |axiom: &Axiom| axiom.0 != "a2")),
        ["a1", "b1", "c1", "skip"]
    );
    // Without an offering collection no probe runs.
    let probed = std::cell::Cell::new(false);
    offer_all(by_priority(&groups), every, |_: &Axiom| {
        probed.set(true);
        true
    });
    assert!(!probed.get());
}

/// Every site of the backend that selects candidates by priority group
/// (`rule::applicable_groups`, `rule::applicable_rewrite_groups`,
/// `BackendDefinition::predicate_equations_for`) or scans a group (`scan::scan_group`) takes its
/// candidates from a `coverage::Selection` or offers them with `coverage::offer_all` in the same
/// function, so that a site that stops early offers what it never tried. The sites that are not
/// part of a run are listed with the reason.
#[test]
fn every_priority_group_selection_offers_what_it_never_tries() {
    use std::path::Path;

    /// Functions that select by priority group outside every run, or that define the selection.
    const OUTSIDE_RUNS: &[(&str, &str)] = &[
        // The definitions of the selections themselves.
        ("rule.rs", "applicable_groups"),
        ("rule.rs", "applicable_rewrite_groups"),
        ("definition.rs", "predicate_equations_for"),
        // Reads the depth of the left-hand sides of a connective's equations; tries none.
        ("simplify.rs", "written_predicate"),
        ("simplify/scan.rs", "scan_group"),
        // The load-time confluence check, which no run's coverage includes.
        ("confluence/join.rs", "*"),
        // The data judgement's ground-instance search (`data_term::DataHeads`), an analysis of
        // the definition that no run's coverage includes: it asks whether an application is
        // stuck, and applies nothing.
        ("data_term/instance.rs", "stuck"),
        // The former lazy step, a differential-test oracle compiled only in tests.
        ("rewrite/step.rs", "rewrite_step_all_first_group_for_tests"),
    ];
    const CALLS: &[&str] = &[
        "applicable_groups(",
        "applicable_rewrite_groups(",
        "predicate_equations_for(",
        "scan_group(",
    ];

    fn sources(directory: &Path, root: &Path, into: &mut Vec<(String, String)>) {
        for entry in std::fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                if path.file_name().is_some_and(|name| name != "tests") {
                    sources(&path, root, into);
                }
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                let relative = path
                    .strip_prefix(root)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned();
                into.push((relative, std::fs::read_to_string(&path).unwrap()));
            }
        }
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    sources(&root, &root, &mut files);

    let mut sites = 0;
    let mut missing = Vec::new();
    for (file, text) in &files {
        let lines = text.lines().collect::<Vec<_>>();
        // A file's test module ends its production code.
        let test_module = lines
            .iter()
            .position(|line| line.starts_with("mod tests {"))
            .unwrap_or(lines.len());
        for (number, line) in lines[..test_module].iter().enumerate() {
            let code = line.split("//").next().unwrap_or("");
            if !CALLS.iter().any(|call| code.contains(call)) || code.contains("fn ") {
                continue;
            }
            // The enclosing function: the nearest line above that opens one, and the line
            // closing it at the same indentation.
            let start = (0..=number)
                .rev()
                .find(|&index| {
                    let trimmed = lines[index].trim_start();
                    trimmed.starts_with("fn ")
                        || trimmed.starts_with("pub fn ")
                        || trimmed.starts_with("pub(crate) fn ")
                        || trimmed.starts_with("pub(super) fn ")
                })
                .unwrap_or_else(|| panic!("{file}:{}: no enclosing function", number + 1));
            let indent = lines[start].len() - lines[start].trim_start().len();
            let close = format!("{}}}", " ".repeat(indent));
            let finish = (number..lines.len())
                .find(|&index| lines[index] == close)
                .unwrap_or(lines.len());
            let name = lines[start]
                .trim_start()
                .split("fn ")
                .nth(1)
                .unwrap()
                .split(['(', '<'])
                .next()
                .unwrap()
                .to_owned();
            if OUTSIDE_RUNS.iter().any(|(outside, function)| {
                outside == file && (*function == "*" || *function == name)
            }) {
                continue;
            }
            sites += 1;
            let body = lines[start..finish].join("\n");
            if !body.contains("Selection::new(") && !body.contains("offer_all(") {
                missing.push(format!("{file}:{} in {name}", number + 1));
            }
        }
    }
    assert!(
        missing.is_empty(),
        "a priority group selection that offers nothing: {missing:?}"
    );
    // The sites: the term scans, the ceil and predicate scans, the `\top` lemmas, the
    // definedness analysis, the two deferred decisions, the three rewrite steps and the
    // re-selection of the lower groups.
    eprintln!("{sites} priority group selections in runs");
    assert!(sites >= 12, "{sites} sites found");
}
