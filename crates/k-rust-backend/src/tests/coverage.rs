//! Run coverage (`crate::coverage`): an execution that asks for it reports every rule and
//! equation it applied, wherever the backend applied it, and every one whose condition it began
//! to decide for a matched instance.
//!
//! The axioms carry labels and no `UNIQUE_ID`, so each one's id is its label.

use std::{collections::BTreeSet, panic::AssertUnwindSafe};

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    coverage::{
        RunCoverage, collect, collect_offering, note_applied, note_matched, note_offered, offer,
        replay, suspend,
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
    term::Term,
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
            .map(|rule| rule.rule.computed_attributes.discharged_by.clone())
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
