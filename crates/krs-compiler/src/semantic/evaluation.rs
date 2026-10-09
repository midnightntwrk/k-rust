//! Whole-theory checks of hand-written heating and cooling rules (KF-014)
//! and of contexts (KF-021).
//!
//! `#[k::rule(heat, hole = h)]` and `#[k::rule(cool, hole = h)]` are K's
//! `[heat]` and `[cool]` rules, whose binder `h` K names `HOLE`. K adds
//! `requires notBool isKResult(HOLE)` to a heating rule and
//! `requires isKResult(HOLE)` to a cooling rule, so the hole must be matched
//! by the left side, exactly once: the condition is about that one subterm.
//!
//! `#[k::context(hole = h)]` is K's `context`, which K turns into a heat rule
//! and a cool rule: its hole occurs once, and a rewrite of it is
//! `HOLE => term-containing-HOLE`.

use krs_ir::SourceRange;
use krs_ir_levels::{IrTermKind, RuleBodyRef, SemanticModule, SemanticRule, SemanticTerm};

use super::error::DescriptorLoweringError;
use super::overload::sort_name;

/// Checks that every heat or cool rule binds its hole once on its left side.
pub(super) fn check_evaluation_steps(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        let Some(step) = rule.evaluation() else {
            continue;
        };
        if step.kind() == krs_ir::EvaluationKind::Context {
            check_context(rule, step)?;
            continue;
        }
        let hole = step.hole();
        let occurrences = left_occurrences(rule, hole);
        let attribute = step.kind().as_str();
        let range = step.hole_origin().origin().exact_authored_range();
        if occurrences == 0 {
            let result = step
                .result()
                .map_or_else(|| "KResult".to_owned(), |result| sort_name(result.sort()));
            let condition = match step.kind() {
                krs_ir::EvaluationKind::Heat => format!("requires notBool is{result}(HOLE)"),
                krs_ir::EvaluationKind::Cool | krs_ir::EvaluationKind::Context => {
                    format!("requires is{result}(HOLE)")
                }
            };
            return Err(fail(
                format!(
                    "a {attribute} rule must match its hole on the left side; K adds '{condition}', a condition on that subterm, and `{}` does not occur there",
                    hole.as_str(),
                ),
                range,
            ));
        }
        if occurrences > 1 {
            return Err(fail(
                format!(
                    "the hole `{}` of a {attribute} rule names one subterm, but the left side binds it {occurrences} times; bind the other occurrences with another name",
                    hole.as_str(),
                ),
                range,
            ));
        }
    }
    Ok(())
}

/// Checks a context (KF-021): its hole occurs exactly once in its left
/// image, and its one rewrite, if any, is `HOLE => term-containing-HOLE`.
fn check_context(
    rule: &SemanticRule,
    step: &krs_ir_levels::SemanticEvaluationStep,
) -> Result<(), DescriptorLoweringError> {
    let hole = step.hole();
    let range = step.hole_origin().origin().exact_authored_range();
    match left_occurrences(rule, hole) {
        0 => {
            return Err(context_error(
                format!(
                    "a context names the subterm K evaluates with `hole = {0}`, but `{0}` does not occur in its pattern; K requires exactly one HOLE",
                    hole.as_str(),
                ),
                range,
            ));
        }
        1 => {}
        occurrences => {
            return Err(context_error(
                format!(
                    "the hole `{}` of a context names one subterm, but the pattern binds it {occurrences} times; bind the other occurrences with another name",
                    hole.as_str(),
                ),
                range,
            ));
        }
    }
    let mut rewrites = Vec::new();
    match rule.relational_body() {
        RuleBodyRef::Term(body) => {
            if let Some(local) = body.local_term() {
                collect_rewrites(local, &mut rewrites);
            }
        }
        RuleBodyRef::Configuration { body, .. } => {
            for clause in body.fixed_clauses() {
                collect_rewrites(clause.before(), &mut rewrites);
            }
        }
        // A predicate simplification (KF-039) holds no object rewrite.
        RuleBodyRef::Predicate(_) => {}
    }
    for (from, to) in rewrites {
        let from_is_hole = matches!(
            from.kind(),
            IrTermKind::Variable { variable } if variable == hole
        );
        if !from_is_hole || occurrences(to, hole) == 0 {
            return Err(context_error(
                format!(
                    "a context may rewrite only its hole, to a term that contains it: K requires HOLE => term-containing-HOLE, here `k::rewrite!({0} => f({0}))`",
                    hole.as_str(),
                ),
                from.origin().origin().exact_authored_range(),
            ));
        }
    }
    Ok(())
}

/// The `(from, to)` sides of every rewrite at or below `term`.
fn collect_rewrites<'a>(
    term: &'a SemanticTerm,
    output: &mut Vec<(&'a SemanticTerm, &'a SemanticTerm)>,
) {
    if let IrTermKind::Rewrite { from, to } = term.kind() {
        output.push((from, to));
    }
    for child in term.children() {
        collect_rewrites(child, output);
    }
}

/// Whether `term` mentions the variable `name`.
pub(super) fn mentions(term: &SemanticTerm, name: &krs_ir::SemanticId) -> bool {
    occurrences(term, name) > 0
}

/// The diagnostic for HOLE or HERE outside the computation cell (KF-021).
pub(super) fn outside_computation_cell(
    binder: &str,
    name: &str,
    cell: &str,
    range: Option<SourceRange>,
) -> DescriptorLoweringError {
    context_error(
        format!(
            "{binder} `{name}` lies in the `{cell}` cell, but heating moves the hole to the front of k; constrain other cells, but put the hole in k"
        ),
        range,
    )
}

pub(super) fn context_error(reason: String, range: Option<SourceRange>) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidContext {
        reason,
        range: range.map(Box::new),
    }
}

/// How often the left side of `rule` binds `hole`.
fn left_occurrences(rule: &SemanticRule, hole: &krs_ir::SemanticId) -> usize {
    match rule.relational_body() {
        RuleBodyRef::Term(body) => occurrences(body.from(), hole),
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .iter()
            .filter_map(krs_ir::ClausePart::pre_term)
            .map(|term| occurrences(&term.pre_pattern(), hole))
            .sum(),
        // A predicate simplification (KF-039) binds no object term.
        RuleBodyRef::Predicate(_) => 0,
    }
}

fn occurrences(term: &SemanticTerm, hole: &krs_ir::SemanticId) -> usize {
    let own = usize::from(matches!(
        term.kind(),
        IrTermKind::Variable { variable } if variable == hole
    ));
    own + term
        .children()
        .into_iter()
        .map(|child| occurrences(child, hole))
        .sum::<usize>()
}

fn fail(reason: String, range: Option<SourceRange>) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidEvaluationStep {
        reason,
        range: range.map(Box::new),
    }
}
