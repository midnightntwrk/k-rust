//! Whole-theory checks of hand-written heating and cooling rules (KF-014).
//!
//! `#[k::rule(heat, hole = h)]` and `#[k::rule(cool, hole = h)]` are K's
//! `[heat]` and `[cool]` rules, whose binder `h` K names `HOLE`. K adds
//! `requires notBool isKResult(HOLE)` to a heating rule and
//! `requires isKResult(HOLE)` to a cooling rule, so the hole must be matched
//! by the left side, exactly once: the condition is about that one subterm.

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
                krs_ir::EvaluationKind::Cool => format!("requires is{result}(HOLE)"),
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

/// How often the left side of `rule` binds `hole`.
fn left_occurrences(rule: &SemanticRule, hole: &krs_ir::SemanticId) -> usize {
    match rule.relational_body() {
        RuleBodyRef::Term(body) => occurrences(body.from(), hole),
        RuleBodyRef::Configuration { body, .. } => body
            .clauses()
            .iter()
            .map(|clause| occurrences(&clause.before().pre_pattern(), hole))
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
