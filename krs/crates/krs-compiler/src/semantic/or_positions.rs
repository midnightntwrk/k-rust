//! Where an `A | B` or-pattern (K's `#Or`) may not stand in a pattern that
//! the compiled definition reads as an equation (KF-030).
//!
//! An equation `f(P) => R` defines `f` by matching its arguments, and an
//! or-pattern anywhere in an argument means one equation per alternative: a
//! symbol distributes over `#Or` (`f(g(A | B))` is `f(g(A) | g(B))`), and so
//! does an alias (`x @ (A | B)` is `(x @ A) | (x @ B)`), and the definition
//! compiler builds those equations. The same holds for a function context
//! cell, which is one more argument of the function, and for a
//! `k::matches!(t, P)` pattern, which K tests with a generated function whose
//! one equation matches `P`.
//!
//! A simplification is different: its left-hand side is matched as one term,
//! not through argument binders, so `krs build` refuses an or-pattern there.
//! This check refuses it first, with the rewrite that keeps one term per
//! simplification.

use krs_ir::SentenceKind;
use krs_ir_levels::{RuleBodyRef, SemanticModule, SemanticRule, SemanticTerm, SemanticTermKind};

use super::error::DescriptorLoweringError;

/// Refuses an or-pattern where the definition compiler does not read it.
pub(super) fn check_or_pattern_positions(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        if let Some(node) = simplification_or(rule) {
            return Err(DescriptorLoweringError::InvalidPatternOr {
                item: Box::new(rule.id().clone()),
                reason: SIMPLIFICATION.to_owned(),
                range: node.origin().origin().exact_authored_range().map(Box::new),
            });
        }
    }
    Ok(())
}

const SIMPLIFICATION: &str = "a simplification rewrites one term, and an or-pattern in its left-hand side is not one; write one simplification per alternative";

/// The first or-pattern of a simplification's left-hand side.
fn simplification_or(rule: &SemanticRule) -> Option<&SemanticTerm> {
    if rule.kind() != SentenceKind::Simplification {
        return None;
    }
    pre_patterns(rule.relational_body())
        .into_iter()
        .find_map(first_or)
}

/// The first or-pattern at or below `term`, in preorder.
fn first_or(term: &SemanticTerm) -> Option<&SemanticTerm> {
    if matches!(term.kind(), SemanticTermKind::Or { .. }) {
        return Some(term);
    }
    term.children().into_iter().find_map(first_or)
}

fn pre_patterns(body: RuleBodyRef<'_, krs_ir_levels::SemanticLevel>) -> Vec<&SemanticTerm> {
    match body {
        RuleBodyRef::Term(body) => vec![body.from()],
        RuleBodyRef::Predicate(body) => body.lhs().terms(),
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .iter()
            .filter_map(krs_ir::ClausePart::pre_term)
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use krs_ir::{
        ApplicationRef, AtLeastTwo, BuiltinSort, ItemKind, NodeOrigin, PackageId, SourceMapKey,
        StableItemId,
    };
    use krs_ir_levels::{SemanticSortRef, SemanticTerm};

    use super::first_or;

    const K: SemanticSortRef = SemanticSortRef::Builtin(BuiltinSort::KSequence);

    fn origin() -> NodeOrigin {
        NodeOrigin::new(
            SourceMapKey::new("sem.or-positions").unwrap(),
            krs_ir::testing::authored(0, 1),
        )
    }

    fn constructor(name: &str, arguments: Vec<SemanticTerm>) -> SemanticTerm {
        SemanticTerm::application(
            origin(),
            K,
            ApplicationRef::Declared(
                StableItemId::new(
                    PackageId::new("OR-POSITIONS", "or-positions", "0.1.0", "test").unwrap(),
                    ["fixture"],
                    name,
                    ItemKind::Constructor,
                    "",
                )
                .unwrap(),
            ),
            arguments,
        )
    }

    #[test]
    fn an_or_pattern_below_a_symbol_is_found() {
        let alternatives = SemanticTerm::pattern_or(
            origin(),
            K,
            AtLeastTwo::try_from(vec![
                constructor("red", vec![]),
                constructor("green", vec![]),
            ])
            .unwrap(),
        );
        let term = constructor("color", vec![alternatives]);
        assert!(first_or(&term).is_some());
        assert!(first_or(&constructor("color", vec![constructor("red", vec![])])).is_none());
    }
}
