//! A builtin `List` pattern holds at most one part whose length it leaves
//! open.
//!
//! K's `List` is a sequence under the associative concatenation `_List_`, so
//! a `List` pattern is a sequence of parts: `ListItem(p)` matches one
//! element, and any other part (a variable, `_`, or another list term)
//! matches a run of elements whose length the pattern does not fix. With at
//! most one such part, the pattern's fixed elements sit at the list's two
//! ends and the length of the list fixes the open part's: the pattern
//! matches a list in at most one way. With two, the elements between them
//! may sit at several places (`Left ListItem(V) Right` matches an
//! `n`-element list in `n` ways), so the pattern does not denote one match,
//! and applying the sentence would have to choose one. This check refuses
//! such a pattern in the sentences that are applied by matching their
//! left-hand side: rules, equations, and simplifications. A claim's
//! left-hand side is a symbolic state, not a pattern applied to one, and is
//! not checked.

use krs_ir::SentenceKind;
use krs_ir_levels::{
    IrTermKind, ListOperands, RuleBodyRef, SemanticModule, SemanticRule, SemanticTerm,
};

use super::error::DescriptorLoweringError;

/// Refuses a `List` pattern with two or more open parts.
pub(super) fn check_list_patterns(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        if !matches!(
            rule.kind(),
            SentenceKind::Transition | SentenceKind::Equation | SentenceKind::Simplification
        ) {
            continue;
        }
        if let Some((node, open)) = patterns(rule).into_iter().find_map(ambiguous_list) {
            return Err(DescriptorLoweringError::AmbiguousListPattern {
                item: Box::new(rule.id().clone()),
                reason: format!(
                    "this `List` pattern has {open} parts that are not single elements, but a `List` pattern holds at most one: with two, such as `Left ListItem(V) Right`, the elements between them could sit at several places in the list, so the pattern matches a list in several ways and does not say which; match one rest and the elements before and after it, as in `[a, .., z]`"
                ),
                range: node.origin().origin().exact_authored_range().map(Box::new),
            });
        }
    }
    Ok(())
}

/// The patterns a sentence is applied by: its left-hand side and its
/// function context's cell patterns.
fn patterns(rule: &SemanticRule) -> Vec<&SemanticTerm> {
    let mut patterns = match rule.relational_body() {
        RuleBodyRef::Term(body) => vec![body.from()],
        RuleBodyRef::Predicate(body) => body.lhs().terms(),
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .iter()
            .filter_map(krs_ir::ClausePart::pre_term)
            .collect(),
    };
    if let Some(context) = rule.function_context() {
        patterns.extend(
            context
                .cells()
                .cells()
                .iter()
                .map(krs_ir::FixedCellPattern::pattern),
        );
    }
    patterns
}

/// The first `List` concatenation at or below `pattern`, in preorder, whose
/// parts include two or more that are not single elements, with their
/// number. A concatenation's parts are read through the concatenations it
/// is made of, since `_List_` is associative.
fn ambiguous_list(pattern: &SemanticTerm) -> Option<(&SemanticTerm, usize)> {
    let mut pending = vec![pattern];
    while let Some(term) = pending.pop() {
        if !is_concat(term) {
            pending.extend(term.children().into_iter().rev());
            continue;
        }
        let parts = concatenated(term);
        let open = parts
            .iter()
            .filter(|part| {
                !matches!(
                    part.kind(),
                    IrTermKind::List(operands)
                        if matches!(**operands, ListOperands::Item { .. } | ListOperands::Empty)
                )
            })
            .count();
        if open >= 2 {
            return Some((term, open));
        }
        for part in parts.into_iter().rev() {
            pending.extend(part.children().into_iter().rev());
        }
    }
    None
}

fn is_concat(term: &SemanticTerm) -> bool {
    matches!(
        term.kind(),
        IrTermKind::List(operands) if matches!(**operands, ListOperands::Concat { .. })
    )
}

/// The parts of a concatenation, left to right, through nested
/// concatenations.
fn concatenated(term: &SemanticTerm) -> Vec<&SemanticTerm> {
    let mut parts = Vec::new();
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        match term.kind() {
            IrTermKind::List(operands) => match &**operands {
                ListOperands::Concat { left, right } => {
                    pending.push(right);
                    pending.push(left);
                }
                _ => parts.push(term),
            },
            _ => parts.push(term),
        }
    }
    parts
}
