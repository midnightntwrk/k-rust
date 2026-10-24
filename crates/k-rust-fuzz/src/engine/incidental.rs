//! Incidental findings (FZ-INCIDENTAL): which leaf of a `stuck` or `undefined` case shows its
//! class, and the item at the head of that leaf's `<k>` cell. The loop keeps the first case of
//! each class ([`crate::report::Incidentals`]); the runner describes it from the results it
//! already has, so no case is run again.

use k_rust::{kast::identifier::decode_label, kore::ast::Pattern as KorePattern};

use crate::{
    exec::{CaseResult, LeafReport, OutcomeClass},
    values::TextSyntax,
};

use k_rust::backend::HaltReasonOutput;

/// The KORE name of the `<k>` cell's symbol.
const K_CELL: &str = "Lbl'-LT-'k'-GT-'";

/// Whether `leaf` contributes the class `class` to its case ([`crate::exec::classify`], "the
/// class of one leaf") when it reaches no target: for `stuck`, a clean `stuck` leaf whose natural
/// end is decided and false (an abnormal stop); for `undefined`, an undefined step (`trivial`)
/// unclean by its halt alone. A case of either class has such a leaf and no leaf of higher
/// precedence, and none of its leaves reaches the target (a reaching leaf is a hit,
/// `reached-unfinished` or `unsupported`, all of higher precedence).
pub(crate) fn shows(leaf: &LeafReport, class: OutcomeClass) -> bool {
    match class {
        OutcomeClass::Stuck => {
            leaf.halt == HaltReasonOutput::Stuck
                && leaf.is_clean()
                && !leaf.natural_end_undecided()
                && !leaf.natural_end
        }
        OutcomeClass::Undefined => {
            leaf.halt == HaltReasonOutput::Trivial && !leaf.unclean_beyond_halt()
        }
        _ => false,
    }
}

/// The index of the first leaf of `result` that shows `class` ([`shows`]).
pub(crate) fn leaf_of(result: &CaseResult, class: OutcomeClass) -> Option<usize> {
    result.leaves.iter().position(|leaf| shows(leaf, class))
}

/// The first item of the first `<k>` cell of `state` (in preorder) that holds a K sequence
/// `kseq(item, rest)`, below its injections: as one line of K text when `text` prints it, else
/// as the K label of its head symbol, else as KORE text. `None` when no `<k>` cell holds an
/// item.
pub(crate) fn k_head(state: &KorePattern, text: Option<&TextSyntax>) -> Option<String> {
    let item = first_k_item(state)?;
    text.and_then(|syntax| syntax.show(item))
        .or_else(|| head_label(item))
        .or_else(|| Some(item.to_string()))
}

/// The item [`k_head`] names.
fn first_k_item(pattern: &KorePattern) -> Option<&KorePattern> {
    let KorePattern::Application { symbol, arguments } = pattern else {
        return None;
    };
    if symbol.name == K_CELL {
        return match arguments.as_slice() {
            [KorePattern::Application { symbol, arguments }] if symbol.name == "kseq" => {
                arguments.first().map(below_injections)
            }
            _ => None,
        };
    }
    arguments.iter().find_map(first_k_item)
}

/// `pattern` without the injections around it.
fn below_injections(mut pattern: &KorePattern) -> &KorePattern {
    while let KorePattern::Application { symbol, arguments } = pattern
        && symbol.name == "inj"
        && let [inner] = arguments.as_slice()
    {
        pattern = inner;
    }
    pattern
}

/// The K label of `pattern`'s head symbol, when it is an application.
fn head_label(pattern: &KorePattern) -> Option<String> {
    match pattern {
        KorePattern::Application { symbol, .. } => decode_label(&symbol.name).ok(),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use k_rust::kore::parser::parse_pattern;

    use super::*;

    fn pattern(text: &str) -> KorePattern {
        parse_pattern(text).expect("test KORE parses")
    }

    #[test]
    fn the_head_is_the_first_item_of_the_first_cell_that_holds_one() {
        // Two threads: the first `<k>` is empty (a finished thread), the second holds
        // `foo(1) ~> .K` below an injection.
        let state = pattern(
            r#"Lbl'-LT-'threads'-GT-'{}(Lbl'-LT-'k'-GT-'{}(dotk{}()), Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortFoo{}, SortKItem{}}(Lblfoo{}(\dv{SortInt{}}("1"))), dotk{}())))"#,
        );
        assert_eq!(k_head(&state, None).as_deref(), Some("foo"));
        // No cell holds an item.
        let finished = pattern(r"Lbl'-LT-'k'-GT-'{}(dotk{}())");
        assert_eq!(k_head(&finished, None), None);
        // A configuration without a `<k>` cell.
        assert_eq!(k_head(&pattern(r"Lblbar{}()"), None), None);
    }
}
