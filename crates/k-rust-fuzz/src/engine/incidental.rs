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

/// The first item of each `<k>` cell of `state` that holds a K sequence `kseq(item, rest)`, in
/// preorder, below its injections: each as one line of K text when `text` prints it, else as
/// the K label of its head symbol, else as KORE text. Under the every-`<k>` normal end a stuck
/// configuration is stuck in every thread, so every such item is where a thread stopped.
pub(crate) fn k_heads(state: &KorePattern, text: Option<&TextSyntax>) -> Vec<String> {
    let mut items = Vec::new();
    k_items(state, &mut items);
    items
        .into_iter()
        .map(|item| {
            text.and_then(|syntax| syntax.show(item))
                .or_else(|| head_label(item))
                .unwrap_or_else(|| item.to_string())
        })
        .collect()
}

/// Push the items [`k_heads`] names, in preorder, not descending into a `<k>` cell.
fn k_items<'a>(pattern: &'a KorePattern, items: &mut Vec<&'a KorePattern>) {
    let KorePattern::Application { symbol, arguments } = pattern else {
        return;
    };
    if symbol.name == K_CELL {
        if let [KorePattern::Application { symbol, arguments }] = arguments.as_slice()
            && symbol.name == "kseq"
            && let Some(item) = arguments.first()
        {
            items.push(below_injections(item));
        }
        return;
    }
    for argument in arguments {
        k_items(argument, items);
    }
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
    fn the_heads_are_the_first_items_of_every_cell_that_holds_one() {
        // Three threads: the first `<k>` holds `bar() ~> .K`, the second is empty (a finished
        // thread), the third holds `foo(1) ~> .K` below an injection.
        let state = pattern(
            r#"Lbl'-LT-'threads'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(Lblbar{}(), dotk{}())), Lbl'-LT-'k'-GT-'{}(dotk{}()), Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortFoo{}, SortKItem{}}(Lblfoo{}(\dv{SortInt{}}("1"))), dotk{}())))"#,
        );
        assert_eq!(k_heads(&state, None), vec!["bar", "foo"]);
        // No cell holds an item.
        let finished = pattern(r"Lbl'-LT-'k'-GT-'{}(dotk{}())");
        assert!(k_heads(&finished, None).is_empty());
        // A configuration without a `<k>` cell.
        assert!(k_heads(&pattern(r"Lblbar{}()"), None).is_empty());
    }
}
