//! The nodes that enclose a failed validation walk.
//!
//! The term walks fail with errors whose shapes their callers match exactly, and those errors
//! carry no location. A walk knows the node it was visiting, and the boundary that turns a
//! failure into a diagnostic needs it, so [`record`] runs a validation with a chain installed for
//! the current thread: each walk of a node that fails appends the node, so the chain lists the
//! nodes that enclose the failure innermost first, and the boundary takes the first that has an
//! exact authored range. A walk that succeeds discards what the walks inside it appended, so a
//! failure that was recovered from leaves nothing behind. Outside `record`, nothing is kept.

use std::cell::RefCell;

use crate::ProvenanceKey;

thread_local! {
    /// One chain per recording in progress, innermost node first.
    static SITES: RefCell<Vec<Vec<ProvenanceKey>>> = const { RefCell::new(Vec::new()) };
}

/// Pops the chain [`record`] pushed, also when the validation unwinds.
struct Installed;

impl Drop for Installed {
    fn drop(&mut self) {
        SITES.with(|sites| sites.borrow_mut().pop());
    }
}

/// Runs `validate` and returns its result with the nodes that enclose its failure, innermost
/// first; empty on success.
pub(crate) fn record<T, E>(
    validate: impl FnOnce() -> Result<T, E>,
) -> (Result<T, E>, Vec<ProvenanceKey>) {
    SITES.with(|sites| sites.borrow_mut().push(Vec::new()));
    let installed = Installed;
    let result = validate();
    let chain = SITES.with(|sites| sites.borrow_mut().last_mut().map(std::mem::take));
    drop(installed);
    let chain = if result.is_err() {
        chain.unwrap_or_default()
    } else {
        Vec::new()
    };
    (result, chain)
}

/// Where a walk of one node began in the current recording's chain.
#[derive(Clone, Copy)]
pub(crate) struct Mark(usize);

/// Marks the start of a walk of one node.
pub(crate) fn enter() -> Mark {
    Mark(SITES.with(|sites| sites.borrow().last().map_or(0, Vec::len)))
}

/// Ends the walk begun at `mark`. A failed walk appends its node to the chain, after the nodes
/// inside it that failed first; a walk that succeeded discards whatever nodes inside it
/// reported, so a failure something inside recovered from leaves no site behind.
pub(crate) fn leave(mark: Mark, failed: bool, key: &ProvenanceKey) {
    SITES.with(|sites| {
        if let Some(chain) = sites.borrow_mut().last_mut() {
            if failed {
                chain.push(key.clone());
            } else {
                chain.truncate(mark.0);
            }
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ProvenanceRole;

    fn walk(key: &ProvenanceKey, result: Result<(), ()>) -> Result<(), ()> {
        let mark = enter();
        leave(mark, result.is_err(), key);
        result
    }

    #[test]
    fn a_failed_walk_lists_its_enclosing_nodes_and_a_recovered_one_none() {
        let inner = ProvenanceKey::new(ProvenanceRole::RulePattern, 1);
        let outer = ProvenanceKey::new(ProvenanceRole::RulePattern, 0);
        let (result, chain) = record(|| {
            let mark = enter();
            let failed = walk(&inner, Err(()));
            leave(mark, failed.is_err(), &outer);
            failed
        });
        assert_eq!(
            (result, chain),
            (Err(()), vec![inner.clone(), outer.clone()])
        );
        // A probe that fails inside a walk that then succeeds leaves no site.
        let (result, chain) = record(|| {
            let mark = enter();
            let _ = walk(&inner, Err(()));
            leave(mark, false, &outer);
            Err::<(), _>(())
        });
        assert_eq!((result, chain), (Err(()), Vec::new()));
    }
}
