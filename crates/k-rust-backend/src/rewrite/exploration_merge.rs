//! The merge table of a state-set execution: the states of each depth whose expansion
//! completed, so that an equal state arriving later at that depth is merged instead of expanded.
//!
//! After term simplification a state's subtree depends only on its pattern up to a renaming of
//! the variables the request does not name (`RequestNames::state_key`), its kind, its depth, its
//! console cursor and console availability, and the options; its leaves also report the path's
//! committed effects, console transcript and diagnostics. So an arriving state whose depth and
//! key equal a recorded state's, whose effects and console are observed alike, whose console
//! availability is the same, and whose diagnostics are among the recorded state's, would yield
//! leaves each equal to a leaf of the recorded state's subtree in configuration, depth, halt
//! reason, effects and console, with no diagnostic the other lacks: the final merge would absorb
//! every one of them. Its expansion is skipped.
//!
//! The table is used under depth-first exploration: `pending`'s depths do not increase from front
//! to back, so no state can later arrive at a depth below the back of `pending`, and those depths
//! are evicted ([`ExplorationMerge::evict_below`]).

use std::collections::{BTreeMap, HashMap};

use crate::{
    diagnostic::PathDiagnostics,
    transition::{EffectJournal, ExecutionIoState},
};

use super::Pattern;

/// What an arriving state is compared on, beside its depth and key.
pub(super) struct Arrival {
    pub(super) depth: u64,
    pub(super) key: Pattern,
    pub(super) effects: EffectJournal,
    pub(super) io: ExecutionIoState,
    pub(super) io_enabled: bool,
    pub(super) diagnostics: PathDiagnostics,
}

/// A recorded state: the parts of an [`Arrival`] that its subtree's leaves report.
struct Recorded {
    effects: EffectJournal,
    io: ExecutionIoState,
    io_enabled: bool,
    diagnostics: PathDiagnostics,
}

impl Recorded {
    /// Whether every leaf `arrival`'s subtree would yield is a leaf of this state's subtree.
    /// The fingerprints decide most comparisons in constant time; equal fingerprints are
    /// confirmed on the sequences, which stop where the two paths share their history.
    fn absorbs(&self, arrival: &Arrival) -> bool {
        self.io_enabled == arrival.io_enabled
            && self.effects.fingerprint() == arrival.effects.fingerprint()
            && arrival.diagnostics.is_subset_of(&self.diagnostics)
            && self.effects == arrival.effects
            && self.io.observed_alike(&arrival.io)
    }
}

/// The recorded states of the depths still reachable, by depth and key.
#[derive(Default)]
pub(super) struct ExplorationMerge {
    depths: BTreeMap<u64, HashMap<Pattern, Vec<Recorded>>>,
    len: usize,
}

impl ExplorationMerge {
    pub(super) fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Whether a recorded state of `arrival`'s depth and key absorbs it.
    pub(super) fn absorbs(&self, arrival: &Arrival) -> bool {
        self.depths
            .get(&arrival.depth)
            .and_then(|keys| keys.get(&arrival.key))
            .is_some_and(|recorded| recorded.iter().any(|state| state.absorbs(arrival)))
    }

    /// Record a state whose expansion completed. A state arriving later with incomparable
    /// diagnostics is recorded beside the earlier one.
    pub(super) fn record(&mut self, arrival: Arrival) {
        let Arrival {
            depth,
            key,
            effects,
            io,
            io_enabled,
            diagnostics,
        } = arrival;
        self.depths
            .entry(depth)
            .or_default()
            .entry(key)
            .or_default()
            .push(Recorded {
                effects,
                io,
                io_enabled,
                diagnostics,
            });
        self.len += 1;
    }

    /// Forget the depths below `depth`, which no state can arrive at any more.
    pub(super) fn evict_below(&mut self, depth: u64) {
        let kept = self.depths.split_off(&depth);
        let evicted = std::mem::replace(&mut self.depths, kept);
        self.len -= evicted
            .values()
            .flat_map(HashMap::values)
            .map(Vec::len)
            .sum::<usize>();
    }

    pub(super) fn clear(&mut self) {
        self.depths.clear();
        self.len = 0;
    }

    /// The recorded states, and the shallowest depth recorded.
    #[cfg(test)]
    pub(super) fn census(&self) -> (usize, Option<u64>) {
        (self.len, self.depths.keys().next().copied())
    }
}
