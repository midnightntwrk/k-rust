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
//!
//! A recorded state keeps its pattern, which shares its nodes with the states it was rewritten
//! from and into, and nothing is computed from the pattern until a second state arrives at its
//! depth. Then each state of the depth is hashed once ([`RequestNames::shape_hash`]), and keys
//! (`RequestNames::state_key`) are built only for states whose hashes agree, each at most once.
//! A run in which no two states of one depth share a hash builds no key.

use std::{cell::OnceCell, collections::BTreeMap};

use rustc_hash::FxHashMap;

use crate::{
    diagnostic::PathDiagnostics,
    fresh::RequestNames,
    transition::{EffectJournal, ExecutionIoState},
};

use super::Pattern;

/// A state that arrives at a depth, as the table compares and records it.
pub(super) struct Arrival {
    pub(super) depth: u64,
    pub(super) pattern: Pattern,
    pub(super) effects: EffectJournal,
    pub(super) io: ExecutionIoState,
    pub(super) io_enabled: bool,
    pub(super) diagnostics: PathDiagnostics,
    /// The pattern's shape hash, once a state of its depth was met.
    shape: Option<u64>,
    /// The pattern's key, once a recorded state of its shape was met.
    key: OnceCell<Pattern>,
}

impl Arrival {
    pub(super) fn new(
        depth: u64,
        pattern: Pattern,
        effects: EffectJournal,
        io: ExecutionIoState,
        io_enabled: bool,
        diagnostics: PathDiagnostics,
    ) -> Self {
        Self {
            depth,
            pattern,
            effects,
            io,
            io_enabled,
            diagnostics,
            shape: None,
            key: OnceCell::new(),
        }
    }

    fn key(&self, names: &RequestNames) -> &Pattern {
        self.key.get_or_init(|| names.state_key(&self.pattern))
    }

    /// Whether every leaf this state's subtree would yield is a leaf of `recorded`'s subtree,
    /// both of one depth and shape hash. The fingerprints decide most comparisons in constant
    /// time, and the keys are built last; equal fingerprints are confirmed on the sequences,
    /// which stop where the two paths share their history.
    fn absorbed_by(&self, recorded: &Self, names: &RequestNames) -> bool {
        recorded.io_enabled == self.io_enabled
            && recorded.effects.fingerprint() == self.effects.fingerprint()
            && self.diagnostics.is_subset_of(&recorded.diagnostics)
            && recorded.key(names) == self.key(names)
            && recorded.effects == self.effects
            && recorded.io.observed_alike(&self.io)
    }
}

/// The recorded states of one depth: those not yet hashed, and the others by shape hash.
#[derive(Default)]
struct Depth {
    unhashed: Vec<Arrival>,
    by_shape: FxHashMap<u64, Vec<Arrival>>,
}

impl Depth {
    fn len(&self) -> usize {
        self.unhashed.len() + self.by_shape.values().map(Vec::len).sum::<usize>()
    }
}

/// Push `arrival`, giving a list its first state room for that state alone: most depths and
/// hashes hold one state, and a vector's first growth would reserve room for four.
fn push(states: &mut Vec<Arrival>, arrival: Arrival) {
    if states.is_empty() {
        states.reserve_exact(1);
    }
    states.push(arrival);
}

/// The recorded states of the depths still reachable.
#[derive(Default)]
pub(super) struct ExplorationMerge {
    depths: BTreeMap<u64, Depth>,
    len: usize,
}

impl ExplorationMerge {
    pub(super) fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Whether a recorded state of `arrival`'s depth absorbs it. When the depth holds a
    /// recorded state, `arrival` and every state of the depth not yet hashed are hashed.
    pub(super) fn absorbs(&mut self, arrival: &mut Arrival, names: &RequestNames) -> bool {
        let Some(depth) = self.depths.get_mut(&arrival.depth) else {
            return false;
        };
        for mut recorded in depth.unhashed.drain(..) {
            let shape = names.shape_hash(&recorded.pattern);
            recorded.shape = Some(shape);
            push(depth.by_shape.entry(shape).or_default(), recorded);
        }
        let shape = *arrival
            .shape
            .get_or_insert_with(|| names.shape_hash(&arrival.pattern));
        depth.by_shape.get(&shape).is_some_and(|recorded| {
            recorded
                .iter()
                .any(|recorded| arrival.absorbed_by(recorded, names))
        })
    }

    /// Record a state whose expansion completed. A state arriving later with incomparable
    /// diagnostics is recorded beside the earlier one.
    pub(super) fn record(&mut self, arrival: Arrival) {
        let depth = self.depths.entry(arrival.depth).or_default();
        let states = match arrival.shape {
            Some(shape) => depth.by_shape.entry(shape).or_default(),
            None => &mut depth.unhashed,
        };
        push(states, arrival);
        self.len += 1;
    }

    /// Forget the depths below `depth`, which no state can arrive at any more.
    pub(super) fn evict_below(&mut self, depth: u64) {
        let kept = self.depths.split_off(&depth);
        let evicted = std::mem::replace(&mut self.depths, kept);
        self.len -= evicted.values().map(Depth::len).sum::<usize>();
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
