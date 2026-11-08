//! Rule windows: the sequences of rewrite rules a run took as consecutive committed steps along
//! some path ([`super::RunCoverage::windows`]).
//!
//! A *window* of length `n` is a sequence `(A1, ..., An)` of rewrite rules such that some path of
//! the run committed to a successor of `A1`, then of `A2`, and so on to `An`, one step after the
//! other; equivalently, a path of `n` labelled transitions of the run's transition graph. A step
//! is committed where `RunCoverage::committed` records its rule (`rewrite::execute`'s
//! `note_committed`): its successor's own normalization showed it defined. So a candidate the step
//! rolled back, an undefined-step entry, a cut-point rule's proposed successor and a successor a
//! stop or the work budget cut before its normalization finished take no part in any window, and
//! the windows of length 1 are `committed`. A remainder is no step: the path through it goes on
//! from the state it restricts.
//!
//! Equations take no part. A function's value is shared through the run's memos across its
//! callers, so where an equation's instance is evaluated, before or within which step, rests on
//! the evaluation history, not on the definition; what a rule does with a function's value is
//! read from the rule's own steps.
//!
//! A run that asks for windows of length up to `d` (`rewrite::ExecutionOptions::collect_windows`)
//! collects every window of length `1..=d`.
//!
//! # Collection
//!
//! Each path carries its last `d - 1` committed steps ([`WindowPath`]), each with the rule and the
//! state it was taken from. Where the path commits to a step by `A`, the window formed by those
//! steps followed by `A` is recorded; its suffixes are the windows that end at this step.
//!
//! Under `state-set`, an arrival at a state equal at its depth to a recorded one is merged
//! (`rewrite::exploration_merge`): its subtree is not explored again, so its steps are not
//! committed again, and the windows that begin on the arriving path and end in the recorded
//! state's subtree are formed by no commit. For each state `s` the merge table records, the run
//! keeps, besides, its forward set `F(s)`: every sequence of length `1..=d-1` of committed steps
//! that starts at `s` ([`Forward`]). Where a path commits to a step, the step is appended to the
//! sequence from each of the path's last `d - 1` source states, so each such state's set grows by
//! the sequence from it to the step; where an arrival is merged into `s`, each sequence of `F(s)`
//! is appended likewise. At the merge the run records each window formed by the arriving path's
//! last steps followed by a sequence of `F(s)`.
//!
//! Exploration is depth-first, and a state merges only into a recorded state of its own depth:
//! every state of that depth explored after `s` lies outside `s`'s subtree, since the subtree's
//! states are deeper than `s` but for remainders, which take no part in merging. So `s`'s subtree
//! was explored to its end before the arrival, and `F(s)` holds every sequence of length below `d`
//! that starts at `s`, through the merges inside the subtree as well, by induction on the merges in
//! exploration order. A window of the unmerged path tree either lies within the subtree of the
//! recorded state, where it was recorded, or begins on the arriving path and ends in that subtree,
//! where the merge records it. So a `state-set` run collects the windows of the `path-set` run of
//! the same request wherever the two explore the same states (`tests::windows`).
//!
//! # Cost
//!
//! Without `collect_windows` nothing is collected and the run does no work for it: a path carries
//! no window state, and the merge table keeps no forward set. With it, under `d`:
//! - each committed step interns its rule (one hash lookup), records one window of at most `d`
//!   ids, and copies the path's last `d - 1` steps into the successor's state when the step forks;
//! - under `state-set` with `d >= 2`, each committed step also adds one sequence of at most
//!   `d - 1` ids to the forward set of each of the path's last `d - 1` source states still in the
//!   merge table, `O(d^2)` ids; and each merged arrival adds, per sequence of the absorbing state's
//!   forward set, one window and at most `d - 1` sequences, `O(|F(s)| d^2)` ids;
//! - a forward set is kept only for a state in the merge table, and only while windows are asked
//!   for: the table owns it, and a path refers to it weakly, so it is freed with the state's
//!   record when the table evicts its depth. It holds at most the distinct rule sequences of
//!   length below `d` that start at its state, at most `b^(d-1)` for a branching factor `b`;
//! - the windows recorded are the distinct maximal windows ending at a step, and the result holds
//!   their suffixes, so its size is at most `d` times theirs.

use std::{
    cell::RefCell,
    collections::BTreeSet,
    num::NonZeroUsize,
    rc::{Rc, Weak},
};

use rustc_hash::{FxHashMap, FxHashSet};

/// A sequence of rules by interned id.
type Sequence = Box<[u32]>;

/// The forward set `F(s)` of a state `s` the merge table records: every sequence of length
/// `1..=d-1` of committed steps that starts at `s` and was taken so far. The merge table owns it
/// (`rewrite::exploration_merge::Arrival::forward`); a path refers to it weakly.
#[derive(Default)]
pub(crate) struct Forward(RefCell<FxHashSet<Sequence>>);

impl Forward {
    fn add(&self, sequence: Sequence) {
        self.0.borrow_mut().insert(sequence);
    }
}

/// What a path carries of its past for the windows: its last `d - 1` committed steps, oldest
/// first, each with its rule and the forward set of the state it was taken from, and the forward
/// set of the path's own state while it is expanded, where it has one.
#[derive(Clone, Debug, Default)]
pub(crate) struct WindowPath {
    steps: Vec<(u32, Weak<Forward>)>,
    source: Weak<Forward>,
}

impl std::fmt::Debug for Forward {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_set()
            .entries(self.0.borrow().iter())
            .finish()
    }
}

impl WindowPath {
    /// The path's state is expanded, with `forward` as its forward set where the merge table
    /// will record it, `None` where it takes no part in merging: the steps it takes start there.
    pub(crate) fn expands(&mut self, forward: Option<&Rc<Forward>>) {
        self.source = forward.map(Rc::downgrade).unwrap_or_default();
    }

    fn rules(&self) -> impl Iterator<Item = u32> + '_ {
        self.steps.iter().map(|(rule, _)| *rule)
    }
}

/// The windows of a run, while it runs.
pub(crate) struct WindowCollection {
    /// `d`, the longest window collected.
    length: usize,
    /// Whether forward sets are kept: `d >= 2` and the run merges states.
    forward: bool,
    ids: FxHashMap<String, u32>,
    names: Vec<String>,
    /// The maximal windows recorded: those ending at a step, as long as the path allows up to `d`.
    windows: FxHashSet<Sequence>,
}

impl WindowCollection {
    /// A collection of the windows of length up to `length`, for a run that merges states when
    /// `merging` holds.
    pub(crate) fn new(length: NonZeroUsize, merging: bool) -> Self {
        Self {
            length: length.get(),
            forward: merging && length.get() >= 2,
            ids: FxHashMap::default(),
            names: Vec::new(),
            windows: FxHashSet::default(),
        }
    }

    /// A forward set for a state the merge table may record, when the collection keeps them.
    pub(crate) fn forward_set(&self) -> Option<Rc<Forward>> {
        self.forward.then(Rc::default)
    }

    fn intern(&mut self, rule: &str) -> u32 {
        if let Some(id) = self.ids.get(rule) {
            return *id;
        }
        let id = u32::try_from(self.names.len()).expect("fewer than 2^32 rules");
        self.names.push(rule.to_owned());
        self.ids.insert(rule.to_owned(), id);
        id
    }

    /// The path `path` committed to a step by `rule`, taken from the state it was expanded from.
    pub(crate) fn committed(&mut self, path: &mut WindowPath, rule: &str) {
        let rule = self.intern(rule);
        let source = std::mem::take(&mut path.source);
        self.windows
            .insert(path.rules().chain(std::iter::once(rule)).collect());
        if self.length == 1 {
            return;
        }
        if path.steps.len() == self.length - 1 {
            path.steps.remove(0);
        }
        path.steps.push((rule, source));
        if !self.forward {
            return;
        }
        let rules = path.rules().collect::<Vec<_>>();
        for (from, (_, source)) in path.steps.iter().enumerate() {
            if let Some(forward) = source.upgrade() {
                forward.add(rules[from..].into());
            }
        }
    }

    /// The path `path`, at a state the run merged into a recorded state of forward set `into`:
    /// the path goes on with every sequence of `into`.
    pub(crate) fn merged(&mut self, path: &WindowPath, into: &Forward) {
        let rules = path.rules().collect::<Vec<_>>();
        let sequences = into.0.borrow().iter().cloned().collect::<Vec<_>>();
        for sequence in &sequences {
            // The window ending at the sequence's last step reaches as far back as `d` allows.
            let back = rules.len().min(self.length - sequence.len());
            self.windows.insert(
                rules[rules.len() - back..]
                    .iter()
                    .chain(sequence.iter())
                    .copied()
                    .collect(),
            );
            for (from, (_, source)) in path.steps.iter().enumerate() {
                if rules.len() - from + sequence.len() >= self.length {
                    continue;
                }
                if let Some(forward) = source.upgrade() {
                    forward.add(
                        rules[from..]
                            .iter()
                            .chain(sequence.iter())
                            .copied()
                            .collect(),
                    );
                }
            }
        }
    }

    /// Every window of length `1..=d` the run took: the suffixes of the recorded ones, by rule
    /// id.
    pub(crate) fn finish(self) -> BTreeSet<Vec<String>> {
        let mut windows = BTreeSet::new();
        for window in &self.windows {
            for from in 0..window.len() {
                windows.insert(
                    window[from..]
                        .iter()
                        .map(|id| self.names[*id as usize].clone())
                        .collect(),
                );
            }
        }
        windows
    }
}
