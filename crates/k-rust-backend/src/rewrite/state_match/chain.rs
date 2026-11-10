//! Matching the states of an execution against a chain of patterns: steps `P1, [U2] P2, …,
//! [Un] Pn`, each a target pattern, each step after the first with an optional *unless* `Ui`,
//! also a target pattern.
//!
//! A chain holds on a path `s0 s1 … sm` of the run when there are indices `k1 ≤ k2 ≤ … ≤ kn`
//! and one assignment of the chain's shared variables under which every `s(ki)` matches step `i`
//! and, for every `i ≥ 2` with an unless, no state strictly between `s(k(i-1))` and `s(ki)`
//! matches `Ui`. Consecutive steps may match one state (each arrow is reflexive). The states are
//! the ones the state matcher observes, and a step's verdict on a state is the state matcher's
//! verdict (parent module documentation): the state is decided, shown to exist, and matched with
//! empty constraints in every required mode. An unless needs no existence: if the state it
//! kills on denotes nothing, neither does the path through it.
//!
//! A *shared* variable is bound by the first step whose body names it. Each later part that names
//! it *imports* it: the value is substituted into the part's target and constraints before the
//! part is matched ([`instantiate`]), so a `requires` that names it is decided by the match on
//! that value, as any `requires` is, and no value is ever compared with another afterwards.
//! A step *exports* the variables it binds that a later part names.
//!
//! Each path carries its progress ([`Progress`]): the partial occurrences of the chain on it,
//! each keyed by the step it awaits and the values of the variables that step and the parts after
//! it import ([`PartialKey`]), which are all that any later verdict reads. A state `s` is
//! processed in the order of the steps awaited, starting from the empty partial that awaits the
//! first step and the parent's partials:
//! - a partial awaiting step `j` is matched against step `j` instantiated by its key. Each
//!   unconditional way extends it into a partial awaiting step `j + 1` at `s`, or completes the
//!   chain when `j` is the last step. The extensions are processed at `s` in turn, so consecutive
//!   steps may match `s`;
//! - a partial of the parent that awaits a step with an unless is matched against the unless
//!   instantiated by its key: matched, it is killed, since `s` lies strictly between its last
//!   state and any later state of the step it awaits; undecided, it is dropped and the drop is
//!   counted, so it never makes a completion; refuted, it is kept. A partial created at `s` is
//!   not matched against an unless at `s`, which ends its arrow. A killed partial is still
//!   extended at `s`, where its arrow may end.
//!
//! A step match that is undecided (an undecided state, a state not shown to exist, a way left
//! undecided or matched only under constraints, a mode disagreement, the placement bound, a
//! stop) is counted; the ways it decided are each a match and extend the partial. With no
//! variable exported to a later part every way gives the same key, so one unconditional way is
//! the whole answer. Under proof agreement a way extends only when both modes find its key, and
//! the match is undecided unless both modes find the same keys and every way.
//!
//! Two partials with one key have the same future: the parts still awaited read only the key,
//! and each partial has survived every state from its last state through `s`. So the progress
//! keeps one partial per key, the one whose step states are least in depth order, step by step
//! (the first processed on a tie). The progress holds at most `partial_cap` partials: beyond it
//! the largest keys are evicted and the progress is marked overflowed, which a judge reads as a
//! possible missed completion. An eviction only loses completions; every partial kept is a real
//! prefix of the chain on the path.
//!
//! The first clean completion (parent module documentation, "clean"; on the prefix through the
//! last step's state) with no term-level `\and` in any step state, in processing order, ends the
//! matching, and is the witness. Among completions at one state the least step states in depth
//! order win, then the least key. For a chain of one step this is the state matcher's first
//! clean reach. A clean completion with a conjunction is kept until such a completion replaces it.
//!
//! A progress's digest ([`Progress::digest`]) is a SHA-256 of its keys, its overflow mark and
//! whether its path is clean, written in canonical compact KORE; two progresses with one digest
//! process every later state alike. It reads no address, no hash-map order and no clock. Once the
//! matching is over every state gets one constant progress, whose digest is that of no other.
//!
//! Merging. A state-set run merges a state into a recorded state of its depth whose subtree
//! would give the same leaves (`exploration_merge`). Under a chain it also requires the two
//! states' merge keys to be equal ([`ChainMatcher::merge_key`]): the digest of the progress each
//! path reached the state with, and whether each path is clean up to and including the state.
//! Equal keys give equal processing: every state of the two subtrees is processed from equal
//! keys, so a completion, an undecided match or an eviction in one is one in the other, with the
//! same cleanness, since a completion's cleanness is that of the path up to the state merged
//! followed by the subtree's own steps. Only the payloads differ, so the recorded subtree's
//! completions are real chains, and the merged arrival would add none that the summary does not
//! already hold. A merge refused for unequal keys explores the arrival's subtree again, which a
//! counted work budget bounds. Once matching is over the summary is final, and a state carries
//! no key.
//!
//! The chain matcher is isolated from the run as the state matcher is; its solver answers and
//! stops for lack of native stack are counted in its summary ([`ChainMatches`]). Every bound it
//! adds is a count: the partial cap.

use std::{
    cell::Cell,
    collections::{BTreeMap, btree_map::Entry},
    fmt,
    rc::Rc,
};

use sha2::{Digest, Sha256};

use crate::{
    definition::BackendDefinition,
    diagnostic::{BackendDiagnostic, PathDiagnostics},
    smt::SmtSolver,
    substitution::{Substitution, substitute},
    term::{Term, Variable},
    transition::PatternDigest,
};

use super::{
    Incomplete, MatchMark, StateMatch, StateReader, UndecidedMatchReason, clean,
    holds_term_conjunction, isolated,
};
use crate::rewrite::{Pattern, predicates::pattern_free_variables};

/// A chain a run matches its states against: its steps, in order, and the most partials one
/// path's progress keeps.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChainOptions {
    pub steps: Vec<ChainStep>,
    pub partial_cap: usize,
}

/// One step of a chain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChainStep {
    /// The internalized target pattern, with its constraints (a `requires`).
    pub target: Pattern,
    /// The variables of the target bound by an earlier step, whose values are substituted into
    /// it before it is matched.
    pub imports: Vec<Variable>,
    /// The variables the target binds that a later step or unless names.
    pub exports: Vec<Variable>,
    /// What no state strictly between the previous step's state and this step's may match.
    pub unless: Option<UnlessPart>,
}

/// The unless of a step: a target pattern whose variables other than its imports are
/// existential.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnlessPart {
    pub target: Pattern,
    /// The variables of the target bound by an earlier step.
    pub imports: Vec<Variable>,
}

/// Why chain options are refused.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InvalidChain(pub String);

impl fmt::Display for InvalidChain {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for InvalidChain {}

/// Chain options that passed [`ChainOptions::check`]: the only form a run accepts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckedChain(ChainOptions);

impl CheckedChain {
    pub fn options(&self) -> &ChainOptions {
        &self.0
    }
}

impl ChainOptions {
    /// The options, once [`Self::check`] accepts them.
    pub fn checked(self) -> Result<CheckedChain, InvalidChain> {
        self.check()?;
        Ok(CheckedChain(self))
    }

    /// Check that the chain's variables are classified consistently: there is a step; the first
    /// step imports nothing and has no unless; each part imports exactly the variables of its
    /// target an earlier step exports; each step exports variables of its target's term that no
    /// earlier step exports; no list names a variable twice.
    pub fn check(&self) -> Result<(), InvalidChain> {
        if self.steps.is_empty() {
            return Err(InvalidChain("a chain has at least one step".to_owned()));
        }
        if self.steps[0].unless.is_some() {
            return Err(InvalidChain(
                "the first step of a chain has no unless".to_owned(),
            ));
        }
        let mut exported: Vec<Variable> = Vec::new();
        for (index, step) in self.steps.iter().enumerate() {
            let part = format!("step {}", index + 1);
            check_imports(&part, &step.target, &step.imports, &exported)?;
            if let Some(unless) = &step.unless {
                let part = format!("the unless of step {}", index + 1);
                check_imports(&part, &unless.target, &unless.imports, &exported)?;
            }
            let variables = step.target.term.attributes();
            for (position, export) in step.exports.iter().enumerate() {
                if step.exports[..position].contains(export) {
                    return Err(InvalidChain(format!("{part} exports {export:?} twice")));
                }
                if exported.contains(export) {
                    return Err(InvalidChain(format!(
                        "{part} exports {export:?}, which an earlier step binds"
                    )));
                }
                if !variables.variables.contains(export) {
                    return Err(InvalidChain(format!(
                        "{part} exports {export:?}, which its term does not name"
                    )));
                }
            }
            exported.extend(step.exports.iter().cloned());
        }
        Ok(())
    }
}

/// `imports` are the variables of `target` that `exported` holds.
fn check_imports(
    part: &str,
    target: &Pattern,
    imports: &[Variable],
    exported: &[Variable],
) -> Result<(), InvalidChain> {
    let variables = pattern_free_variables(target);
    for (position, import) in imports.iter().enumerate() {
        if imports[..position].contains(import) {
            return Err(InvalidChain(format!("{part} imports {import:?} twice")));
        }
        if !exported.contains(import) {
            return Err(InvalidChain(format!(
                "{part} imports {import:?}, which no earlier step exports"
            )));
        }
    }
    if let Some(missed) = variables
        .iter()
        .find(|variable| exported.contains(variable) && !imports.contains(variable))
    {
        return Err(InvalidChain(format!(
            "{part} names {missed:?}, which an earlier step exports, without importing it"
        )));
    }
    Ok(())
}

/// The key of a partial occurrence: the step it awaits (an index into the chain's steps), whether
/// one of its step states holds a term-level `\and`, and the values of the variables it holds
/// that the awaited step and the parts after it import, in the order of the steps that exported
/// them. Keys are ordered by these fields in turn, values by the term order; that order decides
/// eviction and ties between witnesses.
///
/// The conjunction mark is part of the key because it decides whether a completion can end the
/// matching: two partials that differ in it have different futures for the witness.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PartialKey {
    pub next: usize,
    pub term_conjunction: bool,
    pub bindings: Vec<(Variable, Term)>,
}

/// One step matched: the state's depth, its configuration as matched, and the way it matched
/// (the substitution of the step's target with its imports substituted).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StepHit {
    pub depth: u64,
    pub pattern: Pattern,
    pub bindings: Substitution,
}

/// The steps a partial occurrence matched, shared with the partials it was extended from.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Payload(Option<Rc<HitNode>>);

#[derive(Debug, Eq, PartialEq)]
struct HitNode {
    hit: StepHit,
    previous: Payload,
}

impl Payload {
    /// The steps matched, in step order.
    pub fn steps(&self) -> Vec<&StepHit> {
        let mut steps = Vec::new();
        let mut node = self.0.as_deref();
        while let Some(current) = node {
            steps.push(&current.hit);
            node = current.previous.0.as_deref();
        }
        steps.reverse();
        steps
    }

    fn then(&self, hit: StepHit) -> Self {
        Self(Some(Rc::new(HitNode {
            hit,
            previous: self.clone(),
        })))
    }

    /// The depths of the steps matched, in step order.
    fn depths(&self) -> Vec<u64> {
        self.steps().iter().map(|hit| hit.depth).collect()
    }
}

/// One path's progress through a chain after a state (module documentation).
#[derive(Debug)]
pub struct Progress {
    partials: BTreeMap<PartialKey, Payload>,
    overflowed: bool,
    clean: bool,
    frozen: bool,
    digest: [u8; 32],
}

impl Progress {
    fn new(
        partials: BTreeMap<PartialKey, Payload>,
        overflowed: bool,
        clean: bool,
        frozen: bool,
    ) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(b"k-rust-backend/chain-progress/v1\0");
        hasher.update([u8::from(frozen), u8::from(overflowed), u8::from(clean)]);
        hasher.update(count(partials.len()));
        for key in partials.keys() {
            hasher.update(count(key.next));
            hasher.update([u8::from(key.term_conjunction)]);
            hasher.update(count(key.bindings.len()));
            for (_, value) in &key.bindings {
                let value = Pattern {
                    term: value.clone(),
                    constraints: Vec::new(),
                };
                hasher.update(PatternDigest::of(&value).as_bytes());
            }
        }
        Self {
            partials,
            overflowed,
            clean,
            frozen,
            digest: hasher.finalize().into(),
        }
    }

    /// The partial occurrences, in key order.
    pub fn partials(&self) -> &BTreeMap<PartialKey, Payload> {
        &self.partials
    }

    /// Whether a partial was evicted on the path, here or before.
    pub fn overflowed(&self) -> bool {
        self.overflowed
    }

    /// Whether the path up to the state is clean (parent module documentation).
    pub fn clean(&self) -> bool {
        self.clean
    }

    /// Whether the matching was over when the state was reached, so nothing was kept.
    pub fn frozen(&self) -> bool {
        self.frozen
    }

    /// The digest of the keys, the overflow mark, the path's cleanness and the frozen mark (module
    /// documentation). The key variables of a step are a function of the chain, so only the values
    /// are written. Two states whose parents' progresses have one digest are processed alike.
    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }
}

/// What the merge table compares of a state's chain progress ([`ChainMatcher::merge_key`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::rewrite) struct ChainMergeKey {
    progress: Option<[u8; 32]>,
    clean: bool,
}

fn count(value: usize) -> [u8; 8] {
    u64::try_from(value)
        .expect("a count fits in 64 bits")
        .to_le_bytes()
}

/// A completed chain: each step's match, in step order, the diagnostics of the path up to the
/// last step's state, and whether a step state holds a term-level `\and`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChainCompletion {
    pub steps: Vec<StepHit>,
    pub diagnostics: Vec<BackendDiagnostic>,
    pub term_conjunction: bool,
}

/// A part of a chain whose match can be undecided: a step, or a step's unless (indices into the
/// chain's steps).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ChainPart {
    Step(usize),
    Unless(usize),
}

/// The undecided matches of one part for one reason: how many, and the first, with the state and
/// the key bindings the part was instantiated with.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChainUndecided {
    pub part: ChainPart,
    pub reason: UndecidedMatchReason,
    pub count: u64,
    pub first: StateMatch,
    pub bindings: Vec<(Variable, Term)>,
}

/// The summary of a run's chain matching, in the run's depth-first order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ChainMatches {
    /// The first completion on a clean prefix with no term-level `\and` in a step state, where
    /// one exists, and otherwise the first clean completion; matching stopped at the former.
    pub first_clean_completion: Option<ChainCompletion>,
    /// The first completion on a prefix that is not clean.
    pub first_dirty_completion: Option<ChainCompletion>,
    /// The completions on prefixes that are not clean.
    pub dirty_completions: u64,
    /// For each part and reason, in that order, the undecided matches. An undecided unless drops
    /// its partial; an undecided step extends none but the ways it decided.
    pub undecided: Vec<ChainUndecided>,
    /// The paths whose progress evicted a partial: counted where the first eviction happened.
    pub overflowed_paths: u64,
    /// The most partials one progress kept.
    pub peak_partials: u64,
    /// The states processed.
    pub states: u64,
    /// The step and unless matches made.
    pub evaluations: u64,
    /// The undecided answers the solver gave the matcher, which the run's own count leaves out.
    pub smt_unknowns: usize,
    /// The matcher's stops for lack of native stack, which the run's own count leaves out.
    pub stack_stops: usize,
}

/// One step as the matcher reads it.
#[derive(Debug)]
struct Step {
    target: Pattern,
    imports: Vec<Variable>,
    unless: Option<UnlessPart>,
    /// The exports a partial extended by this step keeps in its key: those the next step and the
    /// parts after it import.
    carried: Vec<Variable>,
    /// The key variables of a partial extended by this step.
    next_key: Vec<Variable>,
}

/// The chain matcher of one run.
pub(in crate::rewrite) struct ChainMatcher<'a> {
    steps: Vec<Step>,
    partial_cap: usize,
    reader: StateReader<'a>,
    found: ChainMatches,
    frozen: Rc<Progress>,
}

/// A partial offered to a level at one state: the payload it is extended from at the state, and
/// the payload it is kept with in the new progress, when it is kept.
#[derive(Clone)]
struct Candidate {
    advance: Payload,
    insert: Option<Payload>,
}

/// A completion at one state, before the summary records it.
struct Completed {
    key: PartialKey,
    payload: Payload,
    term_conjunction: bool,
}

impl Completed {
    fn rank(&self) -> (Vec<u64>, &PartialKey) {
        (self.payload.depths(), &self.key)
    }

    fn completion(&self, diagnostics: &PathDiagnostics) -> ChainCompletion {
        ChainCompletion {
            steps: self.payload.steps().into_iter().cloned().collect(),
            diagnostics: diagnostics.to_vec(),
            term_conjunction: self.term_conjunction,
        }
    }
}

/// What processing one state gave, before the summary records it.
#[derive(Default)]
struct Outcome {
    partials: BTreeMap<PartialKey, Payload>,
    completions: Vec<Completed>,
    /// Each undecided match: the part, the reason, and the key bindings it was instantiated with.
    undecided: Vec<UndecidedEvent>,
    evaluations: u64,
}

type UndecidedEvent = (ChainPart, UndecidedMatchReason, Vec<(Variable, Term)>);

/// The facts of a state that matching reads, each computed at most once.
struct StateFacts<'s> {
    pattern: &'s Pattern,
    decided: bool,
    defined: Cell<Option<bool>>,
    conjunction: Cell<Option<bool>>,
}

impl<'s> StateFacts<'s> {
    fn new(pattern: &'s Pattern) -> Self {
        Self {
            pattern,
            decided: pattern.constraints.is_empty()
                && pattern.term.attributes().variables.is_empty(),
            defined: Cell::new(None),
            conjunction: Cell::new(None),
        }
    }

    fn defined(&self, definition: &BackendDefinition) -> bool {
        if let Some(defined) = self.defined.get() {
            return defined;
        }
        let defined = definition.ground_defined(&self.pattern.term);
        self.defined.set(Some(defined));
        defined
    }

    fn conjunction(&self) -> bool {
        if let Some(conjunction) = self.conjunction.get() {
            return conjunction;
        }
        let conjunction = holds_term_conjunction(&self.pattern.term);
        self.conjunction.set(Some(conjunction));
        conjunction
    }
}

/// An unless's verdict on a state.
enum UnlessVerdict {
    Matched,
    Refuted,
    Undecided(UndecidedMatchReason),
}

impl<'a> ChainMatcher<'a> {
    pub(in crate::rewrite) fn new(
        chain: CheckedChain,
        proof_agreement: bool,
        solver: &'a dyn SmtSolver,
        max_iterations: usize,
    ) -> Self {
        let ChainOptions { steps, partial_cap } = chain.0;
        // The variables the parts from each step on import.
        let mut imported_from = vec![Vec::<Variable>::new(); steps.len() + 1];
        for (index, step) in steps.iter().enumerate().rev() {
            let mut imported = imported_from[index + 1].clone();
            for import in step
                .imports
                .iter()
                .chain(step.unless.iter().flat_map(|unless| &unless.imports))
            {
                if !imported.contains(import) {
                    imported.push(import.clone());
                }
            }
            imported_from[index] = imported;
        }
        let mut exported: Vec<Variable> = Vec::new();
        let steps = steps
            .into_iter()
            .enumerate()
            .map(|(index, step)| {
                let needed = &imported_from[index + 1];
                let carried = step
                    .exports
                    .iter()
                    .filter(|export| needed.contains(export))
                    .cloned()
                    .collect();
                exported.extend(step.exports.iter().cloned());
                let next_key = exported
                    .iter()
                    .filter(|export| needed.contains(export))
                    .cloned()
                    .collect();
                Step {
                    target: step.target,
                    imports: step.imports,
                    unless: step.unless,
                    carried,
                    next_key,
                }
            })
            .collect();
        Self {
            steps,
            partial_cap,
            reader: StateReader::new(proof_agreement, solver, max_iterations),
            found: ChainMatches::default(),
            frozen: Rc::new(Progress::new(BTreeMap::new(), false, true, true)),
        }
    }

    /// Whether matching is over: a clean completion with no term-level `\and` was found.
    pub(in crate::rewrite) fn done(&self) -> bool {
        self.found
            .first_clean_completion
            .as_ref()
            .is_some_and(|completion| !completion.term_conjunction)
    }

    /// Process the state `pattern`, reached at `depth` on a path with `diagnostics`, whose
    /// parent's progress is `parent` (`None` for an initial state). Returns the state's progress,
    /// which is `parent` itself when the state changed nothing, and what the merge table keeps of
    /// the state: a reach when a chain completed at it.
    pub(in crate::rewrite) fn observe(
        &mut self,
        definition: &BackendDefinition,
        parent: Option<&Rc<Progress>>,
        depth: u64,
        pattern: &Pattern,
        diagnostics: &PathDiagnostics,
    ) -> (Rc<Progress>, MatchMark) {
        if self.done() {
            return (Rc::clone(&self.frozen), MatchMark::Other);
        }
        let (normalized, normalizing_stops) = self.reader.normalized(definition, pattern);
        let empty = BTreeMap::new();
        let partials = parent.map_or(&empty, |parent| &parent.partials);
        let (outcome, matching_stops) =
            isolated(|| self.process(definition, partials, depth, &normalized));
        self.found.stack_stops += normalizing_stops + matching_stops;
        self.found.states += 1;
        self.found.evaluations += outcome.evaluations;
        for (part, reason, bindings) in outcome.undecided {
            self.count_undecided(part, reason, bindings, || StateMatch {
                depth,
                pattern: normalized.clone(),
                diagnostics: diagnostics.to_vec(),
                term_conjunction: false,
            });
        }
        let clean = clean(diagnostics);
        let mark = self.record_completions(outcome.completions, clean, diagnostics);
        if self.done() {
            return (Rc::clone(&self.frozen), mark);
        }
        (self.progress(parent, outcome.partials, clean), mark)
    }

    /// What the merge table compares of a state about to be expanded, reached on a path with
    /// `diagnostics` whose progress so far is `progress` (its parent's; `None` before any state
    /// was processed on it): the progress's digest and whether the path up to the state is
    /// clean. `None` once matching is over, when the chain reads nothing more and a state merges
    /// as it would without the chain (module documentation, "Merging").
    pub(in crate::rewrite) fn merge_key(
        &self,
        progress: Option<&Rc<Progress>>,
        diagnostics: &PathDiagnostics,
    ) -> Option<ChainMergeKey> {
        (!self.done()).then(|| ChainMergeKey {
            progress: progress.map(|progress| progress.digest),
            clean: clean(diagnostics),
        })
    }

    /// The summary, with the matcher's undecided solver answers.
    pub(in crate::rewrite) fn finish(mut self) -> ChainMatches {
        self.found.smt_unknowns = self.reader.solver.undecided();
        self.found
    }

    /// Keep `completion` as the first clean completion unless one is kept already (which,
    /// matching not being over, holds a term-level `\and`) and `completion` is no better.
    fn keep_clean(&mut self, completion: ChainCompletion) {
        if self.found.first_clean_completion.is_none() || !completion.term_conjunction {
            self.found.first_clean_completion = Some(completion);
        }
    }

    fn count_undecided(
        &mut self,
        part: ChainPart,
        reason: UndecidedMatchReason,
        bindings: Vec<(Variable, Term)>,
        first: impl FnOnce() -> StateMatch,
    ) {
        match self
            .found
            .undecided
            .binary_search_by(|entry| (entry.part, entry.reason).cmp(&(part, reason)))
        {
            Ok(index) => self.found.undecided[index].count += 1,
            Err(index) => self.found.undecided.insert(
                index,
                ChainUndecided {
                    part,
                    reason,
                    count: 1,
                    first: first(),
                    bindings,
                },
            ),
        }
    }

    /// Record the completions at one state (module documentation, the witness order); returns
    /// the state's mark.
    fn record_completions(
        &mut self,
        completions: Vec<Completed>,
        clean: bool,
        diagnostics: &PathDiagnostics,
    ) -> MatchMark {
        let completed = u64::try_from(completions.len()).expect("a count fits in 64 bits");
        let Some(best) = best(completions) else {
            return MatchMark::Other;
        };
        if clean {
            self.keep_clean(best.completion(diagnostics));
        } else {
            self.found.dirty_completions += completed;
            if self.found.first_dirty_completion.is_none() {
                self.found.first_dirty_completion = Some(best.completion(diagnostics));
            }
        }
        MatchMark::Reach {
            term_conjunction: best.term_conjunction,
        }
    }

    /// The progress after a state: `partials` with the largest keys evicted beyond the cap, and
    /// the parent's own progress when nothing changed.
    fn progress(
        &mut self,
        parent: Option<&Rc<Progress>>,
        mut partials: BTreeMap<PartialKey, Payload>,
        clean: bool,
    ) -> Rc<Progress> {
        let was_overflowed = parent.is_some_and(|parent| parent.overflowed);
        let mut evicted = false;
        while partials.len() > self.partial_cap {
            partials.pop_last();
            evicted = true;
        }
        let kept = u64::try_from(partials.len()).expect("a count fits in 64 bits");
        self.found.peak_partials = self.found.peak_partials.max(kept);
        if evicted && !was_overflowed {
            self.found.overflowed_paths += 1;
        }
        let overflowed = was_overflowed || evicted;
        if let Some(parent) = parent
            && parent.overflowed == overflowed
            && parent.clean == clean
            && parent.partials == partials
        {
            return Rc::clone(parent);
        }
        Rc::new(Progress::new(partials, overflowed, clean, false))
    }

    /// Process the decided-or-not state `state` from the parent's `partials` (module
    /// documentation), isolated by the caller.
    fn process(
        &self,
        definition: &BackendDefinition,
        partials: &BTreeMap<PartialKey, Payload>,
        depth: u64,
        state: &Pattern,
    ) -> Outcome {
        let facts = StateFacts::new(state);
        let mut outcome = Outcome::default();
        let mut levels = vec![BTreeMap::<PartialKey, Candidate>::new(); self.steps.len()];
        levels[0].insert(
            PartialKey {
                next: 0,
                term_conjunction: false,
                bindings: Vec::new(),
            },
            Candidate {
                advance: Payload::default(),
                insert: None,
            },
        );
        for (key, payload) in partials {
            let kept = match &self.steps[key.next].unless {
                None => true,
                Some(unless) => {
                    outcome.evaluations += 1;
                    match self.unless_verdict(definition, unless, key, &facts) {
                        UnlessVerdict::Matched => false,
                        UnlessVerdict::Refuted => true,
                        UnlessVerdict::Undecided(reason) => {
                            outcome.undecided.push((
                                ChainPart::Unless(key.next),
                                reason,
                                key.bindings.clone(),
                            ));
                            false
                        }
                    }
                }
            };
            levels[key.next].insert(
                key.clone(),
                Candidate {
                    advance: payload.clone(),
                    insert: kept.then(|| payload.clone()),
                },
            );
        }
        for next in 0..self.steps.len() {
            let step = &self.steps[next];
            for (key, candidate) in std::mem::take(&mut levels[next]) {
                outcome.evaluations += 1;
                let (found, undecided) = self.step_ways(definition, step, &key, &facts);
                if let Some(reason) = undecided {
                    outcome
                        .undecided
                        .push((ChainPart::Step(next), reason, key.bindings.clone()));
                }
                for (values, bindings) in found {
                    let term_conjunction = key.term_conjunction || facts.conjunction();
                    let payload = candidate.advance.then(StepHit {
                        depth,
                        pattern: state.clone(),
                        bindings,
                    });
                    if next + 1 == self.steps.len() {
                        outcome.completions.push(Completed {
                            key: key.clone(),
                            payload,
                            term_conjunction,
                        });
                        continue;
                    }
                    let bindings = step
                        .next_key
                        .iter()
                        .map(|variable| {
                            let value = match step.carried.iter().position(|v| v == variable) {
                                Some(position) => values[position].clone(),
                                None => key_value(&key.bindings, variable).clone(),
                            };
                            (variable.clone(), value)
                        })
                        .collect();
                    offer(
                        &mut levels[next + 1],
                        PartialKey {
                            next: next + 1,
                            term_conjunction,
                            bindings,
                        },
                        payload,
                    );
                }
                if let Some(payload) = candidate.insert {
                    outcome.partials.insert(key, payload);
                }
            }
        }
        outcome
    }

    /// The ways `step`, instantiated by `key`, matches the state, keyed by the values of its
    /// carried exports, and why the match is undecided, if it is.
    fn step_ways(
        &self,
        definition: &BackendDefinition,
        step: &Step,
        key: &PartialKey,
        facts: &StateFacts<'_>,
    ) -> (
        BTreeMap<Vec<Term>, Substitution>,
        Option<UndecidedMatchReason>,
    ) {
        if !facts.decided {
            return (BTreeMap::new(), Some(UndecidedMatchReason::UndecidedState));
        }
        let target = instantiate(&step.target, &step.imports, &key.bindings);
        let ways = self
            .reader
            .ways(definition, &target, facts.pattern, &step.carried);
        if !ways.found.is_empty() && !facts.defined(definition) {
            return (BTreeMap::new(), Some(UndecidedMatchReason::NotCeilFree));
        }
        let reason = ways.incomplete.map(|incomplete| match incomplete {
            Incomplete::Undecided => UndecidedMatchReason::UndecidedMatch,
            Incomplete::Bounded => UndecidedMatchReason::PlacementBound,
        });
        (ways.found, reason)
    }

    /// The verdict of `unless`, instantiated by `key`, on the state.
    fn unless_verdict(
        &self,
        definition: &BackendDefinition,
        unless: &UnlessPart,
        key: &PartialKey,
        facts: &StateFacts<'_>,
    ) -> UnlessVerdict {
        if !facts.decided {
            return UnlessVerdict::Undecided(UndecidedMatchReason::UndecidedState);
        }
        let target = instantiate(&unless.target, &unless.imports, &key.bindings);
        let ways = self.reader.ways(definition, &target, facts.pattern, &[]);
        if !ways.found.is_empty() {
            return UnlessVerdict::Matched;
        }
        match ways.incomplete {
            None => UnlessVerdict::Refuted,
            Some(Incomplete::Undecided) => {
                UnlessVerdict::Undecided(UndecidedMatchReason::UndecidedMatch)
            }
            Some(Incomplete::Bounded) => {
                UnlessVerdict::Undecided(UndecidedMatchReason::PlacementBound)
            }
        }
    }
}

/// The witness among the completions at one state: the least by step depths, then key, with no
/// term-level `\and`, or the least with one when every completion holds one.
fn best(mut completions: Vec<Completed>) -> Option<Completed> {
    completions.sort_by(|left, right| left.rank().cmp(&right.rank()));
    let index = completions
        .iter()
        .position(|completed| !completed.term_conjunction)
        .unwrap_or(0);
    (index < completions.len()).then(|| completions.swap_remove(index))
}

/// Offer a partial created at a state to the level of the step it awaits: the level keeps, per
/// key, the partial whose step depths are least, the first offered on a tie.
fn offer(level: &mut BTreeMap<PartialKey, Candidate>, key: PartialKey, payload: Payload) {
    match level.entry(key) {
        Entry::Vacant(entry) => {
            entry.insert(Candidate {
                advance: payload.clone(),
                insert: Some(payload),
            });
        }
        Entry::Occupied(mut entry) => {
            let candidate = entry.get_mut();
            let depths = payload.depths();
            if depths < candidate.advance.depths() {
                candidate.advance = payload.clone();
            }
            match &candidate.insert {
                Some(kept) if kept.depths() <= depths => {}
                Some(_) | None => candidate.insert = Some(payload),
            }
        }
    }
}

/// The value `bindings` holds for `variable`, which the chain's key variables guarantee.
fn key_value<'b>(bindings: &'b [(Variable, Term)], variable: &Variable) -> &'b Term {
    bindings
        .iter()
        .find_map(|(bound, value)| (bound == variable).then_some(value))
        .expect("a key holds every variable the parts it awaits import")
}

/// `target` with the values `bindings` holds for `imports` substituted into its term and its
/// constraints.
fn instantiate(target: &Pattern, imports: &[Variable], bindings: &[(Variable, Term)]) -> Pattern {
    if imports.is_empty() {
        return target.clone();
    }
    let substitution: Substitution = imports
        .iter()
        .map(|import| (import.clone(), key_value(bindings, import).clone()))
        .collect();
    #[expect(
        clippy::disallowed_methods,
        reason = "each import is bound to a value of a state shown to exist (`ground_defined`), which denotes one element as the variable does, so the instance keeps the condition's definedness"
    )]
    let constraints = crate::rewrite::substitute_predicates(&target.constraints, &substitution);
    Pattern {
        term: substitute(&target.term, &substitution),
        constraints,
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::{
        builtin::ChosenClass,
        rewrite::{
            StateMatchOptions,
            state_match::{StateMatcher, StateWays},
        },
        rule::Predicate,
        simplify::{SimplificationOptions, simplify},
        smt::NoSolver,
        term::Sort,
    };

    const DEFINITION: &str = r#"[] module MAIN
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
            [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
        hooked-symbol leInt{}(SortInt{}, SortInt{}) : SortBool{}
            [function{}(), total{}(), hook{}("INT.le"), smt-hook{}("<=")]
        hooked-sort SortC{} [hook{}("MAP.Map"), unit{}(cUnit{}()), element{}(cItem{}()), concat{}(cConcat{}())]
        hooked-symbol cUnit{}() : SortC{} [function{}(), total{}(), hook{}("MAP.unit")]
        hooked-symbol cItem{}(SortInt{}, SortInt{}) : SortC{} [function{}(), total{}(), hook{}("MAP.element")]
        hooked-symbol cConcat{}(SortC{}, SortC{}) : SortC{}
            [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}(), unit{}(cUnit{}())]
        sort SortS{} []
        symbol st{}(SortInt{}, SortBool{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol ms{}(SortC{}, SortBool{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol h{}(SortInt{}) : SortInt{} [function{}()]
    endmodule []"#;

    fn load() -> BackendDefinition {
        let syntax = parse_definition(DEFINITION).expect("the definition parses");
        BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        let term = definition
            .internalize_term(&parse_pattern(source).unwrap(), &[])
            .expect("the term internalizes");
        simplify(definition, &term, SimplificationOptions::default())
            .expect("no stop is armed")
            .expect("the simplification succeeds")
            .term
    }

    fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
        Pattern {
            term: term(definition, source),
            constraints: Vec::new(),
        }
    }

    /// `source`, a Boolean term, is true.
    fn requires(definition: &BackendDefinition, target: &str, source: &str) -> Pattern {
        Pattern {
            term: term(definition, target),
            constraints: vec![Predicate::Equals(
                term(definition, source),
                term(definition, r#"\dv{SortBool{}}("true")"#),
            )],
        }
    }

    fn int(value: i64) -> String {
        format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
    }

    fn st(pc: &str, halted: bool) -> String {
        format!(r#"st{{}}({pc}, \dv{{SortBool{{}}}}("{halted}"))"#)
    }

    /// `ms(keys |-> 0, flag)`.
    fn ms(keys: &[i64], flag: bool) -> String {
        let map = keys
            .iter()
            .map(|key| format!("cItem{{}}({}, {})", int(*key), int(0)))
            .reduce(|left, right| format!("cConcat{{}}({left}, {right})"))
            .unwrap_or_else(|| "cUnit{}()".to_owned());
        format!(r#"ms{{}}({map}, \dv{{SortBool{{}}}}("{flag}"))"#)
    }

    fn var(name: &str) -> Variable {
        Variable::new(format!("Var{name}"), Sort::simple("SortInt"))
    }

    fn step(target: Pattern, imports: &[&str], exports: &[&str]) -> ChainStep {
        ChainStep {
            target,
            imports: imports.iter().map(|name| var(name)).collect(),
            exports: exports.iter().map(|name| var(name)).collect(),
            unless: None,
        }
    }

    fn unless(mut step: ChainStep, target: Pattern, imports: &[&str]) -> ChainStep {
        step.unless = Some(UnlessPart {
            target,
            imports: imports.iter().map(|name| var(name)).collect(),
        });
        step
    }

    fn matcher(steps: Vec<ChainStep>, partial_cap: usize, proof: bool) -> ChainMatcher<'static> {
        let chain = ChainOptions { steps, partial_cap }
            .checked()
            .expect("the chain is well formed");
        ChainMatcher::new(chain, proof, &NoSolver, 100)
    }

    /// Process `states` as one path, at depths 0, 1, …, returning each state's progress and mark.
    fn walk(
        matcher: &mut ChainMatcher<'_>,
        definition: &BackendDefinition,
        states: &[String],
    ) -> Vec<(Rc<Progress>, MatchMark)> {
        let diagnostics = PathDiagnostics::new_request();
        let mut parent: Option<Rc<Progress>> = None;
        let mut seen = Vec::new();
        for (depth, state) in states.iter().enumerate() {
            let observed = matcher.observe(
                definition,
                parent.as_ref(),
                depth as u64,
                &pattern(definition, state),
                &diagnostics,
            );
            parent = Some(Rc::clone(&observed.0));
            seen.push(observed);
        }
        seen
    }

    fn depths(completion: &ChainCompletion) -> Vec<u64> {
        completion.steps.iter().map(|hit| hit.depth).collect()
    }

    fn witness(matcher: &ChainMatcher<'_>) -> Option<Vec<u64>> {
        matcher.found.first_clean_completion.as_ref().map(depths)
    }

    fn keys(progress: &Progress) -> Vec<(usize, Vec<Term>)> {
        progress
            .partials()
            .keys()
            .map(|key| {
                (
                    key.next,
                    key.bindings
                        .iter()
                        .map(|(_, value)| value.clone())
                        .collect(),
                )
            })
            .collect()
    }

    /// The halt-bug shape: the step after the first is matched on every later state, not only the
    /// nearest one; it is refuted on states whose value differs from the one the first step
    /// bound, and the partial survives them until a later state matches.
    #[test]
    fn a_later_step_is_matched_on_every_later_state() {
        let definition = load();
        for proof in [false, true] {
            let mut chain = matcher(
                vec![
                    step(
                        pattern(&definition, &st("VarP:SortInt{}", true)),
                        &[],
                        &["P"],
                    ),
                    step(
                        pattern(&definition, &st("VarP:SortInt{}", false)),
                        &["P"],
                        &[],
                    ),
                ],
                256,
                proof,
            );
            let seen = walk(
                &mut chain,
                &definition,
                &[
                    st(&int(5), true),
                    st(&int(7), false),
                    st(&int(8), false),
                    st(&int(5), false),
                ],
            );
            assert_eq!(keys(&seen[0].0), [(1, vec![term(&definition, &int(5))])]);
            // The refuting states change nothing: the progress is shared.
            assert!(Rc::ptr_eq(&seen[0].0, &seen[1].0));
            assert!(Rc::ptr_eq(&seen[0].0, &seen[2].0));
            assert_eq!(seen[2].1, MatchMark::Other);
            assert_eq!(
                seen[3].1,
                MatchMark::Reach {
                    term_conjunction: false
                }
            );
            assert_eq!(witness(&chain), Some(vec![0, 3]));
            assert!(chain.done());
            assert!(seen[3].0.frozen());
            let found = chain.finish();
            assert!(found.undecided.is_empty(), "{found:?}");
            assert_eq!(found.states, 4);
            // One start per state, and the second step's match on the state the partial was
            // created at and on the three later ones.
            assert_eq!(found.evaluations, 8);
        }
    }

    /// An unless matched strictly between two steps' states kills the partial; one matched on the
    /// state a partial was created at, or on the state that ends its arrow, does not.
    #[test]
    fn an_unless_match_kills_the_partial_strictly_between_its_steps() {
        let definition = load();
        let chain = || {
            matcher(
                vec![
                    step(
                        pattern(&definition, &st("VarP:SortInt{}", true)),
                        &[],
                        &["P"],
                    ),
                    unless(
                        step(
                            pattern(&definition, &st("VarP:SortInt{}", false)),
                            &["P"],
                            &[],
                        ),
                        pattern(&definition, &st(&int(9), false)),
                        &[],
                    ),
                ],
                256,
                false,
            )
        };
        let mut killed = chain();
        let seen = walk(
            &mut killed,
            &definition,
            &[st(&int(5), true), st(&int(9), false), st(&int(5), false)],
        );
        assert!(seen[1].0.partials().is_empty());
        assert_eq!(witness(&killed), None);
        assert!(killed.finish().undecided.is_empty());

        let mut kept = chain();
        walk(
            &mut kept,
            &definition,
            &[st(&int(5), true), st(&int(6), false), st(&int(5), false)],
        );
        assert_eq!(witness(&kept), Some(vec![0, 2]));

        // The second step's state matches the unless too; it ends the arrow, so the chain
        // completes there.
        let mut at_end = chain();
        let seen = walk(
            &mut at_end,
            &definition,
            &[st(&int(9), true), st(&int(9), false)],
        );
        assert_eq!(witness(&at_end), Some(vec![0, 1]));
        assert!(seen[1].0.frozen());
    }

    /// An unless left undecided between two steps drops the partial, which never completes, and
    /// the drop is counted with the state and the partial's bindings.
    #[test]
    fn an_undecided_unless_drops_the_partial_and_is_counted() {
        let definition = load();
        let mut chain = matcher(
            vec![
                step(
                    pattern(&definition, &st("VarP:SortInt{}", true)),
                    &[],
                    &["P"],
                ),
                unless(
                    step(
                        pattern(&definition, &st("VarP:SortInt{}", false)),
                        &["P"],
                        &[],
                    ),
                    requires(
                        &definition,
                        &st("VarX:SortInt{}", false),
                        &format!("eqInt{{}}(h{{}}(VarX:SortInt{{}}), {})", int(0)),
                    ),
                    &[],
                ),
            ],
            256,
            false,
        );
        let seen = walk(
            &mut chain,
            &definition,
            &[st(&int(5), true), st(&int(6), false), st(&int(5), false)],
        );
        assert_eq!(keys(&seen[0].0).len(), 1);
        assert!(seen[1].0.partials().is_empty());
        assert_eq!(witness(&chain), None);
        let found = chain.finish();
        assert_eq!(found.dirty_completions, 0);
        let [undecided] = found.undecided.as_slice() else {
            panic!("one undecided entry: {found:?}");
        };
        assert_eq!(undecided.part, ChainPart::Unless(1));
        assert_eq!(undecided.reason, UndecidedMatchReason::UndecidedMatch);
        assert_eq!(undecided.count, 1);
        assert_eq!(undecided.first.depth, 1);
        assert_eq!(undecided.bindings, [(var("P"), term(&definition, &int(5)))]);
    }

    /// Consecutive steps may match one state, through an unless that matches it too: every
    /// partial on the way was created at that state, which ends its arrow.
    #[test]
    fn consecutive_steps_may_match_one_state() {
        let definition = load();
        let mut chain = matcher(
            vec![
                step(
                    pattern(&definition, &st("VarP:SortInt{}", true)),
                    &[],
                    &["P"],
                ),
                step(
                    pattern(&definition, &st("VarP:SortInt{}", true)),
                    &["P"],
                    &[],
                ),
                unless(
                    step(
                        requires(
                            &definition,
                            &st("VarQ:SortInt{}", true),
                            "leInt{}(VarP:SortInt{}, VarQ:SortInt{})",
                        ),
                        &["P"],
                        &[],
                    ),
                    pattern(&definition, &st("VarX:SortInt{}", true)),
                    &[],
                ),
            ],
            256,
            false,
        );
        walk(
            &mut chain,
            &definition,
            &[st(&int(3), false), st(&int(4), true)],
        );
        assert_eq!(witness(&chain), Some(vec![1, 1, 1]));
    }

    /// A partial created with the key of a live one is not kept: the live one has the earlier
    /// states, and the progress is unchanged.
    #[test]
    fn a_duplicate_key_keeps_the_earlier_partial() {
        let definition = load();
        let mut chain = matcher(
            vec![
                step(
                    pattern(&definition, &st("VarP:SortInt{}", true)),
                    &[],
                    &["P"],
                ),
                step(
                    pattern(&definition, &st("VarP:SortInt{}", false)),
                    &["P"],
                    &[],
                ),
            ],
            256,
            false,
        );
        let seen = walk(
            &mut chain,
            &definition,
            &[st(&int(5), true), st(&int(5), true), st(&int(5), false)],
        );
        assert!(Rc::ptr_eq(&seen[0].0, &seen[1].0));
        assert_eq!(witness(&chain), Some(vec![0, 2]));
    }

    /// Beyond the cap the largest keys are evicted and the path is marked overflowed, for good;
    /// an evicted partial never completes, a kept one still does.
    #[test]
    fn an_overflow_evicts_the_largest_keys_and_makes_no_completion() {
        let definition = load();
        let mut chain = matcher(
            vec![
                step(
                    pattern(&definition, &st("VarP:SortInt{}", true)),
                    &[],
                    &["P"],
                ),
                step(
                    pattern(&definition, &st("VarP:SortInt{}", false)),
                    &["P"],
                    &[],
                ),
            ],
            1,
            false,
        );
        let seen = walk(
            &mut chain,
            &definition,
            &[
                st(&int(5), true),
                st(&int(3), true),
                st(&int(5), false),
                st(&int(7), false),
            ],
        );
        assert!(!seen[0].0.overflowed());
        assert_eq!(keys(&seen[1].0), [(1, vec![term(&definition, &int(3))])]);
        assert!(seen[1].0.overflowed());
        assert!(seen[3].0.overflowed());
        assert_ne!(seen[0].0.digest(), seen[1].0.digest());
        assert_eq!(seen[2].1, MatchMark::Other);
        assert_eq!(witness(&chain), None);
        let found = chain.finish();
        assert_eq!(found.overflowed_paths, 1);
        assert_eq!(found.peak_partials, 1);

        let mut kept = matcher(
            vec![
                step(
                    pattern(&definition, &st("VarP:SortInt{}", true)),
                    &[],
                    &["P"],
                ),
                step(
                    pattern(&definition, &st("VarP:SortInt{}", false)),
                    &["P"],
                    &[],
                ),
            ],
            1,
            false,
        );
        walk(
            &mut kept,
            &definition,
            &[st(&int(5), true), st(&int(3), true), st(&int(3), false)],
        );
        assert_eq!(witness(&kept), Some(vec![1, 2]));
    }

    /// A `requires` of a later step that names a variable an earlier step bound is decided on the
    /// bound value, substituted before the match: refuted where it does not hold, matched where
    /// it does. The step's bindings hold its own variables only.
    #[test]
    fn a_later_requires_is_decided_on_the_earlier_binding() {
        let definition = load();
        let mut chain = matcher(
            vec![
                step(
                    pattern(&definition, &st("VarP:SortInt{}", true)),
                    &[],
                    &["P"],
                ),
                step(
                    requires(
                        &definition,
                        &st("VarQ:SortInt{}", false),
                        "leInt{}(VarP:SortInt{}, VarQ:SortInt{})",
                    ),
                    &["P"],
                    &[],
                ),
            ],
            256,
            true,
        );
        let seen = walk(
            &mut chain,
            &definition,
            &[st(&int(5), true), st(&int(4), false), st(&int(6), false)],
        );
        assert_eq!(seen[1].1, MatchMark::Other);
        let completion = chain
            .found
            .first_clean_completion
            .clone()
            .expect("a completion");
        assert_eq!(depths(&completion), [0, 2]);
        assert_eq!(
            completion.steps[1].bindings,
            Substitution::from([(var("Q"), term(&definition, &int(6)))])
        );
        assert_eq!(
            completion.steps[0].bindings,
            Substitution::from([(var("P"), term(&definition, &int(5)))])
        );
        assert!(chain.finish().undecided.is_empty());
    }

    /// Among completions at one state the least step depths win, then the least key; a partial
    /// created with the key of a kept one replaces it when its step depths are less.
    #[test]
    fn the_witness_at_one_state_has_the_least_steps_then_the_least_key() {
        let definition = load();
        let entry_chain = || {
            matcher(
                vec![
                    step(
                        pattern(
                            &definition,
                            r#"ms{}(cConcat{}(cItem{}(VarP:SortInt{}, VarV:SortInt{}), VarM:SortC{}), \dv{SortBool{}}("true"))"#,
                        ),
                        &[],
                        &["P"],
                    ),
                    step(
                        pattern(
                            &definition,
                            r#"ms{}(cConcat{}(cItem{}(VarP:SortInt{}, VarW:SortInt{}), VarN:SortC{}), \dv{SortBool{}}("false"))"#,
                        ),
                        &["P"],
                        &[],
                    ),
                ],
                256,
                false,
            )
        };
        let bound = |chain: &ChainMatcher<'_>| {
            chain
                .found
                .first_clean_completion
                .as_ref()
                .map(|completion| completion.steps[0].bindings[&var("P")].clone())
        };
        // One state binds P in two ways: the least key wins.
        let mut keyed = entry_chain();
        let seen = walk(
            &mut keyed,
            &definition,
            &[ms(&[3, 5], true), ms(&[3, 5], false)],
        );
        assert_eq!(keys(&seen[0].0).len(), 2);
        assert_eq!(witness(&keyed), Some(vec![0, 1]));
        assert_eq!(bound(&keyed), Some(term(&definition, &int(3))));
        // The earlier first step wins over the lesser key.
        let mut earlier = entry_chain();
        walk(
            &mut earlier,
            &definition,
            &[ms(&[5], true), ms(&[3], true), ms(&[3, 5], false)],
        );
        assert_eq!(witness(&earlier), Some(vec![0, 2]));
        assert_eq!(bound(&earlier), Some(term(&definition, &int(5))));

        // X is read by the second step only, so a partial awaiting the third keeps no value:
        // the partial X = 3 extended at depth 3 has the key of the one X = 5 extended at depth 2,
        // and replaces it, its step depths (0, 3) being less than (1, 2).
        let mut replaced = matcher(
            vec![
                step(
                    pattern(&definition, &st("VarX:SortInt{}", true)),
                    &[],
                    &["X"],
                ),
                step(
                    pattern(&definition, &st("VarX:SortInt{}", false)),
                    &["X"],
                    &[],
                ),
                step(pattern(&definition, &st(&int(0), true)), &[], &[]),
            ],
            256,
            false,
        );
        let seen = walk(
            &mut replaced,
            &definition,
            &[
                st(&int(3), true),
                st(&int(5), true),
                st(&int(5), false),
                st(&int(3), false),
                st(&int(0), true),
            ],
        );
        let awaiting_third = |progress: &Progress| {
            progress
                .partials()
                .iter()
                .filter(|(key, _)| key.next == 2)
                .map(|(_, payload)| payload.depths())
                .collect::<Vec<_>>()
        };
        assert_eq!(awaiting_third(&seen[2].0), [vec![1, 2]]);
        assert_eq!(awaiting_third(&seen[3].0), [vec![0, 3]]);
        assert_eq!(witness(&replaced), Some(vec![0, 3, 4]));
    }

    /// A chain of one step gives the state matcher's summary: the first clean reach (preferring
    /// one without a term-level `\and`), the first dirty reach and their count, the undecided
    /// states by reason, and the solver and stack counts.
    #[test]
    fn a_chain_of_one_step_matches_as_the_state_matcher() {
        let definition = load();
        let bounded = requires(
            &definition,
            &st("VarP:SortInt{}", true),
            &format!("leInt{{}}(VarP:SortInt{{}}, {})", int(4)),
        );
        let plain = pattern(&definition, &st("VarP:SortInt{}", true));
        let clean = PathDiagnostics::new_request();
        let mut dirty = clean.empty_like();
        dirty.extend(&[BackendDiagnostic::ImplementationChosenValue {
            hook: "MAP.choice".to_owned(),
            class: ChosenClass::Item,
        }]);
        let states = [
            (st("VarY:SortInt{}", true), &clean),
            (st(&format!("h{{}}({})", int(1)), true), &clean),
            (st(&int(2), true), &dirty),
            (st(&int(5), true), &clean),
            (st(&int(1), true), &dirty),
            (st(&int(3), true), &clean),
            (st(&int(0), true), &clean),
        ];
        // The `requires` leaves `h(1)` undecided; without it `h(1)` matches but is not shown to
        // exist.
        let cases = [
            (bounded, UndecidedMatchReason::UndecidedMatch),
            (plain, UndecidedMatchReason::NotCeilFree),
        ];
        for ((target, reason), proof) in cases.iter().flat_map(|case| [(case, false), (case, true)])
        {
            let solver = NoSolver;
            let mut single = StateMatcher::new(
                StateMatchOptions {
                    target: target.clone(),
                    proof_agreement: proof,
                    chain: None,
                },
                &solver,
                100,
            );
            let mut chain = matcher(vec![step(target.clone(), &[], &[])], 256, proof);
            let mut parent: Option<Rc<Progress>> = None;
            for (depth, (state, diagnostics)) in states.iter().enumerate() {
                let state = pattern(&definition, state);
                let depth = depth as u64;
                let mark = single.observe(&definition, depth, &state, diagnostics);
                let (progress, chain_mark) =
                    chain.observe(&definition, parent.as_ref(), depth, &state, diagnostics);
                assert_eq!(mark, chain_mark, "depth {depth}");
                parent = Some(progress);
            }
            let single = single.finish();
            let chain = chain.finish();
            let as_reach = |completion: &ChainCompletion| StateMatch {
                depth: completion.steps[0].depth,
                pattern: completion.steps[0].pattern.clone(),
                diagnostics: completion.diagnostics.clone(),
                term_conjunction: completion.term_conjunction,
            };
            assert!(single.first_clean_reach.is_some());
            assert_eq!(
                single.first_clean_reach,
                chain.first_clean_completion.as_ref().map(as_reach)
            );
            assert!(single.first_dirty_reach.is_some());
            assert_eq!(
                single.first_dirty_reach,
                chain.first_dirty_completion.as_ref().map(as_reach)
            );
            assert_eq!(single.dirty_reaches, chain.dirty_completions);
            assert_eq!(single.matched, chain.states);
            assert_eq!(single.smt_unknowns, chain.smt_unknowns);
            assert_eq!(single.stack_stops, chain.stack_stops);
            assert_eq!(
                single
                    .undecided
                    .iter()
                    .map(|entry| entry.reason)
                    .collect::<Vec<_>>(),
                [UndecidedMatchReason::UndecidedState, *reason]
            );
            assert_eq!(
                single
                    .undecided
                    .iter()
                    .map(|entry| (ChainPart::Step(0), entry.reason, entry.count, &entry.first))
                    .collect::<Vec<_>>(),
                chain
                    .undecided
                    .iter()
                    .map(|entry| (entry.part, entry.reason, entry.count, &entry.first))
                    .collect::<Vec<_>>()
            );
        }
    }

    /// The merge key holds the progress's digest and whether the path is clean up to the state
    /// itself; once matching is over there is none.
    #[test]
    fn the_merge_key_holds_the_progress_and_the_path_s_cleanness() {
        let definition = load();
        let mut chain = matcher(
            vec![
                step(
                    pattern(&definition, &st("VarP:SortInt{}", true)),
                    &[],
                    &["P"],
                ),
                step(
                    pattern(&definition, &st("VarP:SortInt{}", false)),
                    &["P"],
                    &[],
                ),
            ],
            256,
            false,
        );
        let clean = PathDiagnostics::new_request();
        let mut dirty = clean.empty_like();
        dirty.extend(&[BackendDiagnostic::ImplementationChosenValue {
            hook: "MAP.choice".to_owned(),
            class: ChosenClass::Item,
        }]);
        let (empty, _) = chain.observe(
            &definition,
            None,
            0,
            &pattern(&definition, &st(&int(4), false)),
            &clean,
        );
        let (started, _) = chain.observe(
            &definition,
            None,
            0,
            &pattern(&definition, &st(&int(5), true)),
            &clean,
        );
        let key = |progress, diagnostics| chain.merge_key(Some(progress), diagnostics);
        assert_eq!(key(&started, &clean), key(&started, &clean));
        assert_ne!(key(&started, &clean), key(&empty, &clean));
        assert_ne!(key(&started, &clean), key(&started, &dirty));
        let (_, mark) = chain.observe(
            &definition,
            Some(&started),
            1,
            &pattern(&definition, &st(&int(5), false)),
            &clean,
        );
        assert_eq!(
            mark,
            MatchMark::Reach {
                term_conjunction: false
            }
        );
        assert!(chain.done());
        assert_eq!(chain.merge_key(Some(&started), &clean), None);
    }

    /// Under proof agreement a way extends only when both modes found its key; the answer is
    /// complete only when both modes found the same keys and every way.
    #[test]
    fn proof_agreement_compares_the_sets_of_ways() {
        let definition = load();
        let value = |n| vec![term(&definition, &int(n))];
        let ways = |keys: &[i64], incomplete| StateWays {
            found: keys
                .iter()
                .map(|key| (value(*key), Substitution::new()))
                .collect(),
            incomplete,
        };
        assert_eq!(
            ways(&[1, 2], None).agreeing(ways(&[1, 2], None)),
            ways(&[1, 2], None)
        );
        assert_eq!(
            ways(&[1, 2], None).agreeing(ways(&[2, 3], None)),
            ways(&[2], Some(Incomplete::Undecided))
        );
        assert_eq!(
            ways(&[1], None).agreeing(ways(&[1], Some(Incomplete::Bounded))),
            ways(&[1], Some(Incomplete::Bounded))
        );
        assert_eq!(
            ways(&[1], Some(Incomplete::Undecided)).agreeing(ways(&[1], Some(Incomplete::Bounded))),
            ways(&[1], Some(Incomplete::Undecided))
        );
        assert_eq!(ways(&[], None).agreeing(ways(&[], None)), ways(&[], None));
    }

    /// Imports and exports must classify the chain's variables consistently.
    #[test]
    fn an_inconsistent_chain_is_refused() {
        let definition = load();
        let first = || {
            step(
                pattern(&definition, &st("VarP:SortInt{}", true)),
                &[],
                &["P"],
            )
        };
        let check = |steps| {
            ChainOptions {
                steps,
                partial_cap: 1,
            }
            .check()
        };
        assert!(check(vec![]).is_err());
        assert!(
            check(vec![
                first(),
                step(pattern(&definition, &st("VarP:SortInt{}", false)), &[], &[])
            ])
            .is_err()
        );
        assert!(
            check(vec![step(
                pattern(&definition, &st("VarP:SortInt{}", false)),
                &["P"],
                &[]
            )])
            .is_err()
        );
        assert!(
            check(vec![step(
                pattern(&definition, &st(&int(1), false)),
                &[],
                &["P"]
            )])
            .is_err()
        );
        assert!(
            check(vec![
                first(),
                step(
                    pattern(&definition, &st("VarP:SortInt{}", false)),
                    &["P"],
                    &[]
                )
            ])
            .is_ok()
        );
    }
}
