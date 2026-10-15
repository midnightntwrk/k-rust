//! Stable transition identities and opt-in structured observation contracts.

use std::{
    collections::BTreeMap,
    collections::BTreeSet,
    fmt, io,
    sync::{Arc, OnceLock},
};

use k_rust_kore::kore::printer::Printer;
use sha2::{Digest, Sha256};

use crate::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    externalize,
    rewrite::Pattern,
    rewrite::{AppliedRule, RemainderBranch},
    rule::Predicate,
    substitution::Substitution,
};

/// A stable SHA-256 digest of a constrained pattern's canonical compact KORE form.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PatternDigest([u8; 32]);

impl PatternDigest {
    pub fn of(pattern: &Pattern) -> Self {
        let mut writer = DigestWriter(Sha256::new());
        let printable = externalize::Printable::pattern(pattern);
        Printer::compact()
            .write_source(
                externalize::External::Constrained(printable.source()),
                &mut writer,
            )
            .expect("writing to a SHA-256 digest cannot fail");
        Self(writer.0.finalize().into())
    }

    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    pub const fn into_bytes(self) -> [u8; 32] {
        self.0
    }
}

struct DigestWriter(Sha256);

impl io::Write for DigestWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.0.update(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl fmt::Display for PatternDigest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(formatter, "{byte:02x}")?;
        }
        Ok(())
    }
}

/// Definition-derived identity for a committed transition and its successor.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TransitionId {
    pub rule: String,
    pub target: PatternDigest,
}

/// The kind of committed transition a transition observation records.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TransitionClass {
    Rewrite,
    Remainder,
    /// Reserved for a circularity or trusted claim applied inside an observable proof.
    /// No operation emits this class yet.
    Claim,
}

/// The kind of rule applied while normalizing a branch state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvaluationClass {
    FunctionEquation,
    Simplification,
    Builtin,
}

/// Structured evidence for one committed transition of a branch.
///
/// Every transition observation names, by `id`, an element of the branch it is reported on, in
/// branch order; under a rule filter only the admitted elements are reported.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TransitionObservation {
    pub id: TransitionId,
    pub class: TransitionClass,
    pub rule_label: Option<String>,
    pub bindings: Substitution,
    pub introduced_predicates: Vec<Predicate>,
    pub before: Pattern,
    pub after: Pattern,
    pub effects: Vec<BuiltinEffect>,
}

/// One equation, simplification, or builtin application performed while normalizing a state of
/// a branch.
///
/// Normalization rewrites a state to an equal state; it is not a transition, and the branch
/// records no identity for it. `anchor` places it on the branch: it is the number of committed
/// transitions (branch entries, filtered or not) that precede it, so the normalized state is the
/// one reached by `branch[..anchor]` (the initial state when `anchor` is 0), or that state
/// restricted by the negated conditions of higher-priority rules when the next transition is a
/// lower-priority rewrite. Anchors are non-decreasing along a branch's observations.
///
/// Evaluations are recorded for the normalization passes of branch states: the term normalization
/// of the initial state and of every rewrite successor and remainder, the normalization of a
/// higher-priority remainder before a lower-priority rewrite, the normalization of each candidate
/// successor at a branch stop, and the pattern normalization of a state leaving the engine as a
/// leaf or search result. A candidate's normalization is recorded after its transition, on the
/// branch it extends: a candidate that continues as the only successor keeps it, and a candidate
/// that a `Branch` or `CutPointRule` halt reports without committing carries its events in its own
/// `observations` (a cut-point rule is proposed, not committed, so neither the rule nor its
/// successor's normalization is on that leaf's branch, unless the leaf reports the successor's
/// pattern because its normalization failed or is bottom). Constraint simplification at the start
/// of a step reports none. Evaluations performed while deciding a rule's side conditions or
/// building its right-hand side belong to that rule's application, committed or not, and are not
/// reported. Evaluations of a state that is later dropped (a candidate or remainder that simplifies
/// to bottom, a leaf merged into an equal leaf, leaves the breadth bound discards) are reported on
/// no branch. Which evaluations occur, how often, and in which order depends on the simplifier's
/// strategy, so these events are diagnostics: their absence is not evidence that an equation does
/// not apply.
///
/// `before` and `after` are the endpoints of the whole normalization pass, shared by every
/// evaluation that pass performed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluationObservation {
    pub rule: String,
    pub class: EvaluationClass,
    pub rule_label: Option<String>,
    pub anchor: usize,
    pub before: Pattern,
    pub after: Pattern,
    pub effects: Vec<BuiltinEffect>,
}

/// Why an attempted transition was not committed to a surviving branch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UncommittedReason {
    RolledBack,
}

/// Structured evidence retained outside a committed branch stream.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UncommittedObservation {
    pub id: TransitionId,
    pub rule_label: Option<String>,
    pub effects: Vec<BuiltinEffect>,
    pub reason: UncommittedReason,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ObservationEvent {
    Transition(TransitionObservation),
    Evaluation(EvaluationObservation),
    Uncommitted(UncommittedObservation),
}

/// One ordered write to a console descriptor on an execution branch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DescriptorTranscriptEntry {
    /// The hook that produced this write.
    pub hook: &'static str,
    pub descriptor: i32,
    pub bytes: Arc<[u8]>,
}

/// What a process observes of a branch's console: how many input bytes the branch consumed, and
/// the bytes it wrote, in order, as runs to one descriptor.
///
/// A process reading the console sees each descriptor's byte stream and, where the streams share
/// a terminal, how writes to different descriptors interleave; it does not see which hook wrote a
/// byte, how the bytes were split into calls, or a call that wrote none. So `writes` is the
/// transcript with empty writes dropped and each maximal run of adjacent writes to one descriptor
/// joined into one entry, and two consoles over the same input are observably equal exactly when
/// their observations are. The input is not part of an observation: it is one value shared by
/// every branch of an execution.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct ConsoleObservation {
    /// The number of input bytes read, the branch's cursor.
    pub consumed: usize,
    /// The bytes written, in order, as `(descriptor, bytes)`: no entry is empty, and adjacent
    /// entries have different descriptors.
    pub writes: Vec<(i32, Arc<[u8]>)>,
}

/// Buffered console state owned by one execution branch.
///
/// Input is immutable and shared between forks. The cursor and transcript are values of the
/// branch. The transcript is a shared-prefix list: a fork clones a handle to its newest write in
/// constant time, and a write appended on one branch is seen by that branch only. It also keeps
/// the running length and digest of its observable form ([`Self::observable_fingerprint`]). The
/// transcript is materialised as a slice once per state, when [`Self::transcript`] or
/// [`Self::observable`] first reads it.
#[derive(Clone, Default)]
pub struct ExecutionIoState {
    input: Arc<[u8]>,
    cursor: usize,
    transcript: SharedLog<DescriptorTranscriptEntry>,
    /// The bytes of non-empty writes, and the digest of the observable form, so far.
    written: usize,
    digest: RunningDigest,
    /// The descriptor of the latest non-empty write, which starts the current observable run.
    last_descriptor: Option<i32>,
    /// `transcript` as a slice, computed on first read and shared by the clones that hold the
    /// same transcript; an append replaces it.
    materialised: Arc<OnceLock<Vec<DescriptorTranscriptEntry>>>,
}

/// A filter for comparing consoles as a process observes them: equal observations
/// ([`ExecutionIoState::observable`]) have equal fingerprints. Different fingerprints prove the
/// observations different; equal ones do not prove them equal, so equality is decided on the
/// observations themselves.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "the state-set exploration merge, which compares states by fingerprint first, is not built yet"
    )
)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ConsoleFingerprint {
    consumed: usize,
    written: usize,
    digest: RunningDigest,
}

impl ExecutionIoState {
    pub fn new(input: impl Into<Arc<[u8]>>) -> Self {
        Self {
            input: input.into(),
            ..Self::default()
        }
    }

    pub fn input(&self) -> &[u8] {
        &self.input
    }

    pub const fn cursor(&self) -> usize {
        self.cursor
    }

    pub fn remaining_input(&self) -> &[u8] {
        &self.input[self.cursor..]
    }

    pub fn transcript(&self) -> &[DescriptorTranscriptEntry] {
        self.materialised.get_or_init(|| self.transcript.to_vec())
    }

    /// This console as a process observes it (see [`ConsoleObservation`]). The transcript keeps
    /// each write's hook and call boundaries for diagnostics; this is the form two consoles are
    /// compared in.
    pub fn observable(&self) -> ConsoleObservation {
        let mut writes = Vec::<(i32, Arc<[u8]>)>::new();
        let mut entries = self
            .transcript()
            .iter()
            .filter(|entry| !entry.bytes.is_empty())
            .peekable();
        while let Some(first) = entries.next() {
            let descriptor = first.descriptor;
            let same_descriptor =
                |entry: &&DescriptorTranscriptEntry| entry.descriptor == descriptor;
            if entries.peek().is_none_or(|next| !same_descriptor(next)) {
                writes.push((descriptor, Arc::clone(&first.bytes)));
                continue;
            }
            let mut bytes = first.bytes.to_vec();
            while let Some(next) = entries.next_if(same_descriptor) {
                bytes.extend_from_slice(&next.bytes);
            }
            writes.push((descriptor, bytes.into()));
        }
        ConsoleObservation {
            consumed: self.cursor,
            writes,
        }
    }

    /// The fingerprint of [`Self::observable`], in constant time: the input consumed, the bytes
    /// written, and a digest folded over the observable form as the writes were appended (each
    /// run's descriptor, then its bytes), so writes split differently, or with empty writes
    /// between them, fold to the same digest.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the state-set exploration merge, which compares states by fingerprint first, is not built yet"
        )
    )]
    pub(crate) fn observable_fingerprint(&self) -> ConsoleFingerprint {
        ConsoleFingerprint {
            consumed: self.cursor,
            written: self.written,
            digest: self.digest,
        }
    }

    /// Fork a tentative evaluator state from this branch.
    ///
    /// Dropping the context rolls every read and write back. `commit` returns the updated state
    /// for the caller to attach to the retained successor.
    pub(crate) fn begin_evaluation(&self) -> ExecutionEvaluationContext {
        ExecutionEvaluationContext {
            state: self.clone(),
        }
    }

    fn append(&mut self, entry: DescriptorTranscriptEntry) {
        if !entry.bytes.is_empty() {
            if self.last_descriptor != Some(entry.descriptor) {
                self.digest.fold_marker(entry.descriptor);
                self.last_descriptor = Some(entry.descriptor);
            }
            self.digest.fold_bytes(&entry.bytes);
            self.written += entry.bytes.len();
        }
        self.transcript.push(entry);
        self.materialised = Arc::default();
    }
}

impl PartialEq for ExecutionIoState {
    fn eq(&self, other: &Self) -> bool {
        self.cursor == other.cursor
            && self.input == other.input
            && self.transcript == other.transcript
    }
}

impl Eq for ExecutionIoState {}

impl fmt::Debug for ExecutionIoState {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ExecutionIoState")
            .field("input", &self.input)
            .field("cursor", &self.cursor)
            .field("transcript", &self.transcript())
            .finish()
    }
}

/// The console capability available to an impure builtin candidate.
///
/// This context owns only buffered semantic state. It has no process handles and cannot read from
/// or write to the host. Candidate selection commits it by attaching `commit()`'s result to the
/// selected successor; a failed candidate is rolled back by dropping the context.
#[derive(Debug)]
pub(crate) struct ExecutionEvaluationContext {
    state: ExecutionIoState,
}

impl ExecutionEvaluationContext {
    pub(crate) fn read(&mut self, maximum: usize) -> &[u8] {
        let start = self.state.cursor;
        let end = start.saturating_add(maximum).min(self.state.input.len());
        self.state.cursor = end;
        &self.state.input[start..end]
    }

    pub(crate) fn append(
        &mut self,
        hook: &'static str,
        descriptor: i32,
        bytes: impl Into<Arc<[u8]>>,
    ) {
        self.state.append(DescriptorTranscriptEntry {
            hook,
            descriptor,
            bytes: bytes.into(),
        });
    }

    pub(crate) fn commit(self) -> ExecutionIoState {
        self.state
    }

    /// The console state now, for [`Self::restore`]: the cursor and the transcript are values,
    /// so this copies a few shared pointers and numbers.
    pub(crate) fn snapshot(&self) -> ExecutionIoState {
        self.state.clone()
    }

    /// Return to `snapshot`: every read since is unread and every write since unwritten.
    pub(crate) fn restore(&mut self, snapshot: ExecutionIoState) {
        self.state = snapshot;
    }

    /// The position of the next byte a read takes from the input.
    pub(crate) const fn cursor(&self) -> usize {
        self.state.cursor
    }

    /// Whether nothing was read or written since `snapshot`: input is only consumed and the
    /// transcript only grows.
    pub(crate) fn unchanged_since(&self, snapshot: &ExecutionIoState) -> bool {
        self.state.cursor == snapshot.cursor
            && self.state.transcript.len() == snapshot.transcript.len()
    }
}

/// Effects owned by the committed prefix of one execution branch.
///
/// Simplification and rule application return candidate effects as ordinary vectors. The
/// execution loop may append them here only when it retains that candidate as a successor. The
/// journal is a shared-prefix list: a branch clones a handle to its newest effect with its
/// semantic state in constant time, and an effect committed on one branch is seen by that branch
/// only, so effects from sibling, rolled-back, or pruned candidates cannot enter another branch's
/// transcript. It keeps its length and a running digest ([`Self::fingerprint`]) and is
/// materialised once, when the branch ends in a leaf.
#[derive(Clone, Default)]
pub(crate) struct EffectJournal {
    committed: SharedLog<BuiltinEffect>,
    digest: RunningDigest,
}

/// A filter for comparing effect journals: equal journals have equal fingerprints, and equality
/// is decided on the journals themselves.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "the state-set exploration merge, which compares states by fingerprint first, is not built yet"
    )
)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct JournalFingerprint {
    len: usize,
    digest: RunningDigest,
}

impl EffectJournal {
    pub(crate) fn commit(&mut self, effects: impl IntoIterator<Item = BuiltinEffect>) {
        for effect in effects {
            self.digest.fold_effect(&effect);
            self.committed.push(effect);
        }
    }

    pub(crate) fn into_committed(self) -> Vec<BuiltinEffect> {
        self.committed.into_vec()
    }

    /// The fingerprint of the committed effects, in constant time.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the state-set exploration merge, which compares states by fingerprint first, is not built yet"
        )
    )]
    pub(crate) fn fingerprint(&self) -> JournalFingerprint {
        JournalFingerprint {
            len: self.committed.len(),
            digest: self.digest,
        }
    }
}

impl PartialEq for EffectJournal {
    fn eq(&self, other: &Self) -> bool {
        self.digest == other.digest && self.committed == other.committed
    }
}

impl Eq for EffectJournal {}

impl fmt::Debug for EffectJournal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("EffectJournal")
            .field("committed", &self.committed.to_vec())
            .finish()
    }
}

/// A sequence appended at its end and shared, prefix by prefix, by the clones it was forked
/// into: each node points at its predecessor, so a clone is constant time and an append adds one
/// node only its appender holds.
struct SharedLog<T> {
    newest: Option<Arc<LogNode<T>>>,
    len: usize,
}

struct LogNode<T> {
    /// Always present, except while [`SharedLog::into_vec`] moves it out of a node it owns.
    item: Option<T>,
    parent: Option<Arc<LogNode<T>>>,
}

impl<T> Default for SharedLog<T> {
    fn default() -> Self {
        Self {
            newest: None,
            len: 0,
        }
    }
}

impl<T> Clone for SharedLog<T> {
    fn clone(&self) -> Self {
        Self {
            newest: self.newest.clone(),
            len: self.len,
        }
    }
}

impl<T> SharedLog<T> {
    fn push(&mut self, item: T) {
        self.newest = Some(Arc::new(LogNode {
            item: Some(item),
            parent: self.newest.take(),
        }));
        self.len += 1;
    }

    const fn len(&self) -> usize {
        self.len
    }

    /// The items newest first.
    fn iter_newest_first(&self) -> impl Iterator<Item = &T> {
        std::iter::successors(self.newest.as_deref(), |node| node.parent.as_deref())
            .filter_map(|node| node.item.as_ref())
    }

    /// Whether `self` and `other` hold the same newest node, so that each item is stored once.
    #[cfg(test)]
    fn shares_items_with(&self, other: &Self) -> bool {
        match (&self.newest, &other.newest) {
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<T: Clone> SharedLog<T> {
    /// The items, oldest first.
    fn to_vec(&self) -> Vec<T> {
        let mut items = Vec::with_capacity(self.len);
        items.extend(self.iter_newest_first().cloned());
        items.reverse();
        items
    }

    /// The items, oldest first, for the owner that ends the log: an item no other clone shares
    /// is moved out, and only the items shared with another clone are cloned.
    fn into_vec(mut self) -> Vec<T> {
        let mut items = Vec::with_capacity(self.len);
        let mut node = self.newest.take();
        while let Some(current) = node {
            match Arc::try_unwrap(current) {
                Ok(mut owned) => {
                    items.extend(owned.item.take());
                    node = owned.parent.take();
                }
                Err(shared) => {
                    let rest = SharedLog {
                        newest: Some(shared),
                        len: 0,
                    };
                    items.extend(rest.iter_newest_first().cloned());
                    break;
                }
            }
        }
        items.reverse();
        items
    }
}

impl<T: PartialEq> PartialEq for SharedLog<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        let mut left = self.newest.as_ref();
        let mut right = other.newest.as_ref();
        while let (Some(l), Some(r)) = (left, right) {
            if Arc::ptr_eq(l, r) {
                return true;
            }
            if l.item != r.item {
                return false;
            }
            left = l.parent.as_ref();
            right = r.parent.as_ref();
        }
        true
    }
}

impl<T> Drop for LogNode<T> {
    /// Unlink a long unshared chain iteratively rather than by recursive drops.
    fn drop(&mut self) {
        let mut parent = self.parent.take();
        while let Some(node) = parent {
            match Arc::try_unwrap(node) {
                Ok(mut node) => parent = node.parent.take(),
                Err(_) => break,
            }
        }
    }
}

/// A 128-bit digest folded symbol by symbol, in two independent multiply-xor lanes. A filter
/// only: it is never the reason two sequences are taken as equal.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct RunningDigest {
    low: u64,
    high: u64,
}

impl Default for RunningDigest {
    fn default() -> Self {
        Self {
            low: 0xcbf2_9ce4_8422_2325,
            high: 0x6c62_272e_07bb_0142,
        }
    }
}

impl RunningDigest {
    fn fold(&mut self, symbol: u64) {
        self.low = (self.low ^ symbol).wrapping_mul(0x0000_0100_0000_01b3);
        self.high = (self.high ^ symbol.rotate_left(29) ^ (symbol >> 7))
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .rotate_left(31);
    }

    /// Symbols at or above 2^32 never equal a byte, so a marker cannot be confused with data.
    fn fold_marker(&mut self, descriptor: i32) {
        self.fold((1 << 32) | u64::from(descriptor as u32));
    }

    fn fold_bytes(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.fold(u64::from(*byte));
        }
    }

    /// Each effect folds its kind as a marker, then its content and its length, so that a
    /// sequence of effects folds to one symbol sequence that determines it.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn fold_effect(&mut self, effect: &BuiltinEffect) {
        match effect {
            BuiltinEffect::UserLog(text) => {
                self.fold(2 << 32);
                self.fold_bytes(text.as_bytes());
                self.fold((3 << 32) | text.len() as u64);
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObservationOptions {
    rules: Option<BTreeSet<String>>,
}

impl ObservationOptions {
    /// Observe every supported activity.
    pub const fn all() -> Self {
        Self { rules: None }
    }

    /// Construct an immutable executable-rule allowlist.
    ///
    /// Validation is atomic: every id must identify one executable rewrite, function equation,
    /// simplification, or definedness rule, and exactly one classified axiom of any kind in the
    /// selected definition. `builtin:<hook>` ids are observable only with `all`.
    /// Written axioms that are equal up to their origins and a renaming of variables were
    /// internalized as one rule, so an id is ambiguous only when the axioms carrying it differ.
    pub fn with_rules<I, S>(
        definition: &BackendDefinition,
        rules: I,
    ) -> Result<Self, ObservationFilterError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let mut available = BTreeMap::<(String, Option<usize>), usize>::new();
        let mut identity_counts = BTreeMap::<&str, usize>::new();
        for axiom in definition.classified_axioms() {
            *identity_counts
                .entry(axiom.attributes().unique_id.as_str())
                .or_default() += 1;
        }
        for priorities in definition.rewrite_theory().values() {
            for rules in priorities.values() {
                for rule in rules {
                    *available
                        .entry((
                            rule.rule.attributes.unique_id.clone(),
                            rule.rule.lhs_alternative,
                        ))
                        .or_default() += 1;
                }
            }
        }
        for theory in [
            definition.function_theory(),
            definition.simplification_theory(),
            definition.ceil_theory(),
        ] {
            for priorities in theory.values() {
                for rules in priorities.values() {
                    for rule in rules {
                        *available
                            .entry((rule.attributes.unique_id.clone(), rule.lhs_alternative))
                            .or_default() += 1;
                    }
                }
            }
        }

        let mut selected = BTreeSet::new();
        for rule in rules.into_iter().map(Into::into) {
            if !selected.insert(rule.clone()) {
                return Err(ObservationFilterError::DuplicateRule(rule));
            }
            let counts = available
                .iter()
                .filter_map(|((id, _), count)| (id == &rule).then_some(*count))
                .collect::<Vec<_>>();
            if counts.is_empty() {
                return Err(ObservationFilterError::UnknownRule(rule));
            }
            if counts.iter().any(|count| *count > 1)
                || identity_counts
                    .get(rule.as_str())
                    .is_some_and(|count| *count > 1)
            {
                return Err(ObservationFilterError::AmbiguousRule(rule));
            }
        }
        Ok(Self {
            rules: Some(selected),
        })
    }

    pub(crate) fn observes(&self, rule: &str) -> bool {
        self.rules
            .as_ref()
            .is_none_or(|selected| selected.contains(rule))
    }

    pub(crate) const fn rules_are_unfiltered(&self) -> bool {
        self.rules.is_none()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ObservationFilterError {
    UnknownRule(String),
    DuplicateRule(String),
    AmbiguousRule(String),
}

impl fmt::Display for ObservationFilterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownRule(rule) => write!(
                formatter,
                "no executable rewrite, function equation, simplification or definedness rule \
                 has the id '{rule}'"
            ),
            Self::DuplicateRule(rule) => {
                write!(formatter, "the rule id '{rule}' is listed more than once")
            }
            Self::AmbiguousRule(rule) => write!(
                formatter,
                "the rule id '{rule}' is carried by axioms that differ, so it names no one rule"
            ),
        }
    }
}

impl std::error::Error for ObservationFilterError {}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) struct ObservationNodeId(usize);

pub(crate) type ObservationHead = Option<ObservationNodeId>;

struct ObservationNode {
    parent: ObservationHead,
    /// Committed transitions on the chain ending at this node, this node's included.
    transitions: usize,
    transition: Option<TransitionId>,
    event: Option<ObservationEvent>,
}

#[derive(Default)]
pub(crate) struct ObservationLog {
    nodes: Vec<ObservationNode>,
}

impl ObservationLog {
    pub(crate) fn append_applied(
        &mut self,
        parent: ObservationHead,
        applied: &AppliedRule,
        options: Option<&ObservationOptions>,
    ) -> ObservationHead {
        let options = options?;
        let id = TransitionId {
            rule: applied.unique_id.clone(),
            target: PatternDigest::of(&applied.pattern),
        };
        let event = options.observes(&applied.unique_id).then(|| {
            ObservationEvent::Transition(TransitionObservation {
                id: id.clone(),
                class: TransitionClass::Rewrite,
                rule_label: applied.label.clone(),
                bindings: applied.rule_substitution.clone(),
                introduced_predicates: applied.rule_predicates.clone(),
                before: applied.before.clone(),
                after: applied.pattern.clone(),
                effects: applied.effects.clone(),
            })
        });
        Some(self.push(parent, Some(id), event))
    }

    pub(crate) fn append_remainder(
        &mut self,
        parent: ObservationHead,
        before: Pattern,
        remainder: &RemainderBranch,
        options: Option<&ObservationOptions>,
    ) -> ObservationHead {
        let options = options?;
        let id = TransitionId {
            rule: format!("remainder:{}", remainder.rule_ids.join(",")),
            target: PatternDigest::of(&remainder.pattern),
        };
        let event = options.rules_are_unfiltered().then(|| {
            ObservationEvent::Transition(TransitionObservation {
                id: id.clone(),
                class: TransitionClass::Remainder,
                rule_label: None,
                bindings: Substitution::new(),
                introduced_predicates: Vec::new(),
                before,
                after: remainder.pattern.clone(),
                effects: Vec::new(),
            })
        });
        Some(self.push(parent, Some(id), event))
    }

    /// Record the evaluations of one normalization pass of the state at `parent`'s branch
    /// position; see [`EvaluationObservation`] for the anchor.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn append_simplification(
        &mut self,
        mut parent: ObservationHead,
        definition: &BackendDefinition,
        before: Pattern,
        after: &Pattern,
        applied_rules: &[String],
        effects: &[BuiltinEffect],
        options: Option<&ObservationOptions>,
    ) -> ObservationHead {
        let options = options?;
        let anchor = self.transitions(parent);
        let mut effects = effects.iter().peekable();
        for rule in applied_rules {
            let class = evaluation_class(definition, rule);
            let attributed_effects = if let Some(hook) = rule.strip_prefix("builtin:")
                && class == EvaluationClass::Builtin
                && effects.peek().is_some_and(|effect| effect.hook() == hook)
            {
                vec![effects.next().expect("peeked effect").clone()]
            } else {
                Vec::new()
            };
            if !options.observes(rule) {
                continue;
            }
            parent = Some(self.push(
                parent,
                None,
                Some(ObservationEvent::Evaluation(EvaluationObservation {
                    rule: rule.clone(),
                    class,
                    rule_label: equation_label(definition, rule),
                    anchor,
                    before: before.clone(),
                    after: after.clone(),
                    effects: attributed_effects,
                })),
            ));
        }
        parent
    }

    pub(crate) fn materialize(
        &self,
        mut head: ObservationHead,
    ) -> (Vec<TransitionId>, Vec<ObservationEvent>) {
        let mut branch = Vec::new();
        let mut events = Vec::new();
        while let Some(id) = head {
            let node = &self.nodes[id.0];
            if let Some(transition) = &node.transition {
                branch.push(transition.clone());
            }
            if let Some(event) = &node.event {
                events.push(event.clone());
            }
            head = node.parent;
        }
        branch.reverse();
        events.reverse();
        (branch, events)
    }

    /// The events recorded on the chain from `ancestor` (exclusive) to `head`, in order.
    /// `ancestor` must be on `head`'s chain.
    pub(crate) fn events_since(
        &self,
        mut head: ObservationHead,
        ancestor: ObservationHead,
    ) -> Vec<ObservationEvent> {
        let mut events = Vec::new();
        while head != ancestor {
            let id = head.expect("the ancestor is on the chain");
            let node = &self.nodes[id.0];
            events.extend(node.event.clone());
            head = node.parent;
        }
        events.reverse();
        events
    }

    fn transitions(&self, head: ObservationHead) -> usize {
        head.map_or(0, |id| self.nodes[id.0].transitions)
    }

    fn push(
        &mut self,
        parent: ObservationHead,
        transition: Option<TransitionId>,
        event: Option<ObservationEvent>,
    ) -> ObservationNodeId {
        let transitions = self.transitions(parent) + usize::from(transition.is_some());
        let id = ObservationNodeId(self.nodes.len());
        self.nodes.push(ObservationNode {
            parent,
            transitions,
            transition,
            event,
        });
        id
    }
}

fn evaluation_class(definition: &BackendDefinition, rule_id: &str) -> EvaluationClass {
    if rule_id.starts_with("builtin:") {
        return EvaluationClass::Builtin;
    }
    if theory_contains_rule(definition.function_theory(), rule_id) {
        EvaluationClass::FunctionEquation
    } else {
        EvaluationClass::Simplification
    }
}

fn equation_label(definition: &BackendDefinition, rule_id: &str) -> Option<String> {
    [
        definition.function_theory(),
        definition.simplification_theory(),
    ]
    .into_iter()
    .flat_map(|theory| theory.values())
    .flat_map(|priorities| priorities.values())
    .flatten()
    .find(|rule| rule.attributes.unique_id == rule_id)
    .and_then(|rule| rule.attributes.label.clone())
}

fn theory_contains_rule(theory: &crate::rule::Theory, rule_id: &str) -> bool {
    theory
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
        .any(|rule| rule.attributes.unique_id == rule_id)
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::{
        ConsoleObservation, DescriptorTranscriptEntry, EffectJournal, EvaluationClass,
        ExecutionIoState, ObservationEvent, ObservationOptions,
    };
    use crate::{
        builtin::BuiltinEffect,
        definition::BackendDefinition,
        rewrite::{ExecutionOptions, Pattern, execute_observed},
    };

    /// A filtered-out rewrite is still a committed transition of the branch, so the evaluation
    /// of its successor is anchored after it.
    #[test]
    fn evaluation_anchor_counts_transitions_the_filter_excludes() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol value{}() : SortS{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \top{R}()),
                    \equals{SortS{}, R}(
                        value{}(),
                        \and{SortS{}}(\dv{SortS{}}("value"), \top{SortS{}}())
                    )
                ) [label{}("value")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                    value{}()
                ) [label{}("step")]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let initial = Pattern {
            term: definition
                .internalize_term(&parse_pattern("wrap{}(value{}())").unwrap(), &[])
                .unwrap(),
            constraints: Vec::new(),
        };
        let options = ObservationOptions::with_rules(&definition, ["value"]).unwrap();

        let result = execute_observed(&definition, initial, ExecutionOptions::default(), &options);

        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one leaf: {:?}", result.leaves);
        };
        assert_eq!(leaf.branch.len(), 1);
        assert_eq!(leaf.branch[0].rule, "step");
        let anchors = leaf
            .observations
            .iter()
            .map(|event| match event {
                ObservationEvent::Evaluation(evaluation) => {
                    assert_eq!(evaluation.rule, "value");
                    assert_eq!(evaluation.class, EvaluationClass::FunctionEquation);
                    evaluation.anchor
                }
                other => panic!("the filter selects only the equation: {other:?}"),
            })
            .collect::<Vec<_>>();
        assert_eq!(anchors, [0, 1]);
    }

    #[test]
    fn evaluation_reads_prebuffered_input_in_order() {
        let state = ExecutionIoState::new(Vec::from(&b"abcd"[..]));
        let mut evaluation = state.begin_evaluation();

        assert_eq!(evaluation.read(2), b"ab");
        assert_eq!(evaluation.read(3), b"cd");
        assert_eq!(evaluation.read(1), b"");

        let committed = evaluation.commit();
        assert_eq!(committed.cursor(), 4);
        assert_eq!(committed.remaining_input(), b"");
    }

    #[test]
    fn dropping_a_failed_evaluation_does_not_advance_the_branch_cursor() {
        let state = ExecutionIoState::new(Vec::from(&b"retry"[..]));
        let mut failed = state.begin_evaluation();
        assert_eq!(failed.read(3), b"ret");
        drop(failed);

        assert_eq!(state.cursor(), 0);
        let mut retry = state.begin_evaluation();
        assert_eq!(retry.read(3), b"ret");
        assert_eq!(retry.commit().cursor(), 3);
    }

    #[test]
    fn forks_after_a_read_have_independent_cursors() {
        let state = ExecutionIoState::new(Vec::from(&b"abcdef"[..]));
        let mut first = state.begin_evaluation();
        assert_eq!(first.read(1), b"a");
        let fork_point = first.commit();

        let mut left = fork_point.begin_evaluation();
        let mut right = fork_point.begin_evaluation();
        assert_eq!(left.read(2), b"bc");
        assert_eq!(right.read(4), b"bcde");

        let left = left.commit();
        let right = right.commit();
        assert_eq!(fork_point.cursor(), 1);
        assert_eq!(left.cursor(), 3);
        assert_eq!(right.cursor(), 5);
        assert_eq!(left.remaining_input(), b"def");
        assert_eq!(right.remaining_input(), b"f");
    }

    #[test]
    fn forks_retain_distinct_ordered_descriptor_transcripts() {
        let state = ExecutionIoState::default();
        let mut left = state.begin_evaluation();
        let mut right = state.begin_evaluation();

        left.append("IO.write", 1, Vec::from(&b"left-out"[..]));
        left.append("IO.putc", 2, Vec::from(&b"left-err"[..]));
        right.append("IO.write", 2, Vec::from(&b"right-err"[..]));
        right.append("IO.putc", 1, Vec::from(&b"right-out"[..]));

        let left = left.commit();
        let right = right.commit();
        assert!(state.transcript().is_empty());
        assert_eq!(
            left.transcript(),
            [
                DescriptorTranscriptEntry {
                    hook: "IO.write",
                    descriptor: 1,
                    bytes: Vec::from(&b"left-out"[..]).into(),
                },
                DescriptorTranscriptEntry {
                    hook: "IO.putc",
                    descriptor: 2,
                    bytes: Vec::from(&b"left-err"[..]).into(),
                },
            ]
        );
        assert_eq!(
            right.transcript(),
            [
                DescriptorTranscriptEntry {
                    hook: "IO.write",
                    descriptor: 2,
                    bytes: Vec::from(&b"right-err"[..]).into(),
                },
                DescriptorTranscriptEntry {
                    hook: "IO.putc",
                    descriptor: 1,
                    bytes: Vec::from(&b"right-out"[..]).into(),
                },
            ]
        );
    }

    #[test]
    fn console_observation_joins_writes_to_a_descriptor_and_drops_empty_ones() {
        let state = ExecutionIoState::new(Vec::from(&b"input"[..]));
        let mut evaluation = state.begin_evaluation();
        assert_eq!(evaluation.read(2), b"in");
        evaluation.append("IO.write", 1, Vec::from(&b"ab"[..]));
        evaluation.append("IO.putc", 1, Vec::from(&b"c"[..]));
        evaluation.append("IO.write", 2, Vec::new());
        evaluation.append("IO.putc", 1, Vec::from(&b"d"[..]));
        evaluation.append("IO.putc", 2, Vec::from(&b"e"[..]));
        evaluation.append("IO.write", 1, Vec::from(&b"f"[..]));
        evaluation.append("IO.write", 1, Vec::new());
        let state = evaluation.commit();

        let joined = |bytes: &[u8]| -> std::sync::Arc<[u8]> { bytes.into() };
        assert_eq!(
            state.observable(),
            ConsoleObservation {
                consumed: 2,
                writes: vec![(1, joined(b"abcd")), (2, joined(b"e")), (1, joined(b"f"))],
            }
        );
        assert_eq!(
            ExecutionIoState::default().observable(),
            ConsoleObservation::default()
        );
        let mut empty_only = ExecutionIoState::default().begin_evaluation();
        empty_only.append("IO.write", 2, Vec::new());
        assert_eq!(
            empty_only.commit().observable(),
            ConsoleObservation::default()
        );
    }

    fn console(
        input: &[u8],
        consumed: usize,
        writes: &[(&'static str, i32, &[u8])],
    ) -> ExecutionIoState {
        let mut evaluation = ExecutionIoState::new(input.to_vec()).begin_evaluation();
        evaluation.read(consumed);
        for (hook, descriptor, bytes) in writes {
            evaluation.append(hook, *descriptor, bytes.to_vec());
        }
        evaluation.commit()
    }

    fn entry(hook: &'static str, descriptor: i32, bytes: &[u8]) -> DescriptorTranscriptEntry {
        DescriptorTranscriptEntry {
            hook,
            descriptor,
            bytes: bytes.into(),
        }
    }

    // A fork shares its parent's console transcript and effect journal, stored once, and what one
    // branch appends afterwards is not the other's; each materialises exactly the entries a
    // vector of its own would hold, also when the parent's transcript was read before the fork.
    // This pins the representation's contract; it is not a regression test that fails at a base
    // where forks copied the vectors.
    #[test]
    fn a_fork_shares_its_console_and_journal_and_extends_them_apart() {
        let prefix = (0..200u8)
            .map(|byte| entry("IO.putc", 1, &[byte]))
            .collect::<Vec<_>>();
        let mut evaluation = ExecutionIoState::default().begin_evaluation();
        for written in &prefix {
            evaluation.append(written.hook, written.descriptor, written.bytes.clone());
        }
        let parent = evaluation.commit();
        assert_eq!(parent.transcript(), prefix);

        let fork = parent.clone();
        assert!(fork.transcript.shares_items_with(&parent.transcript));
        let mut left = fork.begin_evaluation();
        left.append("IO.write", 2, b"left".to_vec());
        let left = left.commit();
        let mut right = parent.begin_evaluation();
        right.append("IO.write", 1, b"right".to_vec());
        let right = right.commit();
        assert!(!left.transcript.shares_items_with(&right.transcript));
        assert_eq!(parent.transcript(), prefix);
        assert_eq!(
            left.transcript(),
            [prefix.as_slice(), &[entry("IO.write", 2, b"left")]].concat()
        );
        assert_eq!(
            right.transcript(),
            [prefix.as_slice(), &[entry("IO.write", 1, b"right")]].concat()
        );
        assert_ne!(left, right);
        assert_eq!(left, left.clone());

        let effect = |text: &str| BuiltinEffect::UserLog(text.to_owned());
        let mut journal = EffectJournal::default();
        journal.commit((0..200).map(|index| effect(&index.to_string())));
        let mut first = journal.clone();
        assert!(first.committed.shares_items_with(&journal.committed));
        let mut second = journal.clone();
        first.commit([effect("first")]);
        second.commit([effect("second")]);
        assert!(!first.committed.shares_items_with(&second.committed));
        let expected = (0..200)
            .map(|index| effect(&index.to_string()))
            .collect::<Vec<_>>();
        assert_eq!(journal.clone().into_committed(), expected);

        // A journal that ends moves out the effects it holds alone and clones those another
        // branch shares: a moved effect keeps its text's buffer, a cloned one gets a new one.
        let text_buffers = |effects: &mut dyn Iterator<Item = &BuiltinEffect>| {
            effects
                .map(|BuiltinEffect::UserLog(text)| text.as_ptr())
                .collect::<Vec<_>>()
        };
        let in_place = |journal: &EffectJournal| {
            let mut buffers = text_buffers(&mut journal.committed.iter_newest_first());
            buffers.reverse();
            buffers
        };
        let first_buffers = in_place(&first);
        let second_buffers = in_place(&second);
        let first = first.into_committed();
        assert_eq!(first, [expected.as_slice(), &[effect("first")]].concat());
        let first_out = text_buffers(&mut first.iter());
        assert_eq!(first_out.last(), first_buffers.last());
        assert!(
            first_out[..expected.len()]
                .iter()
                .zip(&first_buffers)
                .all(|(out, held)| out != held)
        );
        drop(journal);
        let second = second.into_committed();
        assert_eq!(second, [expected.as_slice(), &[effect("second")]].concat());
        assert_eq!(text_buffers(&mut second.iter()), second_buffers);
    }

    // The fingerprint is a filter for `observable()`: over consoles that write the same bytes by
    // different hooks or calls, add empty writes, interleave descriptors differently, consume
    // different input, or write bytes that spell a descriptor, two fingerprints agree exactly when
    // the observations do.
    #[test]
    fn console_fingerprints_agree_exactly_when_observations_do() {
        let consoles = [
            console(b"", 0, &[]),
            console(b"", 0, &[("IO.write", 2, b"")]),
            console(b"", 0, &[("IO.write", 1, b"ab")]),
            console(b"", 0, &[("IO.putc", 1, b"a"), ("IO.putc", 1, b"b")]),
            console(
                b"",
                0,
                &[
                    ("IO.putc", 1, b"a"),
                    ("IO.write", 2, b""),
                    ("IO.putc", 1, b"b"),
                ],
            ),
            console(b"", 0, &[("IO.write", 1, b"a"), ("IO.write", 2, b"b")]),
            console(b"", 0, &[("IO.write", 2, b"b"), ("IO.write", 1, b"a")]),
            console(b"", 0, &[("IO.write", 2, b"a"), ("IO.write", 2, b"b")]),
            console(b"", 0, &[("IO.write", 1, b"ba")]),
            console(b"", 0, &[("IO.write", 1, b"\x00\x00\x00\x01\x02")]),
            console(
                b"",
                0,
                &[
                    ("IO.write", 1, b"a"),
                    ("IO.write", 2, b"b"),
                    ("IO.write", 1, b"c"),
                ],
            ),
            console(b"", 0, &[("IO.write", 1, b"ac"), ("IO.write", 2, b"b")]),
            console(b"xy", 1, &[("IO.write", 1, b"ab")]),
            console(b"xy", 2, &[("IO.write", 1, b"ab")]),
        ];
        for left in &consoles {
            for right in &consoles {
                assert_eq!(
                    left.observable_fingerprint() == right.observable_fingerprint(),
                    left.observable() == right.observable(),
                    "{:?} and {:?}",
                    left.observable(),
                    right.observable()
                );
            }
        }
    }

    // The same for effect journals: two fingerprints agree exactly when the journals do, also
    // when the concatenation of their texts is the same.
    #[test]
    fn journal_fingerprints_agree_exactly_when_journals_do() {
        let journal = |texts: &[&str]| {
            let mut journal = EffectJournal::default();
            journal.commit(
                texts
                    .iter()
                    .map(|text| BuiltinEffect::UserLog((*text).to_owned())),
            );
            journal
        };
        let journals = [
            journal(&[]),
            journal(&[""]),
            journal(&["", ""]),
            journal(&["ab"]),
            journal(&["a", "b"]),
            journal(&["b", "a"]),
            journal(&["ab", ""]),
            journal(&["a", "b", "c"]),
        ];
        for left in &journals {
            for right in &journals {
                assert_eq!(left.fingerprint() == right.fingerprint(), left == right);
                assert_eq!(
                    left == right,
                    left.clone().into_committed() == right.clone().into_committed()
                );
            }
        }
    }
}
