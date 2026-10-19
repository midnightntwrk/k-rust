//! Run coverage: the rules and equations an execution used, as sets of axiom identities
//! collected on the thread that runs it.
//!
//! An execution that asks for it (`rewrite::ExecutionOptions::collect_coverage`) opens a
//! collection in its entry point, after the definition has been selected, and closes it after
//! final leaf selection; the result carries the sets as `rewrite::ExecutionResult::coverage`
//! ([`RunCoverage`] states what they hold). The backend reports to the collection where it
//! applies an axiom or begins deciding a matched instance's condition, not where a caller keeps
//! a result, so every caller is covered alike: state, constraint and remainder simplification, a
//! rule's `requires`, `ensures`, definedness and narrowing phases and its right-hand side,
//! another equation's condition at any depth, the definedness analysis (`definedness::ceil_term`)
//! and its decisions about operands a conditional does not evaluate (`deferred::decide_defined`),
//! and attempts that are later rewound or discarded.
//!
//! A rewrite rule's definedness may be discharged when the definition is loaded, before any run
//! (`BackendDefinition::discharge_rewrite_definedness`): the discharge's own coverage is
//! collected there and kept on the rule (`ComputedRuleAttributes::discharged_by`), and a run that
//! begins deciding the rule's `requires` reports its sets as its own, since the discharge removed
//! the obligations that run would otherwise decide. Equations only the load-time
//! confluence check uses are uses by the definition, not by a run, and appear in no run's sets.
//!
//! The collection is per thread. Everything an execution evaluates runs on its own thread before
//! its entry point returns (`crate::evaluation`), so the collection sees every application of the
//! run and nothing of another thread. With no collection open, a report reads one thread-local
//! flag and returns.
//!
//! An execution that also asks for the offered level (`rewrite::ExecutionOptions::collect_offered`)
//! opens an offering collection. The backend reports to it, besides, where a site that selected
//! candidates for a subject by priority group (a rewrite step, an equation scan of a term or a
//! predicate, a definedness decision) stops before trying some of them, and where it tries one
//! whose left-hand side matched: each candidate left untried is matched against the subject by
//! a probe ([`offer`]) that runs isolated from the run, so that asking for the level changes
//! nothing else ([`RunCoverage::offered`] states what it holds). Such a site takes its
//! candidates from a [`Selection`], which offers what the site never took on every exit.
//!
//! Collection is crate-private: only the execute entry point opens one around a run, and the
//! definition load around a rule's discharge. A caller that could open one around its own calls
//! would also collect what selecting or loading a module applies, which depends on the requests
//! made before (`session::BackendSession::definition` builds a module on its first use).

use std::{
    cell::{Cell, RefCell},
    collections::BTreeSet,
    sync::Arc,
};

use k_rust_kore::measure::{self, Counter};
use rustc_hash::FxHashSet;

/// The axioms a run used, by `UNIQUE_ID`.
///
/// Each set is defined by the places the backend reports to it (the recording sites, listed
/// here by what they record); nothing else adds to them.
///
/// `applied` holds the id of an axiom when, while the collection was open:
/// - a function, simplification, `anywhere` or overload equation's instance gave a result: the
///   instantiated right-hand side, or the subject stated empty by a refuted binding obligation,
///   `ensures` or a `#Bottom` right-hand side (`Simplification::equation`,
///   `Simplification::bottom_subject`), even where the scan then reads a result equal to the
///   application as no value; or a `#Top` lemma dropped an operand of a term-level `#And`;
/// - a ceil or predicate equation's instance gave its instantiated right-hand side or refuted
///   its subject (`apply_ceil_equation_instance`, `apply_predicate_equation`);
/// - the definedness analysis took an unconditional ceil equation's instance as the condition of
///   a partial application (`definedness::ceil_theory_condition`);
/// - a decision about the definedness of an operand that a conditional does not evaluate came
///   from one equation (`deferred::decide_defined`): the value of one function-equation step
///   (D1), an unconditional ceil equation that refuted, established or restated the atom (D2,
///   D2'), or one function-equation step that refuted or established it (D4);
/// - a rewrite step built a successor of a rule (`AppliedRule`) or an undefined-step entry of it
///   (`TrivialApplication`), whether or not the step kept it;
/// - a rewrite rule's `requires` phase was entered: the `applied` ids of its
///   `ComputedRuleAttributes::discharged_by`.
///
/// `matched` holds `applied`, plus the id of an axiom when the backend began deciding a
/// condition of an instance whose left-hand side matched:
/// - a rewrite rule's `requires` phase was entered, which happens when its left-hand side
///   matched, or unified under a narrowing condition the solver did not refute; the
///   `matched` ids of its `discharged_by` are added then too;
/// - an equation's condition evaluation was entered (`simplify::evaluate_equation_condition`):
///   for a usable instance of a term, ceil, predicate or `#Top` equation; and, in a function
///   scan where a lower group follows (`simplify::scan::SetAsideRequires::Decide`), for an
///   instance that matches only under equalities of the subject's variables, with those
///   equalities, and for one a `concrete` or `symbolic` attribute set aside whose `requires`
///   is not empty. A set-aside instance with an empty `requires` and no such equalities is not
///   decided and not counted;
/// - a definedness decision considered an equation instance (`deferred::decide_defined`): the
///   function equation selected for one step, whose condition is then checked, and every usable
///   instance of an unconditional ceil equation, whose condition is then folded.
///
/// `matched` is noted on entry, before any verdict: an instance whose condition was refuted, left
/// undecided, or cut short by a stop is in it, and so is one whose attempt then failed without a
/// result (a disjunctive right-hand side, or an error after the condition held).
///
/// Neither set depends on whether the caller kept what was recorded: an application in an
/// attempt that was later rewound or discarded counts. A compiler-generated axiom without an id
/// is recorded as `UNKNOWN`. Builtin hooks are not axioms and are never recorded. Claims, macro
/// and alias rules, and `smt-lemma` axioms have no recording site, and neither has matching
/// modulo overloads, which consults the `symbol-overload` relation the compiler generates from
/// production attributes (`matching`), not an author's sentence; an overload equation applied as
/// an equation is recorded as any other.
///
/// The sets are a deterministic function of the definition, the request, the solver profile and
/// the k-rust version. They depend on the backend's trial order and stopping rules (an equation
/// group is scanned until one equation applies, a rewrite step stops at the first productive
/// priority group), but not on the order or multiplicity of applications, and they do not grow
/// with the number of leaves.
///
/// `offered`, present exactly when the collection offered (`collect_offering`), holds
/// `matched`, plus the id of an axiom whose left-hand side matched a subject at a site where the
/// backend selected the axiom as a candidate for it, whether or not the site went on to decide
/// the axiom's condition there. Two kinds of report add to it:
/// - a candidate never tried: every site that selects candidates by priority group and stops
///   before trying them all takes them from a [`Selection`], which offers each candidate the
///   site never took, matched against the site's subject by a probe ([`offer`]). The sites are
///   the rewrite steps (`rewrite::step`: the rules of the groups below the step's first
///   productive or undecided group and of that undecided group after the rule that left it
///   undecided, the rules after the one that took the state under `ExecutionMode::Any`, and, in
///   the fold of the lower groups through the remainder, the rules of a group after the one
///   that left the remainder undecided and of the groups after it, against the remainder),
///   the function and simplification term scans (`simplify::scan::scan_term_theory`), the ceil
///   and predicate scans of the predicate simplifier (`simplify::apply_ceil_theory`,
///   `simplify::apply_predicate_theory`), the `#Top` lemmas of an operand of a term-level
///   conjunction (`simplify::matches_top_equation`), the ceil equations of the definedness
///   analysis (`definedness::ceil_theory_condition`), and the definedness decisions of an
///   operand a conditional does not evaluate (`deferred`: the one-step function selection and
///   the unconditional ceil equations);
/// - a candidate tried: every attempt at those sites whose match of the left-hand side
///   succeeded or was left undecided notes the axiom, however the attempt then ends: refuted
///   before its condition (a rewrite rule's narrowing, an undefined binding), set aside by
///   `concrete` or `symbolic`, read as unused, undecided, or decided.
///
/// A match left undecided counts, and an undecided match blocks the lower groups of its site: an
/// axiom in no set cannot change the run when it is raised, loses its `owise`, `concrete` or
/// `symbolic`, or is lowered (a lower priority, an added `owise`, `concrete` or `symbolic`),
/// whereas lowering an axiom in `offered` alone can. Each probe is one match attempt, isolated
/// from the run ([`offer`]). An axiom already in a set is not probed again, but one whose probe
/// failed is probed again at the next site that skips it: the probes cost at most one match per
/// candidate a site skipped, at every visit of the site while the candidate has not matched, so
/// over a run they grow with the visits times the skipped candidates. A tried candidate costs no
/// probe, except that a rewrite step under `ExecutionMode::All` skips the rules of the groups
/// below its first productive group, probed against its subject, before the fold tries them on
/// the remainder.
///
/// The type is `non_exhaustive` so that further sets of the run can be added beside these.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
pub struct RunCoverage {
    pub applied: BTreeSet<String>,
    pub matched: BTreeSet<String>,
    pub offered: Option<BTreeSet<String>>,
}

/// The ids reported to the open collection, inserted once each.
#[derive(Default)]
struct Sink {
    applied: FxHashSet<String>,
    matched: FxHashSet<String>,
    offered: FxHashSet<String>,
}

impl Sink {
    fn absorb(&mut self, inner: &Sink) {
        self.applied.extend(inner.applied.iter().cloned());
        self.matched.extend(inner.matched.iter().cloned());
        self.offered.extend(inner.offered.iter().cloned());
    }

    fn holds(&self, id: &str) -> bool {
        self.offered.contains(id) || self.matched.contains(id) || self.applied.contains(id)
    }

    fn into_coverage(self, offering: bool) -> RunCoverage {
        let mut matched = self.matched;
        matched.extend(self.applied.iter().cloned());
        let offered = offering.then(|| {
            let mut offered = self.offered;
            offered.extend(matched.iter().cloned());
            offered.into_iter().collect()
        });
        RunCoverage {
            applied: self.applied.into_iter().collect(),
            matched: matched.into_iter().collect(),
            offered,
        }
    }
}

thread_local! {
    /// Whether reports are collected now: a collection is open and no [`suspend`] is in effect.
    static OPEN: Cell<bool> = const { Cell::new(false) };
    /// Whether the innermost open collection offers.
    static OFFERING: Cell<bool> = const { Cell::new(false) };
    /// What the innermost open collection has received.
    static SINK: RefCell<Sink> = RefCell::new(Sink::default());
}

/// Run `action` with a collection open and return what it reported.
///
/// A collection opened inside another one also feeds the outer one when it closes. The flag and
/// the outer collection's contents are restored when `action` unwinds, and then nothing it
/// reported reaches the outer collection.
pub(crate) fn collect<T>(action: impl FnOnce() -> T) -> (T, RunCoverage) {
    collect_offering(false, action)
}

/// [`collect`], with the offered level collected when `offering` holds
/// ([`RunCoverage::offered`]). A collection opened inside does not offer unless it asks, and its
/// offered ids feed this one when it closes.
pub(crate) fn collect_offering<T>(offering: bool, action: impl FnOnce() -> T) -> (T, RunCoverage) {
    /// Restores the flags and the outer sink on every exit, and hands the inner sink back.
    struct Restore {
        was_open: bool,
        was_offering: bool,
        outer: Option<Sink>,
    }
    impl Restore {
        fn close(mut self) -> Sink {
            let outer = self.outer.take().unwrap_or_default();
            let inner = SINK.replace(outer);
            if self.was_open {
                SINK.with_borrow_mut(|sink| sink.absorb(&inner));
            }
            inner
        }
    }
    impl Drop for Restore {
        fn drop(&mut self) {
            OPEN.set(self.was_open);
            OFFERING.set(self.was_offering);
            if let Some(outer) = self.outer.take() {
                // Unwinding: the inner reports are dropped with the action.
                SINK.set(outer);
            }
        }
    }

    let restore = Restore {
        was_open: OPEN.replace(true),
        was_offering: OFFERING.replace(offering),
        outer: Some(SINK.take()),
    };
    let result = action();
    let inner = restore.close();
    (result, inner.into_coverage(offering))
}

/// Report every set of `coverage`, a coverage collected earlier and stored (such as a rule's
/// load-time discharge, `ComputedRuleAttributes::discharged_by`), to the open collection, each
/// id to the set it was collected in.
pub(crate) fn replay(coverage: &RunCoverage) {
    let RunCoverage {
        applied,
        matched,
        offered,
    } = coverage;
    for id in applied {
        note_applied(id);
    }
    for id in matched {
        note_matched(id);
    }
    for id in offered.iter().flatten() {
        note_offered(id);
    }
}

/// Run `action` with no report collected: caller code that runs inside an execution, such as
/// the legacy effect observer, is not part of the run. The flag is restored afterwards, also
/// when `action` unwinds.
pub(crate) fn suspend<T>(action: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            OPEN.set(self.0);
        }
    }
    let _restore = Restore(OPEN.replace(false));
    action()
}

/// Report that an instance of the axiom `id` was used ([`RunCoverage::applied`]).
#[inline]
pub(crate) fn note_applied(id: &str) {
    if OPEN.get() {
        SINK.with_borrow_mut(|sink| insert(&mut sink.applied, id));
    }
}

/// Report that the backend began deciding the condition of a matched instance of the axiom `id`
/// ([`RunCoverage::matched`]).
#[inline]
pub(crate) fn note_matched(id: &str) {
    if OPEN.get() {
        SINK.with_borrow_mut(|sink| insert(&mut sink.matched, id));
    }
}

fn insert(set: &mut FxHashSet<String>, id: &str) {
    if !set.contains(id) {
        set.insert(id.to_owned());
    }
}

/// Whether an offering collection is open and no [`suspend`] is in effect: the sites that offer
/// do their probes' work only then.
#[inline]
pub(crate) fn offering() -> bool {
    OPEN.get() && OFFERING.get()
}

/// Report that the left-hand side of the axiom `id` matched the subject of a selection site
/// that did not decide its condition ([`RunCoverage::offered`]); nothing unless [`offering`].
#[inline]
pub(crate) fn note_offered(id: &str) {
    if offering() {
        SINK.with_borrow_mut(|sink| insert(&mut sink.offered, id));
    }
}

/// An axiom a selection site selects as a candidate for a subject, by its coverage id.
pub(crate) trait Candidate {
    /// The id the coverage sets hold for the axiom (`UNIQUE_ID`).
    fn coverage_id(&self) -> &str;
}

impl Candidate for crate::rule::RewriteRule {
    fn coverage_id(&self) -> &str {
        &self.attributes.unique_id
    }
}

impl Candidate for crate::rule::PredicateRewriteRule {
    fn coverage_id(&self) -> &str {
        &self.attributes.unique_id
    }
}

/// The candidates one selection site selected for one subject, by priority group in trial
/// order, which the site takes from here as it tries them. However the site ends (it returns at
/// a group that applied or blocked, it gives up, or an error or stop propagates), every candidate
/// it never took is offered ([`offer`]), matched against the subject by `probe`. Every site that
/// selects by priority group and can stop before trying every candidate takes its candidates
/// from a `Selection`, so that no exit of it leaves a candidate unoffered.
///
/// `groups` are the selected groups, each with its priority, in the order the site tries them.
/// `candidate` says which axioms of a group are this site's candidates (a site may use only some
/// of the axioms selection offers, such as the unconditional ceil equations): only those are
/// taken and only those are offered.
///
/// The site takes the groups in order ([`Self::groups`]) and each group's candidates in order,
/// and takes a later group only once the earlier one is exhausted; it may stop anywhere. A
/// candidate is taken when its group yields it. A site that then ends without trying it gives it
/// back ([`Self::give_back`]).
///
/// Unless the run collects the offered level nothing is probed: taking a candidate writes its
/// position, and the end of the selection reads the thread's flag.
pub(crate) struct Selection<'a, R, G, P>
where
    R: Candidate + 'a,
    G: Iterator<Item = (u8, &'a [Arc<R>])> + Clone,
    P: FnMut(&R) -> bool,
{
    groups: G,
    candidate: fn(&R) -> bool,
    /// The position of a group and the index in it of the first candidate not taken: every
    /// candidate before it was taken.
    taken: Cell<(usize, usize)>,
    probe: P,
}

impl<'a, R, G, P> Selection<'a, R, G, P>
where
    R: Candidate + 'a,
    G: Iterator<Item = (u8, &'a [Arc<R>])> + Clone,
    P: FnMut(&R) -> bool,
{
    pub(crate) fn new(groups: G, candidate: fn(&R) -> bool, probe: P) -> Self {
        Self {
            groups,
            candidate,
            taken: Cell::new((0, 0)),
            probe,
        }
    }

    /// The groups in order, each with its priority and its candidates, which it yields in order.
    pub(crate) fn groups(&self) -> impl Iterator<Item = (u8, Group<'_, 'a, R>)> + '_ {
        self.groups
            .clone()
            .enumerate()
            .map(move |(position, (priority, rules))| {
                debug_assert_eq!(
                    self.taken.get(),
                    (position, 0),
                    "a selection site takes a group only after exhausting the one before"
                );
                (
                    priority,
                    Group {
                        taken: &self.taken,
                        candidate: self.candidate,
                        position,
                        rules: rules.iter().enumerate(),
                    },
                )
            })
    }

    /// The candidate taken last was not tried: it is offered with the candidates not taken.
    pub(crate) fn give_back(&self) {
        let (position, index) = self.taken.get();
        debug_assert!(index > 0, "a candidate of this group was taken");
        self.taken.set((position, index.saturating_sub(1)));
    }
}

impl<'a, R, G, P> Drop for Selection<'a, R, G, P>
where
    R: Candidate + 'a,
    G: Iterator<Item = (u8, &'a [Arc<R>])> + Clone,
    P: FnMut(&R) -> bool,
{
    fn drop(&mut self) {
        if !offering() || std::thread::panicking() {
            return;
        }
        let (taken_group, taken_index) = self.taken.get();
        for (position, (_, rules)) in self.groups.clone().enumerate().skip(taken_group) {
            let start = if position == taken_group {
                taken_index
            } else {
                0
            };
            for rule in rules.iter().skip(start) {
                if (self.candidate)(rule) {
                    let probe = &mut self.probe;
                    offer(rule.coverage_id(), || probe(rule));
                }
            }
        }
    }
}

/// The candidates of one group of a [`Selection`], in trial order; each one it yields is taken.
pub(crate) struct Group<'s, 'a, R> {
    taken: &'s Cell<(usize, usize)>,
    candidate: fn(&R) -> bool,
    position: usize,
    rules: std::iter::Enumerate<std::slice::Iter<'a, Arc<R>>>,
}

impl<R> Group<'_, '_, R> {
    /// Whether no candidate of the group is left to take.
    pub(crate) fn is_exhausted(&self) -> bool {
        !self.rules.clone().any(|(_, rule)| (self.candidate)(rule))
    }
}

impl<'a, R> Iterator for Group<'_, 'a, R> {
    type Item = &'a Arc<R>;

    fn next(&mut self) -> Option<Self::Item> {
        for (index, rule) in self.rules.by_ref() {
            if (self.candidate)(rule) {
                self.taken.set((self.position, index + 1));
                return Some(rule);
            }
        }
        self.taken.set((self.position + 1, 0));
        None
    }
}

/// The groups of a selection stored by priority, as a [`Selection`] takes them.
pub(crate) fn by_priority<R>(
    groups: &std::collections::BTreeMap<u8, Vec<Arc<R>>>,
) -> impl Iterator<Item = (u8, &[Arc<R>])> + Clone {
    groups
        .iter()
        .map(|(priority, rules)| (*priority, rules.as_slice()))
}

/// Every axiom of the groups is a candidate of the site.
pub(crate) fn every<R>(_: &R) -> bool {
    true
}

/// Offer every candidate of `groups`, which a site never tries: a [`Selection`] from which
/// nothing is taken.
pub(crate) fn offer_all<'a, R, G, P>(groups: G, candidate: fn(&R) -> bool, probe: P)
where
    R: Candidate + 'a,
    G: Iterator<Item = (u8, &'a [Arc<R>])> + Clone,
    P: FnMut(&R) -> bool,
{
    drop(Selection::new(groups, candidate, probe));
}

/// Offer the axiom `id` when `probe`, a match of its left-hand side against a site's subject,
/// says it matched: `probe` runs only while [`offering`] and only for an axiom no set holds yet,
/// once per call, isolated from the run, and counts one `Counter::CoverageOfferMatches`.
///
/// Isolated: whatever `probe` does reports to no coverage set, counts no other work, emits no
/// diagnostic into any collection and leaves the thread's emission positions as they were,
/// notes no path fact, and leaves the counter of renamed-apart names as it was, so that the
/// names it minted are minted again by the run's next renaming exactly as without the probe.
/// Its own renamed terms do not outlive it, so no name is shared. It takes nothing from the
/// run's `FreshCounter`, which it is not given.
pub(crate) fn offer(id: &str, probe: impl FnOnce() -> bool) {
    if !offering() || SINK.with_borrow(|sink| sink.holds(id)) {
        return;
    }
    let matched = suspend(|| {
        measure::without_counting(|| {
            crate::diagnostic::discarded(|| {
                crate::path_facts::discarded(|| crate::rule::with_apart_names_restored(probe))
            })
        })
    });
    measure::bump(Counter::CoverageOfferMatches);
    if matched {
        note_offered(id);
    }
}
