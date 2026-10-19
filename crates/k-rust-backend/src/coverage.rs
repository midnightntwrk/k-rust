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
//! candidates for a subject stops before trying some of them (a rewrite step, a function or
//! simplification equation scan, a definedness decision of an unevaluated operand) or tries one
//! without deciding its condition: each candidate left untried is matched against the subject by
//! a probe ([`offer`]) that runs isolated from the run, so that asking for the level changes
//! nothing else ([`RunCoverage::offered`] states what it holds).
//!
//! Collection is crate-private: only the execute entry point opens one around a run, and the
//! definition load around a rule's discharge. A caller that could open one around its own calls
//! would also collect what selecting or loading a module applies, which depends on the requests
//! made before (`session::BackendSession::definition` builds a module on its first use).

use std::{
    cell::{Cell, RefCell},
    collections::BTreeSet,
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
/// `matched`, plus the id of an axiom whose left-hand side matched the subject of a site where
/// the backend selected candidates for it and never began to decide the axiom's condition there:
/// - a rewrite step (`rewrite::step`): a rule of a priority group below the step's first
///   productive or undecided group, of that undecided group after the rule whose attempt left
///   the step undecided, and, under `ExecutionMode::Any`, after the rule that took the state;
///   matched against the step's subject with `matching::match_rule_in_definition`;
/// - a function or simplification equation scan (`simplify::scan::scan_term_theory`): an
///   equation after the one that applied, in its group or a later one, and one of a group after
///   a function group that blocked the scan; matched by `simplify::equation_instances`;
/// - an equation the scan tried whose instances exist but whose condition it did not decide
///   (`simplify::apply_equation`): a set-aside or unused instance, or an undecided matching;
/// - a definedness decision of an operand a conditional does not evaluate (`deferred`): the
///   function equations after the group the one-step selection returned at, with the other
///   matching equations of that group when it gave up on several, and the unconditional ceil
///   equations after the one that decided.
///
/// A match left undecided counts. Each probe is one match attempt, isolated from the run
/// ([`offer`]), and an axiom already in a set is not probed again.
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
