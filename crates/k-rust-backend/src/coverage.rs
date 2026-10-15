//! Run coverage: the rules and equations an execution used, as two sets of axiom identities
//! collected on the thread that runs it.
//!
//! An execution that asks for it (`rewrite::ExecutionOptions::collect_coverage`) opens a
//! collection in its entry point, after the definition has been selected, and closes it after
//! final leaf selection; the result carries the sets as `rewrite::ExecutionResult::coverage`
//! ([`RunCoverage`] states what they hold). The backend reports to the collection where it
//! applies an axiom or begins deciding a matched instance's condition, not where a caller keeps
//! a result, so every caller is covered alike: state, constraint and remainder simplification, a
//! rule's `requires`, `ensures`, definedness and narrowing phases and its right-hand side,
//! another equation's condition at any depth, the definedness analysis (`definedness::ceil_term`),
//! and attempts that are later rewound or discarded.
//!
//! A rewrite rule's definedness may be discharged when the definition is loaded, before any run
//! (`BackendDefinition::discharge_rewrite_definedness`): the ceil equations the discharge used
//! are collected there and kept on the rule (`ComputedRuleAttributes::discharged_by`), and a run
//! that begins deciding the rule's `requires` reports them as applied, since the discharge
//! removed the obligations that run would otherwise decide. Equations only the load-time
//! confluence check uses are uses by the definition, not by a run, and appear in no run's sets.
//!
//! The collection is per thread. Everything an execution evaluates runs on its own thread before
//! its entry point returns (`crate::evaluation`), so the collection sees every application of the
//! run and nothing of another thread. With no collection open, a report reads one thread-local
//! flag and returns.
//!
//! Collection is crate-private: only the execute entry point opens one around a run, and the
//! definition load around a rule's discharge. A caller that could open one around its own calls
//! would also collect what selecting or loading a module applies, which depends on the requests
//! made before (`session::BackendSession::definition` builds a module on its first use).

use std::{
    cell::{Cell, RefCell},
    collections::BTreeSet,
};

use rustc_hash::FxHashSet;

/// The axioms a run used, by `UNIQUE_ID`.
///
/// `applied` holds the id of every axiom an instance of which the backend used while the
/// collection was open:
/// - an equation of any theory (function, simplification, `anywhere`, overload, ceil or
///   predicate) whose result replaced its subject, or made the subject bottom, wherever it was
///   applied, the definedness analysis included;
/// - a rewrite rule that produced a successor or an undefined-step entry;
/// - every id in `ComputedRuleAttributes::discharged_by` of a rewrite rule whose `requires`
///   phase was entered.
///
/// `matched` holds `applied`, plus every axiom at whose condition-evaluation site the backend
/// arrived for an instance whose left-hand side matched:
/// - for a rewrite rule, the entry of its `requires` phase, reached when the left-hand side
///   matched, or unified with a narrowing condition the solver did not refute;
/// - for an equation, the entry of its condition's evaluation, which also covers a conditional
///   instance evaluated together with its subject equalities, and an instance that a `concrete`
///   or `symbolic` attribute set aside when its `requires` is non-empty and the scan decides it
///   (`simplify::scan::SetAsideRequires::Decide`). A set-aside instance with an empty `requires`
///   and no subject equalities is not used and not decided, and is not counted.
///
/// `matched` is noted on entry, before any verdict: an instance whose condition was refuted, left
/// undecided, or cut short by a stop is in it.
///
/// Both sets ignore whether the caller kept the result: an application in an attempt that was
/// later rewound or discarded counts. A compiler-generated axiom without an id is recorded as
/// `UNKNOWN`. Builtin hooks are not axioms and are never recorded.
///
/// The sets are a deterministic function of the definition, the request, the solver profile and
/// the k-rust version. They depend on the backend's trial order and stopping rules (an equation
/// group is scanned until one equation applies, a rewrite step stops at the first productive
/// priority group), but not on the order or multiplicity of applications, and they do not grow
/// with the number of leaves.
///
/// The type is `non_exhaustive` so that further sets of the run can be added beside these two.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
pub struct RunCoverage {
    pub applied: BTreeSet<String>,
    pub matched: BTreeSet<String>,
}

/// The ids reported to the open collection, inserted once each.
#[derive(Default)]
struct Sink {
    applied: FxHashSet<String>,
    matched: FxHashSet<String>,
}

impl Sink {
    fn absorb(&mut self, inner: &Sink) {
        self.applied.extend(inner.applied.iter().cloned());
        self.matched.extend(inner.matched.iter().cloned());
    }

    fn into_coverage(self) -> RunCoverage {
        let mut matched = self.matched;
        matched.extend(self.applied.iter().cloned());
        RunCoverage {
            applied: self.applied.into_iter().collect(),
            matched: matched.into_iter().collect(),
        }
    }
}

thread_local! {
    /// Whether reports are collected now: a collection is open and no [`suspend`] is in effect.
    static OPEN: Cell<bool> = const { Cell::new(false) };
    /// What the innermost open collection has received.
    static SINK: RefCell<Sink> = RefCell::new(Sink::default());
}

/// Run `action` with a collection open and return what it reported.
///
/// A collection opened inside another one also feeds the outer one when it closes. The flag and
/// the outer collection's contents are restored when `action` unwinds, and then nothing it
/// reported reaches the outer collection.
pub(crate) fn collect<T>(action: impl FnOnce() -> T) -> (T, RunCoverage) {
    /// Restores the flag and the outer sink on every exit, and hands the inner sink back.
    struct Restore {
        was_open: bool,
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
            if let Some(outer) = self.outer.take() {
                // Unwinding: the inner reports are dropped with the action.
                SINK.set(outer);
            }
        }
    }

    let restore = Restore {
        was_open: OPEN.replace(true),
        outer: Some(SINK.take()),
    };
    let result = action();
    let inner = restore.close();
    (result, inner.into_coverage())
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
