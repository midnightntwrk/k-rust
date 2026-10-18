//! Path facts: facts about the model-dependence of a run that its leaves must carry whatever
//! became of the work that found them, collected on the thread that runs it.
//!
//! The one kind of fact is an evaluation that read a value the definition leaves open
//! ([`PathFact::ChosenValue`], `builtin::chosen_value`): a leaf whose path read one is one model's
//! answer. Such a fact is a fact about the decisions a path rests on, not about the result the
//! work contributed to, so it is never withdrawn with that work. The diagnostic channel
//! (`crate::diagnostic`) drops the reports of work on no path (an attempt that did not apply, an
//! undone `Unspecified` attempt, a speculative attempt, a superseded or retracted one); this
//! collector has no drop, rewind, discard or retraction at all. Every rule below is stated per
//! fact, so a further kind of fact is a further variant and needs no new rule.
//!
//! - A phase of a run collects what it noted ([`collect`]); closing a collection adds what it
//!   holds to the enclosing collection. A fact noted inside a candidate-owned scope ([`owned`])
//!   is kept apart from the enclosing phase's own facts (`Facts::owned`), so that the phase can
//!   attribute it to the candidate alone.
//! - A structure that lets a later step skip an evaluation stores the facts its evaluation noted
//!   ([`marker`], [`since`]) and notes them again where it is served ([`replay`]).
//! - An evaluation whose value only decides a definedness that is the same in every model runs
//!   with notes suspended ([`suspend`]): its facts reach no collection and no run record, and a
//!   memo filled there still learns them, so it replays them where they count.
//! - The run-level record ([`run`]) holds every distinct fact the run noted outside a
//!   suspension, in first-observed order, whatever became of the work and the paths that met it.
//!
//! With nothing open a note reads one thread-local flag and returns.

use std::{
    cell::{Cell, RefCell},
    collections::BTreeSet,
    sync::Arc,
};

use crate::{
    builtin::ChosenValue,
    diagnostic::{self, BackendDiagnostic},
};

/// A fact a path's leaves carry whatever became of the work that found it.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum PathFact {
    /// An evaluation took one of several values the definition admits (`builtin::chosen_value`).
    ChosenValue(ChosenValue),
}

impl PathFact {
    /// The fact as a diagnostic of the paths it is attributed to.
    pub(crate) fn diagnostic(&self) -> BackendDiagnostic {
        match self {
            Self::ChosenValue(chosen) => BackendDiagnostic::ImplementationChosenValue {
                hook: chosen.hook.to_string(),
                class: chosen.class,
            },
        }
    }

    /// The fact a diagnostic of [`Self::diagnostic`] states, `None` for any other diagnostic.
    pub(crate) fn of_diagnostic(diagnostic: &BackendDiagnostic) -> Option<Self> {
        match diagnostic {
            BackendDiagnostic::ImplementationChosenValue { hook, class } => Some(
                Self::ChosenValue(ChosenValue::new(Arc::from(hook.as_str()), *class)),
            ),
            _ => None,
        }
    }

    /// The chosen value, when the fact is one.
    pub(crate) fn chosen_value(&self) -> Option<&ChosenValue> {
        match self {
            Self::ChosenValue(chosen) => Some(chosen),
        }
    }
}

/// A set of facts, in their order (hook, then class).
pub(crate) type FactSet = BTreeSet<PathFact>;

/// What a [`collect`] scope noted: `shared`, outside every candidate-owned scope inside it, and
/// `owned`, inside one.
#[derive(Debug, Default)]
pub(crate) struct Facts {
    pub(crate) shared: FactSet,
    pub(crate) owned: FactSet,
}

impl Facts {
    /// Every fact, shared or owned.
    pub(crate) fn all(&self) -> FactSet {
        self.shared.union(&self.owned).cloned().collect()
    }
}

/// The facts as diagnostics, in their order.
pub(crate) fn diagnostics<'a>(
    facts: impl IntoIterator<Item = &'a PathFact>,
) -> Vec<BackendDiagnostic> {
    facts.into_iter().map(PathFact::diagnostic).collect()
}

/// The facts among `diagnostics`.
pub(crate) fn of_diagnostics<'a>(
    diagnostics: impl IntoIterator<Item = &'a BackendDiagnostic>,
) -> FactSet {
    diagnostics
        .into_iter()
        .filter_map(PathFact::of_diagnostic)
        .collect()
}

struct Sink {
    facts: Facts,
    /// A candidate-owned scope ([`owned`]): its facts go to the enclosing `owned`.
    owned: bool,
}

#[derive(Default)]
struct State {
    sinks: Vec<Sink>,
    suspended: bool,
    run: Option<Vec<PathFact>>,
    /// The number of notes made while something was open.
    sequence: u64,
    /// Each distinct fact noted, with the sequence number of its latest note.
    stamps: Vec<(PathFact, u64)>,
}

impl State {
    fn is_open(&self) -> bool {
        !self.sinks.is_empty() || self.run.is_some()
    }

    /// Note `fact`; returns it when it is a fact of an open run noted outside every phase of the
    /// run, which only the run record receives, so that the caller can report the stray note once
    /// the state is no longer borrowed.
    fn note(&mut self, fact: PathFact) -> Option<PathFact> {
        self.sequence += 1;
        let sequence = self.sequence;
        match self.stamps.iter_mut().find(|(stamped, _)| *stamped == fact) {
            Some((_, stamp)) => *stamp = sequence,
            None => self.stamps.push((fact.clone(), sequence)),
        }
        if self.suspended {
            return None;
        }
        let stray = (self.run.is_some() && self.sinks.is_empty()).then(|| fact.clone());
        if let Some(run) = &mut self.run
            && !run.contains(&fact)
        {
            run.push(fact.clone());
        }
        if let Some(sink) = self.sinks.last_mut() {
            sink.facts.shared.insert(fact);
        }
        stray
    }

    fn close(&mut self) -> Sink {
        let sink = self.sinks.pop().expect("a collection is closed once");
        if let Some(enclosing) = self.sinks.last_mut() {
            if sink.owned {
                enclosing.facts.owned.extend(sink.facts.all());
            } else {
                enclosing
                    .facts
                    .shared
                    .extend(sink.facts.shared.iter().cloned());
                enclosing
                    .facts
                    .owned
                    .extend(sink.facts.owned.iter().cloned());
            }
        }
        if !self.is_open() {
            self.stamps.clear();
        }
        sink
    }
}

thread_local! {
    /// Whether a collection or a run record is open, so that a note has somewhere to go.
    static OPEN: Cell<bool> = const { Cell::new(false) };
    static STATE: RefCell<State> = RefCell::new(State::default());
}

fn with_state<T>(action: impl FnOnce(&mut State) -> T) -> T {
    STATE.with_borrow_mut(|state| {
        let result = action(state);
        OPEN.set(state.is_open());
        result
    })
}

/// Note `fact`: it reaches the innermost open collection and the run record, unless notes are
/// suspended.
pub(crate) fn note(fact: PathFact) {
    if !OPEN.get() {
        return;
    }
    let stray = with_state(|state| state.note(fact));
    report_stray(stray);
}

/// Every evaluation of a run is inside one of its phases, which attribute what it notes to
/// paths; a note outside all of them would reach the run's list and no leaf. Asserted after the
/// state's borrow is released, so that a failure unwinds through the scopes' restores (which
/// borrow it again) instead of aborting.
fn report_stray(stray: Option<PathFact>) {
    debug_assert!(
        stray.is_none(),
        "a fact of a run is noted outside every phase of it: {stray:?}"
    );
}

/// Note each of `facts` again, where a stored evaluation that noted them is reused.
pub(crate) fn replay<'a>(facts: impl IntoIterator<Item = &'a PathFact>) {
    if !OPEN.get() {
        return;
    }
    let stray = with_state(|state| {
        let mut stray = None;
        for fact in facts {
            stray = stray.or(state.note(fact.clone()));
        }
        stray
    });
    report_stray(stray);
}

/// Closes the innermost collection on every exit, unwinding included: a fact noted is never
/// withdrawn, so even an unwinding collection hands its facts on.
struct Close {
    closed: bool,
}

impl Close {
    fn open(owned: bool) -> Self {
        with_state(|state| {
            state.sinks.push(Sink {
                facts: Facts::default(),
                owned,
            });
        });
        Self { closed: false }
    }

    fn take(mut self) -> Facts {
        self.closed = true;
        with_state(State::close).facts
    }
}

impl Drop for Close {
    fn drop(&mut self) {
        if !self.closed {
            with_state(|state| {
                state.close();
            });
        }
    }
}

/// Run `action`, a phase of a run, with a collection open, and return what it noted.
pub(crate) fn collect<T>(action: impl FnOnce() -> T) -> (T, Facts) {
    let close = Close::open(false);
    let result = action();
    (result, close.take())
}

/// Run `action`, work whose result belongs to one candidate only, with a candidate-owned
/// collection open, and return every fact it noted. The enclosing collection receives them as
/// `owned`: the caller attributes them to the candidate, or notes them again as shared work
/// ([`replay`]) when the candidate is not what the work produced.
pub(crate) fn owned<T>(action: impl FnOnce() -> T) -> (T, FactSet) {
    let close = Close::open(true);
    let result = action();
    let facts = close.take();
    (result, facts.all())
}

/// [`diagnostic::collect`] of `action`, followed by the facts it noted as diagnostics, in their
/// order: the list a phase attributes to the paths its result belongs to.
pub(crate) fn collect_with_diagnostics<T>(
    action: impl FnOnce() -> T,
) -> (T, Vec<BackendDiagnostic>) {
    let ((result, mut list), facts) = collect(|| diagnostic::collect(action));
    list.extend(diagnostics(&facts.all()));
    (result, list)
}

/// Emit `facts` as diagnostics into the current diagnostic collection, so that they follow the
/// attribution of the unit of work that collects them.
pub(crate) fn emit(facts: &FactSet) {
    for fact in facts {
        diagnostic::emit(fact.diagnostic());
    }
}

/// Run `action` with notes suspended: an evaluation whose value decides nothing that depends on
/// which admitted value it took. Restored on every exit.
pub(crate) fn suspend<T>(action: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            let previous = self.0;
            with_state(|state| state.suspended = previous);
        }
    }
    let _restore = Restore(with_state(|state| {
        std::mem::replace(&mut state.suspended, true)
    }));
    action()
}

/// A point in the notes of this thread, for [`since`] and [`noted_since`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Marker(u64);

/// The current point.
pub(crate) fn marker() -> Marker {
    Marker(STATE.with_borrow(|state| state.sequence))
}

/// Every distinct fact noted since `marker`, suspended or not.
pub(crate) fn since(marker: Marker) -> FactSet {
    STATE.with_borrow(|state| {
        state
            .stamps
            .iter()
            .filter(|(_, stamp)| *stamp > marker.0)
            .map(|(fact, _)| fact.clone())
            .collect()
    })
}

/// Whether anything was noted since `marker`.
pub(crate) fn noted_since(marker: Marker) -> bool {
    STATE.with_borrow(|state| state.sequence > marker.0)
}

/// Run `action`, a whole run, with the run-level record open, and return every distinct fact it
/// noted outside a suspension, in first-observed order. A record open around this one receives
/// them too.
pub(crate) fn run<T>(action: impl FnOnce() -> T) -> (T, Vec<PathFact>) {
    struct Restore(Option<Option<Vec<PathFact>>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            if let Some(outer) = self.0.take() {
                with_state(|state| {
                    let inner = std::mem::replace(&mut state.run, outer).unwrap_or_default();
                    if let Some(outer) = &mut state.run {
                        for fact in inner {
                            if !outer.contains(&fact) {
                                outer.push(fact);
                            }
                        }
                    }
                });
            }
        }
    }
    impl Restore {
        fn finish(mut self) -> Vec<PathFact> {
            let outer = self.0.take().expect("the record is closed once");
            with_state(|state| {
                let inner = std::mem::replace(&mut state.run, outer).unwrap_or_default();
                if let Some(outer) = &mut state.run {
                    for fact in &inner {
                        if !outer.contains(fact) {
                            outer.push(fact.clone());
                        }
                    }
                }
                inner
            })
        }
    }
    let restore = Restore(Some(with_state(|state| state.run.replace(Vec::new()))));
    let result = action();
    let facts = restore.finish();
    (result, facts)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::ChosenClass;

    fn fact(hook: &str) -> PathFact {
        PathFact::ChosenValue(ChosenValue::new(Arc::from(hook), ChosenClass::Order))
    }

    #[test]
    fn a_fact_survives_every_discard_of_the_diagnostic_channel_and_reaches_the_run_record() {
        let ((), run) = run(|| {
            let ((), facts) = collect(|| {
                let mark = diagnostic::mark();
                note(fact("A"));
                // The work is undone: its diagnostics are discarded, its facts are not.
                diagnostic::discard_since(mark);
                let ((), _buffered) = diagnostic::buffer(|| note(fact("B")));
            });
            assert_eq!(facts.shared, FactSet::from([fact("A"), fact("B")]));
        });
        assert_eq!(run, [fact("A"), fact("B")]);
    }

    #[test]
    fn owned_facts_are_kept_apart_and_replay_and_suspension_follow_the_rules() {
        let ((), run) = run(|| {
            let ((), facts) = collect(|| {
                let ((), owned) = owned(|| note(fact("O")));
                assert_eq!(owned, FactSet::from([fact("O")]));
                let marker = marker();
                suspend(|| note(fact("S")));
                // A memo filled under suspension still learns what it computed.
                assert_eq!(since(marker), FactSet::from([fact("S")]));
                assert!(noted_since(marker));
                replay(&FactSet::from([fact("S")]));
            });
            assert_eq!(facts.shared, FactSet::from([fact("S")]));
            assert_eq!(facts.owned, FactSet::from([fact("O")]));
        });
        assert_eq!(run, [fact("O"), fact("S")]);
        // Nothing is open: a note goes nowhere.
        note(fact("N"));
        assert!(!OPEN.get());
    }

    /// A note of a run outside every phase of it fails the debug assertion as an ordinary
    /// panic, raised once the state is no longer borrowed, and the unwinding run record hands its
    /// facts on and is closed.
    #[cfg(debug_assertions)]
    #[test]
    fn a_stray_note_of_a_run_fails_cleanly_and_the_record_is_restored() {
        let ((), outer) = run(|| {
            let stray = std::panic::catch_unwind(|| run(|| note(fact("A"))));
            assert!(stray.is_err());
        });
        assert_eq!(outer, [fact("A")]);
        assert!(!OPEN.get());
    }
}
