//! Path-relative normal forms recorded within a proof ([`NormalForms`]).
//!
//! ```toml algorithm
//! id = "backend.simplify.normal_forms"
//! name = "reuse of a clean simplification within a proof under an equal path condition"
//! sites = ["NormalForms", "NormalForms::served", "NormalForms::record", "simplified_through_record", "Probe::new", "Watch::start", "Watch::verdict", "holds_an_apart_name", "result_node_bytes", "scope", "aside", "NormalFormsScope"]
//! variable = "k = known predicates of the key; r = pairs of the key's renaming; c = conjuncts of a recorded simplification"
//! counters = ["SimplifyNormalFormsRecorded", "SimplifyNormalFormsServed", "SimplifyNormalFormsRefusedConsole", "SimplifyNormalFormsRefusedUnspecified", "SimplifyNormalFormsRefusedCoverage", "SimplifyNormalFormsRefusedStop", "SimplifyNormalFormsRefusedFailed", "SimplifyNormalFormsRefusedDiagnostic", "SimplifyNormalFormsRefusedPathFact", "SimplifyNormalFormsRefusedUnknown", "SimplifyNormalFormsRefusedEffect", "SimplifyNormalFormsRefusedApart"]
//! span = "none"
//! invariant = "A recorded simplification ran inside a proof's scope and an ApartScope, outside an execution and any run with a console, with no Unspecified attempt or lineage and no coverage collection open, did not stop or dismiss a stack stop, did not fail, received no undecided solver answer, noted no path fact, performed no effect, holds no name its own renamings apart minted, and emitted no diagnostic where a collector was open; its key holds the subject node, the renaming applied to it, the known predicates, the options, the definition, the solver, the thread's condition modes and the choice-sampling seed. It is served only under an equal key, only where no path-fact record is open unless one was open when it was recorded, and only where no collector is open unless one was open when it was recorded; a serve counts again the equation conditions and attempts it left undecided and moves the renaming-apart counter on by the names it minted."
//! tests = ["crates/k-rust-backend/src/simplify/normal_forms.rs", "crates/k-rust-backend/src/implication/destination.rs", "crates/k-rust-backend/src/proof.rs"]
//!
//! [[cost]]
//! mode = "lookup (every simplification a caller routes through the record while a proof's scope is open)"
//! bound = "the context checks (thread flags); the record's copy of the known list found by one comparison with the copy last found at the caller's place, O(k) predicates compared down to the first difference, and where that fails one hash lookup by content that hashes them; then a key with r cloned pairs and one map lookup, the subject compared by node and the known list by allocation. A hit clones the recorded simplification's shared handles and moves two thread counters on; a miss runs the simplification, which it pays, and then reads six thread counters, the result's effects, and, only where its renamings minted names, its variables (one cached set per term of the result and its c conjuncts). A record walks the distinct nodes of the subject and of the result once each (n = their number), O(n) with a hash set of node addresses, for its byte estimate."
//!
//! [[cost]]
//! mode = "retention"
//! bound = "per recorded simplification: its key (r pairs, a subject handle, a shared known list), and the simplification's shared handles; per distinct known list, one copy (k predicate handles) shared by every key that names it, and at most 4,096 noted places of a caller's copy. At most 65,536 records and an estimate of 64 MiB of these allocations and of the result's term nodes that are not the subject's; reaching either clears the record. The term nodes the keys and the simplifications hold are shared handles, kept alive until the proof's scope closes or the record clears."
//! ```
//!
//! A simplification is a function of what it reads: the term, the path condition it is
//! simplified under (the known predicates), the definition, the options, the solver's answers,
//! the thread's condition modes, the choice-sampling seed, and what else the thread holds open
//! (a console, an `Unspecified` attempt, a coverage collection, a path-fact record, a diagnostic
//! collector, the counter of names minted by renamings apart). Where it read no undecided solver
//! answer, and each of those else is closed or unread, an equal key gives an equal result: the
//! record serves it. A decided answer is a function of the query and the build, so an equation
//! condition or attempt the simplification left undecided on decided answers alone (as where
//! the solver finds both a condition and its negation satisfiable) is left undecided again by a
//! new simplification under an equal key; only an undecided answer (`Unknown`, which may be a
//! timeout) is refused.
//!
//! The record keeps only clean simplifications, whose reuse changes no output: no path fact
//! noted, no undecided answer, no stop, no effect, and no diagnostic emitted where a collector
//! was open. A diagnostic emitted with no collector open reaches no sink and moves no emission
//! position (`diagnostic::buffer` holds nothing without one), so a simplification that emitted
//! only there is recorded with `collected` unset, and served only where no collector is open
//! either: under a collector a new simplification is made, which would emit into it (the
//! condition memo's `MemoVerdict::replays_in_full`, with an empty replay). What a reuse does
//! replay are two thread counters a later reader compares: the equation conditions and attempts
//! it left undecided (`simplify::UNDECIDED`, read by `simplify_ground_subterm` and by an
//! enclosing simplification routed through the record), counted again as many times, and the
//! renaming-apart counter, moved on as far.
//!
//! The renaming-apart argument needs an open `rule::ApartScope` ([`Probe::new`] consults the
//! record only then): within the outermost scope the counter only grows, so every `!apart` name
//! in scope was minted below the current counter, and work run with the names restored
//! (`rule::with_apart_names_restored`, `coverage::isolate`) does not outlive itself. A new
//! simplification at a serve point mints as many names as the recorded one, since a renaming
//! skips no number; a result that holds a name its own renamings minted is refused, since a new
//! one would number it from another start. Outside every scope an entry point would restart the
//! counter at 0, and the count a recorded run minted would not say where a new one ends.
//!
//! The record is keyed by the path condition itself, not by implication: a stronger path
//! condition can decide more, so a normal form under `P` is one under `P` only. At a
//! destination the rule conditions active against re-entry are empty; a caller that simplifies
//! under active rule conditions (the term round loop, K17 part b) must add them to the key or
//! route only where they are empty, since an attempt on a condition met again is `Recurred`
//! there.
//!
//! A proof opens the record ([`scope`]); a caller routes a simplification through it with
//! [`simplified_through_record`], naming the node the result is a function of. The implication
//! check's destination does (`implication::Destination::prepare`); the term round loop of the
//! simplifier, at a non-ground subterm without the evaluated mark, is the other site the record
//! is meant for (K17 part b).

use std::{
    cell::{Cell, RefCell},
    hash::{Hash, Hasher},
    sync::Arc,
};

use k_rust_kore::measure::{self, Counter};
use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    InternTable, Interned, Simplification, SimplificationError, SimplificationOptions,
    UNSPECIFIED_VALUES, UnspecifiedEvaluation, slice_place, solver_address,
};
use crate::{
    definition::BackendDefinition,
    evaluation::EvaluationMode,
    rule::Predicate,
    smt::SmtSolver,
    stop::{self, Stoppable},
    substitution::Substitution,
    term::{Term, Variable},
};

/// The most simplifications [`NormalForms`] holds at once; reaching it clears the record.
const NORMAL_FORMS_CAPACITY: usize = 1 << 16;

/// The most bytes, by [`NormalForms`]'s estimate, it holds at once; reaching it clears the record.
const NORMAL_FORMS_BYTES: usize = 64 << 20;

/// The clean simplifications of one proof, by everything they read ([`NormalFormKey`]).
///
/// The record is bounded by its number of entries ([`NORMAL_FORMS_CAPACITY`]) and by an
/// estimate of the bytes it holds in place ([`NORMAL_FORMS_BYTES`]); reaching either clears it,
/// and a cleared record simplifies again what it no longer holds. The estimate counts the
/// record's own allocations, not the term nodes its keys and results share with the run, which
/// an entry keeps alive until the proof ends or the record clears.
#[derive(Default)]
struct NormalForms {
    entries: FxHashMap<NormalFormKey, Recorded>,
    /// Every known-predicate list a key names, once.
    knowns: InternTable<[Predicate]>,
    /// The estimate of the bytes held ([`NORMAL_FORMS_BYTES`]).
    retained: usize,
}

/// A recorded simplification.
struct Recorded {
    simplification: Simplification,
    /// Whether a path-fact record was open when it was simplified, so that "noted none" covers
    /// what an open record would have received.
    facts_open: bool,
    /// Whether a diagnostic collector was open when it was simplified, so that "emitted none"
    /// covers what an open collector would have received.
    collected: bool,
    /// What a reuse counts again ([`Replayed`]).
    replayed: Replayed,
    /// Its share of [`NormalForms::retained`].
    bytes: usize,
}

/// The thread counters a recorded simplification moved, which a reuse moves as far.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Replayed {
    /// The names its renamings apart minted: a reuse moves the thread's counter on by as many,
    /// so that the renamings after it mint what they would have minted after a simplification.
    apart: u64,
    /// The equation conditions and attempts it left undecided on decided answers
    /// (`simplify::UNDECIDED`): a reuse counts as many, so that a reader comparing two readings
    /// around it reads what it would read around a simplification.
    undecided: u64,
}

/// A served simplification and what its reuse counts again.
struct Served {
    simplification: Simplification,
    replayed: Replayed,
}

/// Everything a recorded simplification read, but the solver's answers: [`Scalars`] names the
/// solver that gives them.
struct NormalFormKey {
    /// The node the caller simplifies after renaming it by `renaming`, held so that no other
    /// node takes its address while the key exists; compared by node.
    subject: Term,
    /// The renaming applied to `subject` before it is simplified, in variable order (a
    /// destination's existentials freshened apart from the state; empty for a subterm simplified
    /// as it is).
    renaming: Box<[(Variable, Term)]>,
    /// The known predicates, the record's copy ([`NormalForms::knowns`]).
    known: Interned<[Predicate]>,
    scalars: Scalars,
}

impl PartialEq for NormalFormKey {
    fn eq(&self, other: &Self) -> bool {
        self.subject.ptr_eq(&other.subject)
            && self.known.address() == other.known.address()
            && self.scalars == other.scalars
            && self.renaming == other.renaming
    }
}

impl Eq for NormalFormKey {}

impl Hash for NormalFormKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.subject.node_address().hash(state);
        self.known.address().hash(state);
        self.scalars.hash(state);
        self.renaming.hash(state);
    }
}

/// The parts of a key that are plain values: the definition and the solver by address, the
/// options, and the thread's modes that change how a condition is simplified.
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct Scalars {
    definition: usize,
    solver: usize,
    max_iterations: usize,
    keep_partial: bool,
    mode: EvaluationMode,
    general_path: bool,
    stated_ceil_conditions: bool,
    /// The choice-sampling seed in force (`choice_sampling::seed`, always `None` without the
    /// feature): a value the definition leaves open is chosen by it.
    seed: Option<u64>,
}

thread_local! {
    /// The open record on this thread, `None` outside every [`scope`].
    static NORMAL_FORMS: RefCell<Option<NormalForms>> = const { RefCell::new(None) };
    /// The open [`scope`]s on this thread.
    static DEPTH: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
thread_local! {
    static NORMAL_FORMS_OFF: Cell<bool> = const { Cell::new(false) };
}

/// Run `action` with nothing recorded or served ([`NormalForms`]), for a test that compares a
/// proof with and without the record.
#[cfg(test)]
pub(crate) fn without_normal_forms<T>(action: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            NORMAL_FORMS_OFF.set(self.0);
        }
    }
    let _restore = Restore(NORMAL_FORMS_OFF.replace(true));
    action()
}

/// An open scope of the record on this thread ([`scope`]).
pub(crate) struct NormalFormsScope(());

/// Keep the clean simplifications routed through [`simplified_through_record`] while the scope
/// is open: a proof opens one, so that a destination simplified again under the same state
/// constraints at a later check is served. A scope opened inside another shares its record; the
/// outermost one drops it when it closes.
///
/// An undecided solver answer is detected through `smt::undecided_on_thread`, which counts the
/// answers of a solver wrapped in `smt::UndecidedCounting`: the work inside must query such a
/// solver (a proof queries the condition memo's, `simplify::condition_memo_scope`).
pub(crate) fn scope() -> NormalFormsScope {
    if DEPTH.replace(DEPTH.get() + 1) == 0 {
        NORMAL_FORMS.set(Some(NormalForms::default()));
    }
    NormalFormsScope(())
}

impl Drop for NormalFormsScope {
    fn drop(&mut self) {
        let depth = DEPTH.get() - 1;
        DEPTH.set(depth);
        if depth == 0 {
            drop(NORMAL_FORMS.take());
        }
    }
}

/// Run `action` with the thread's record set aside, and restore it afterwards, also when
/// `action` unwinds: work inside is neither served nor recorded (`coverage::isolated`, whose
/// emissions and facts go nowhere, so that a clean-looking simplification there need not be).
pub(crate) fn aside<T>(action: impl FnOnce() -> T) -> T {
    struct Restore(Option<(Option<NormalForms>, usize)>);
    impl Drop for Restore {
        fn drop(&mut self) {
            if let Some((record, depth)) = self.0.take() {
                NORMAL_FORMS.set(record);
                DEPTH.set(depth);
            }
        }
    }
    let _restore = Restore(Some((NORMAL_FORMS.take(), DEPTH.replace(0))));
    action()
}

/// Why a simplification is neither recorded nor served, each counted by its own counter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Refusal {
    /// An execution, or a run with a console: the evaluation reads and advances the console.
    Console,
    /// An `Unspecified` attempt or recording lineage is open, whose reads the key does not hold.
    Unspecified,
    /// A coverage collection is open, which a reuse would not report to.
    Coverage,
    /// The simplification stopped, or dismissed a stop for lack of native stack, which depends
    /// on the depth it ran at.
    Stop,
    /// The simplification failed.
    Failed,
    /// It emitted a diagnostic while a collector was open.
    Diagnostic,
    /// It noted a path fact.
    PathFact,
    /// It received an undecided solver answer, which may be a timeout. (A verdict the condition
    /// memo serves from an earlier decision counts no answer again; the memo keeps one that rests
    /// on an undecided answer only where those answers are a function of the query,
    /// `SmtSolver::undecided_answers_reproducible`.)
    Unknown,
    /// It performed a builtin effect.
    Effect,
    /// Its result holds a name its own renamings apart minted, which a new simplification would
    /// mint under another number, or the renaming-apart counter went back during it.
    Apart,
}

impl Refusal {
    fn counter(self) -> Counter {
        match self {
            Self::Console => Counter::SimplifyNormalFormsRefusedConsole,
            Self::Unspecified => Counter::SimplifyNormalFormsRefusedUnspecified,
            Self::Coverage => Counter::SimplifyNormalFormsRefusedCoverage,
            Self::Stop => Counter::SimplifyNormalFormsRefusedStop,
            Self::Failed => Counter::SimplifyNormalFormsRefusedFailed,
            Self::Diagnostic => Counter::SimplifyNormalFormsRefusedDiagnostic,
            Self::PathFact => Counter::SimplifyNormalFormsRefusedPathFact,
            Self::Unknown => Counter::SimplifyNormalFormsRefusedUnknown,
            Self::Effect => Counter::SimplifyNormalFormsRefusedEffect,
            Self::Apart => Counter::SimplifyNormalFormsRefusedApart,
        }
    }
}

/// A simplification's inputs, borrowed where they are, for a lookup and a record.
struct Probe<'a> {
    subject: &'a Term,
    renaming: &'a Substitution,
    known: &'a [Predicate],
    scalars: Scalars,
}

impl<'a> Probe<'a> {
    /// The probe of a simplification now; `None` where no record is open or no
    /// `rule::ApartScope` is (the renaming-apart argument of the module doc needs one; a proof
    /// opens one around its record), and a refusal where the thread holds open something the key
    /// does not.
    fn new(
        definition: &BackendDefinition,
        subject: &'a Term,
        renaming: &'a Substitution,
        known: &'a [Predicate],
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) -> Option<Result<Self, Refusal>> {
        #[cfg(test)]
        if NORMAL_FORMS_OFF.get() {
            return None;
        }
        if DEPTH.get() == 0 || !crate::rule::apart_scope_open() {
            return None;
        }
        let mode = crate::evaluation::current();
        if mode == EvaluationMode::Execution || crate::evaluation::console_attached() {
            return Some(Err(Refusal::Console));
        }
        if UnspecifiedEvaluation::any_open()
            || UNSPECIFIED_VALUES.with_borrow(|table| table.scopes > 0)
        {
            return Some(Err(Refusal::Unspecified));
        }
        if crate::coverage::collecting() {
            return Some(Err(Refusal::Coverage));
        }
        Some(Ok(Self {
            subject,
            renaming,
            known,
            scalars: Scalars {
                definition: std::ptr::from_ref(definition).addr(),
                solver: solver_address(solver),
                max_iterations: options.max_iterations,
                keep_partial: options.budget == super::BudgetPolicy::KeepPartial,
                mode,
                general_path: crate::condition::on_general_condition_path(),
                stated_ceil_conditions: crate::definedness::ceil_conditions_stated(),
                seed: crate::choice_sampling::seed(),
            },
        }))
    }

    fn renaming(&self) -> Box<[(Variable, Term)]> {
        self.renaming
            .iter()
            .map(|(original, renamed)| (original.clone(), renamed.clone()))
            .collect()
    }
}

/// Simplify through the thread's record: `simplify` must be the simplification of `subject`
/// renamed by `renaming` under the known predicates `known`, with `options`, `definition` and
/// `solver` (a function of exactly those and of the solver's answers). Where a scope is open
/// ([`scope`]) and an equal key was recorded, the recorded simplification is returned, the
/// thread counters it moved are moved as far ([`Replayed`]), and `simplify` does not run;
/// otherwise it runs, and its result is recorded when it was clean ([`NormalForms`]). Without an
/// open scope this is `simplify()`.
///
/// Under the `check-normal-forms` feature (every test build of this crate), a served
/// simplification is compared with the one `simplify` gives now from scratch ([`check_served`]).
pub(crate) fn simplified_through_record(
    definition: &BackendDefinition,
    subject: &Term,
    renaming: &Substitution,
    known: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    simplify: impl FnOnce() -> Stoppable<Result<Simplification, SimplificationError>>,
) -> Stoppable<Result<Simplification, SimplificationError>> {
    let probe = match Probe::new(definition, subject, renaming, known, options, solver) {
        None => return simplify(),
        Some(Err(refusal)) => {
            measure::bump(refusal.counter());
            return simplify();
        }
        Some(Ok(probe)) => probe,
    };
    if let Some(served) = NormalForms::served(&probe) {
        measure::bump(Counter::SimplifyNormalFormsServed);
        // Checked where a new simplification would run: before the reuse moves any counter.
        #[cfg(feature = "check-normal-forms")]
        check_served(&served, simplify);
        crate::rule::skip_apart_names(served.replayed.apart);
        super::note_undecided_times(served.replayed.undecided);
        return Ok(Ok(served.simplification));
    }
    let watch = Watch::start();
    let (result, stack_stops) = stop::counting_stack_stops(simplify);
    match watch.verdict(&result, stack_stops) {
        Err(refusal) => measure::bump(refusal.counter()),
        Ok((simplification, replayed)) => {
            NormalForms::record(
                &probe,
                simplification.clone(),
                watch.facts_open,
                watch.collected,
                replayed,
            );
            measure::bump(Counter::SimplifyNormalFormsRecorded);
        }
    }
    result
}

/// The thread's counters at the start of a simplification, read again at its end to say
/// whether it was clean ([`Watch::verdict`]).
struct Watch {
    emitted: u64,
    collected: bool,
    facts: crate::path_facts::Marker,
    facts_open: bool,
    unknown: usize,
    undecided: u64,
    apart: u64,
}

impl Watch {
    fn start() -> Self {
        Self {
            emitted: crate::diagnostic::emitted(),
            collected: crate::diagnostic::collecting(),
            facts: crate::path_facts::marker(),
            facts_open: crate::path_facts::is_open(),
            unknown: crate::smt::undecided_on_thread(),
            undecided: super::undecided_so_far(),
            apart: crate::rule::apart_counter(),
        }
    }

    /// The names the renamings apart minted since the start; `None` where the counter went
    /// back, which only the opening of an outermost `rule::ApartScope` since the start does
    /// (it restarts the counter at 0; [`Probe::new`] consults the record only inside one).
    fn apart(&self) -> Option<u64> {
        crate::rule::apart_counter().checked_sub(self.apart)
    }

    /// The simplification that ended with `result`, having dismissed `stack_stops` stops for
    /// lack of native stack, with the counters a reuse of it moves, when it was clean; why it
    /// is not recorded otherwise, the first reason found.
    fn verdict<'r>(
        &self,
        result: &'r Stoppable<Result<Simplification, SimplificationError>>,
        stack_stops: usize,
    ) -> Result<(&'r Simplification, Replayed), Refusal> {
        let simplification = match result {
            Err(_) => return Err(Refusal::Stop),
            Ok(_) if stack_stops > 0 => return Err(Refusal::Stop),
            Ok(Err(_)) => return Err(Refusal::Failed),
            Ok(Ok(simplification)) => simplification,
        };
        // An emission with no collector open reaches no sink and moves no emission position:
        // the entry is served only where none is open either (`Recorded::collected`).
        if self.collected && crate::diagnostic::emitted() != self.emitted {
            return Err(Refusal::Diagnostic);
        }
        if crate::path_facts::noted_since(self.facts) {
            return Err(Refusal::PathFact);
        }
        if crate::smt::undecided_on_thread() != self.unknown {
            return Err(Refusal::Unknown);
        }
        if !simplification.effects.is_empty() {
            return Err(Refusal::Effect);
        }
        let Some(apart) = self.apart() else {
            return Err(Refusal::Apart);
        };
        if apart > 0 && holds_an_apart_name(simplification) {
            return Err(Refusal::Apart);
        }
        let undecided = super::undecided_so_far().wrapping_sub(self.undecided);
        Ok((simplification, Replayed { apart, undecided }))
    }
}

/// Visit every term of `simplification` that a reader of it sees: its term, its conjuncts'
/// terms, its undefined term, the term it found `\bottom` at with the `total` applications named
/// there, and its contradicted `total` application with the undefined term that reached it.
fn visit_result_terms(simplification: &Simplification, visit: &mut impl FnMut(&Term)) {
    visit(&simplification.term);
    if let Some(term) = &simplification.undefined_term {
        visit(term);
    }
    for conjunct in simplification.conjoined() {
        conjunct.visit_terms(&mut *visit);
    }
    if let Some(bottom) = &simplification.bottom {
        visit(&bottom.term);
        bottom.named.iter().for_each(&mut *visit);
    }
    if let Some(contradicted) = &simplification.contradicted_total {
        visit(&contradicted.application);
        visit(&contradicted.undefined_term);
    }
}

/// Whether a term of `simplification` ([`visit_result_terms`]) holds a name minted by a
/// renaming apart.
fn holds_an_apart_name(simplification: &Simplification) -> bool {
    let mut found = false;
    visit_result_terms(simplification, &mut |term| {
        found = found
            || term
                .attributes()
                .variables
                .iter()
                .any(crate::rule::is_apart_name);
    });
    found
}

/// The bytes a term node takes in place, by the estimate of [`result_node_bytes`].
const NODE_BYTES: usize = std::mem::size_of::<crate::term::TermKind>()
    + std::mem::size_of::<crate::term::TermAttributes>()
    + 2 * std::mem::size_of::<usize>();

/// The bytes, [`NODE_BYTES`] each, of the distinct term nodes of `simplification`
/// ([`visit_result_terms`]) that are not nodes of `subject`: those an entry may keep alive after
/// the run drops them. The subject's nodes are the caller's, a proof's destination, which the
/// run holds anyway.
fn result_node_bytes(subject: &Term, simplification: &Simplification) -> usize {
    fn walk(root: &Term, seen: &mut FxHashSet<usize>) {
        let mut pending = vec![root];
        while let Some(term) = pending.pop() {
            if seen.insert(term.node_address()) {
                pending.extend(crate::term::immediate_children(term.kind()));
            }
        }
    }
    let mut seen = FxHashSet::default();
    walk(subject, &mut seen);
    let shared = seen.len();
    visit_result_terms(simplification, &mut |term| walk(term, &mut seen));
    (seen.len() - shared) * NODE_BYTES
}

impl NormalForms {
    /// The simplification recorded under `probe`'s key, with the counters its reuse moves;
    /// `None` when there is none, or where a reuse would not replay what a new simplification
    /// notes or emits: a path-fact record is open that was not open when it was recorded, or a
    /// collector is that was not.
    fn served(probe: &Probe<'_>) -> Option<Served> {
        NORMAL_FORMS.with_borrow_mut(|record| {
            let record = record.as_mut()?;
            // A list no key names is in no key.
            let known = Arc::clone(record.knowns.find(probe.known, slice_place(probe.known))?);
            let key = NormalFormKey {
                subject: probe.subject.clone(),
                renaming: probe.renaming(),
                known: Interned(known),
                scalars: probe.scalars,
            };
            let recorded = record.entries.get(&key)?;
            if !recorded.facts_open && crate::path_facts::is_open() {
                return None;
            }
            if !recorded.collected && crate::diagnostic::collecting() {
                return None;
            }
            Some(Served {
                simplification: recorded.simplification.clone(),
                replayed: recorded.replayed,
            })
        })
    }

    fn record(
        probe: &Probe<'_>,
        simplification: Simplification,
        facts_open: bool,
        collected: bool,
        replayed: Replayed,
    ) {
        let renaming = probe.renaming();
        let bytes = std::mem::size_of::<(NormalFormKey, Recorded)>()
            + std::mem::size_of_val(&*renaming)
            + simplification.conjoined().len() * std::mem::size_of::<Predicate>()
            + simplification.applied_rules.len() * std::mem::size_of::<String>()
            + result_node_bytes(probe.subject, &simplification);
        NORMAL_FORMS.with_borrow_mut(|record| {
            let Some(record) = record.as_mut() else {
                return;
            };
            // A bound on the memory the record holds, not on what is served: a cleared record
            // simplifies again what it no longer holds.
            if record.entries.len() >= NORMAL_FORMS_CAPACITY
                || record.retained >= NORMAL_FORMS_BYTES
            {
                record.entries.clear();
                record.knowns.clear();
                record.retained = 0;
            }
            let known = record.intern_known(probe.known);
            let key = NormalFormKey {
                subject: probe.subject.clone(),
                renaming,
                known,
                scalars: probe.scalars,
            };
            record.retained += bytes;
            let recorded = Recorded {
                simplification,
                facts_open,
                collected,
                replayed,
                bytes,
            };
            // A simplification recorded again where the one held was not served (a path-fact
            // record or a collector open now and not then) replaces it.
            if let Some(replaced) = record.entries.insert(key, recorded) {
                record.retained -= replaced.bytes;
            }
        });
    }

    /// The one copy of `known` the record holds, made now if there is none.
    fn intern_known(&mut self, known: &[Predicate]) -> Interned<[Predicate]> {
        let place = slice_place(known);
        if let Some(held) = self.knowns.find(known, place) {
            return Interned(Arc::clone(held));
        }
        self.retained += std::mem::size_of_val(known) + 2 * std::mem::size_of::<Arc<[Predicate]>>();
        Interned(self.knowns.insert(place, Arc::from(known)))
    }
}

/// The check of a served simplification (`check-normal-forms`): `simplify` now, from scratch,
/// gives what was served and moves the counters the reuse moves as far ([`Replayed`]), and does
/// so cleanly where the reuse replays nothing: it emits nothing where a collector is open, and
/// notes nothing where a path-fact record is.
///
/// From scratch: the record, the condition memo, the results of pure hooks and the records of
/// `Unspecified` evaluations are set aside, as `coverage::isolate` sets them aside, so that a
/// served simplification that agrees with a new one only through what those hold is caught, and
/// the check fills none of them for the run. Nothing it emits, notes or counts reaches the run:
/// emissions are discarded (and not counted in `diagnostic::emitted`), notes go to a record of
/// the check's own, opened only where one is open at the serve, the work counters are suppressed,
/// and the renaming-apart counter and `simplify::UNDECIDED` are restored. A simplification that
/// stops or meets an undecided solver answer now proves nothing either way (a deadline, a
/// timeout), and is not compared; that answer stays counted in `smt::undecided_on_thread`.
#[cfg(feature = "check-normal-forms")]
fn check_served(
    served: &Served,
    simplify: impl FnOnce() -> Stoppable<Result<Simplification, SimplificationError>>,
) {
    let collecting = crate::diagnostic::collecting();
    let facts_open = crate::path_facts::is_open();
    let recompute = || {
        let emitted = crate::diagnostic::emitted();
        let facts = crate::path_facts::marker();
        let unknown = crate::smt::undecided_on_thread();
        let undecided = super::undecided_so_far();
        let apart = crate::rule::apart_counter();
        let (result, stack_stops) = stop::counting_stack_stops(simplify);
        let outcome = match result {
            Err(stop) => {
                stop.forgo_refinement();
                None
            }
            Ok(_) if stack_stops > 0 => None,
            Ok(_) if crate::smt::undecided_on_thread() != unknown => None,
            Ok(result) => Some(result),
        };
        let replayed = crate::rule::apart_counter()
            .checked_sub(apart)
            .map(|apart| Replayed {
                apart,
                undecided: super::undecided_so_far().wrapping_sub(undecided),
            });
        (
            outcome,
            crate::diagnostic::emitted() != emitted,
            crate::path_facts::noted_since(facts),
            replayed,
        )
    };
    let (outcome, emitted, noted, replayed) = measure::without_counting(|| {
        super::with_undecided_restored(|| {
            crate::rule::with_apart_names_restored(|| {
                crate::diagnostic::discarded(|| {
                    crate::path_facts::discarded(|| {
                        let from_scratch = || {
                            aside(|| {
                                super::condition_memo_aside(|| {
                                    crate::deferred::hook_values_aside(|| {
                                        super::unspecified_values_aside(recompute)
                                    })
                                })
                            })
                        };
                        if facts_open {
                            crate::path_facts::collect(from_scratch).0
                        } else {
                            from_scratch()
                        }
                    })
                })
            })
        })
    });
    let Some(fresh) = outcome else {
        return;
    };
    let fresh = fresh.expect("a served simplification is one that succeeds when done again");
    let emitted = emitted && collecting;
    assert!(
        fresh == served.simplification && !emitted && !noted && replayed == Some(served.replayed),
        "a served simplification differs from a new one, or the new one is not clean \
         (emitted under a collector: {emitted}, noted a fact: {noted}, counters moved: \
         {replayed:?}, replayed: {:?}):\nserved: {:#?}\nnew: {fresh:#?}",
        served.replayed,
        served.simplification,
    );
}
