//! Path-relative normal forms recorded within a proof ([`NormalForms`]).
//!
//! ```toml algorithm
//! id = "backend.simplify.normal_forms"
//! name = "reuse of a clean simplification within a proof under an equal path condition"
//! sites = ["NormalForms", "NormalForms::served", "NormalForms::record", "NormalForms::count_new_nodes", "NormalForms::intern_path_condition", "simplified_through_record", "subterm_lookup", "subterm_recorded", "consult", "serve", "Pending::start", "Pending::finish", "open", "Probe::new", "Watch::start", "Watch::verdict", "Watch::counts", "holds_an_apart_name", "scope", "aside", "NormalFormsScope"]
//! variable = "k = known predicates of the key; p = bindings and replacements of a subterm key's path condition; r = pairs of the key's renaming; c = conjuncts of a recorded simplification; n = term nodes of a recorded subject and result the record has not counted yet"
//! counters = ["SimplifyNormalFormsRecorded", "SimplifyNormalFormsServed", "SimplifyNormalFormsSubtermRecorded", "SimplifyNormalFormsSubtermServed", "SimplifyNormalFormsRefusedConsole", "SimplifyNormalFormsRefusedUnspecified", "SimplifyNormalFormsRefusedCoverage", "SimplifyNormalFormsRefusedStop", "SimplifyNormalFormsRefusedFailed", "SimplifyNormalFormsRefusedDiagnostic", "SimplifyNormalFormsRefusedPathFact", "SimplifyNormalFormsRefusedUnknown", "SimplifyNormalFormsRefusedEffect", "SimplifyNormalFormsRefusedApart", "SimplifyNormalFormsSubtermRefusedConsole", "SimplifyNormalFormsSubtermRefusedUnspecified", "SimplifyNormalFormsSubtermRefusedCoverage", "SimplifyNormalFormsSubtermRefusedStop", "SimplifyNormalFormsSubtermRefusedFailed", "SimplifyNormalFormsSubtermRefusedDiagnostic", "SimplifyNormalFormsSubtermRefusedPathFact", "SimplifyNormalFormsSubtermRefusedUnknown", "SimplifyNormalFormsSubtermRefusedEffect", "SimplifyNormalFormsSubtermRefusedApart", "SimplifyNormalFormsCleared"]
//! span = "none"
//! invariant = "A recorded simplification ran inside a proof's scope and an ApartScope, outside an execution and any run with a console, with no Unspecified attempt or lineage and no coverage collection open, did not stop or dismiss a stack stop, did not fail, received no undecided solver answer, noted no path fact, performed no effect, holds no name its own renamings apart minted, and emitted no diagnostic where a collector was open; its key holds the subject node, the renaming applied to it, the known predicates, for a subterm the path condition it was simplified under, the options, the iteration budget it started from, the definition, the solver, the thread's condition modes, whether claims are checked and the choice-sampling seed. A subterm is routed only where no rule condition is active against re-entry. It is served only under an equal key, only where no path-fact record is open unless one was open when it was recorded, and only where no collector is open unless one was open when it was recorded; a serve counts again the equation conditions and attempts it left undecided, moves the renaming-apart counter on by the names it minted, and leaves the iteration budget it left."
//! tests = ["crates/k-rust-backend/src/simplify/normal_forms.rs", "crates/k-rust-backend/src/implication/destination.rs", "crates/k-rust-backend/src/proof.rs"]
//!
//! [[cost]]
//! mode = "lookup (every simplification a caller routes through the record while a proof's scope is open)"
//! bound = "the context checks (thread flags); the record's copy of the known list found by one comparison with the copy last found at the caller's place, O(k) predicates compared down to the first difference, and where that fails one hash lookup by content that hashes them; for a subterm the record's copy of the path condition found the same way, O(p); then a key with r cloned pairs and one map lookup, the subject compared by node and the known list and path condition by allocation. A hit clones the recorded simplification's shared handles and moves two thread counters on; a miss boxes the probe and the thread's counters at the start (off the caller's recursive frame), runs the simplification, which it pays, and then reads seven thread counters, the result's effects, and, only where its renamings minted names, its variables (one cached set per term of the result and its c conjuncts). A record walks, for its byte estimate, only the nodes of its subject and result no earlier record counted, O(n) with one hash-set insertion each, so the records of nested subterms together walk each node they hold once."
//!
//! [[cost]]
//! mode = "retention"
//! bound = "per recorded simplification: its key (r pairs, a subject handle, a shared known list, a shared path condition), and the simplification's shared handles; per distinct known list, one copy (k predicate handles), and per distinct path condition, one copy (p binding and replacement handles), each shared by every key that names it, with at most 4,096 noted places of a caller's copy each; one address per term node counted. At most 65,536 records and an estimate of 64 MiB of these allocations and of the term nodes the subjects and results hold, each node counted once at a fixed size per node (a node count: what a node holds on the heap beyond its place is left out, and conjuncts and rule names nested entries share are counted at each); reaching either clears the record. The term nodes the keys and the simplifications hold are shared handles, kept alive until the proof's scope closes or the record clears."
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
//! destination the rule conditions active against re-entry are empty; the term simplifier
//! routes a subterm only where they are empty too, since an attempt on a condition met again is
//! `Recurred` under them, and the key does not hold them.
//!
//! A proof opens the record ([`scope`]); a caller routes a simplification through it with
//! [`simplified_through_record`] or [`subterm_lookup`] and [`subterm_recorded`], naming the
//! node the result is a function of. The implication check's destination does (`implication::Destination::prepare`),
//! and so does the term simplifier at each non-ground compound term it enters with no rule
//! condition active (`simplify::simplify_on_stack`), the configuration's subterms among them: an
//! application whose equation's `requires` stays undecided is not evaluated and carries no mark
//! (the mark is ground-only), and each step of a proof enters it again under a path condition
//! that has not changed.
//!
//! A subterm is simplified under a path condition that is not always the one its known
//! predicates give (a conjunct of a conjunction is simplified under the others' equalities and
//! not its own), so a subterm's key holds the path condition too. It is simplified within its
//! caller's lineage, from the iteration budget that lineage has left: the key holds that
//! budget, since one exhausted cuts the simplification short (or makes it fail), and a serve
//! leaves the caller the budget the recorded simplification left. Whether contradicted claims
//! are checked is in every key, since a lineage reports where it found `\bottom` only then.
//!
//! A serve does none of the work a new simplification would do, so it spends none of the polls
//! of `stop::check` or the native stack that work would spend: where a new simplification would
//! stop, at an enclosing `stop::with_poll_budget`'s last poll or for want of stack, a served one
//! is returned. Neither is reachable within a proof today: a poll budget is in force only under
//! `coverage::isolated`, which sets the record aside ([`aside`]), and in load-time checks, which
//! open no proof's scope; a stop for want of stack depends on the thread's stack and on the depth
//! the work runs at, not on its inputs, and a simplification that met one is never recorded.

use std::{
    cell::{Cell, RefCell},
    hash::{Hash, Hasher},
    sync::Arc,
};

use k_rust_kore::measure::{self, Counter};
use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    InternTable, Interned, PathConditionReplacements, Simplification, SimplificationError,
    SimplificationOptions, TermAssumptions, UNSPECIFIED_VALUES, UnspecifiedEvaluation, slice_place,
    solver_address,
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
/// estimate of the bytes it holds ([`NORMAL_FORMS_BYTES`]); reaching either clears it (counted,
/// `simplify.normal_forms.cleared`), and a cleared record simplifies again what it no longer
/// holds. The estimate counts the record's own allocations (each key and entry in place, its
/// renaming pairs, its conjunct and rule-name handles, the interned lists) and the term nodes its
/// subjects and results hold, each node once ([`NormalForms::count_new_nodes`]), at
/// [`NODE_BYTES`] apiece: it is a count of nodes, not of bytes held. It leaves out what a node
/// holds on the heap beyond its place (argument slices, the increments of its variable set, a
/// collection's chunked storage, which [`crate::term::immediate_children`] does not walk), and
/// it counts again at every entry the conjuncts and rule names that entries share (a nested
/// entry's `applied_rules` are part of the enclosing entry's).
#[derive(Default)]
struct NormalForms {
    entries: FxHashMap<NormalFormKey, Recorded>,
    /// Every known-predicate list a key names, once.
    knowns: InternTable<[Predicate]>,
    /// Every path condition a subterm's key names, once.
    path_conditions: InternTable<PathConditionReplacements>,
    /// The estimate of the bytes held ([`NORMAL_FORMS_BYTES`]).
    retained: usize,
    /// The addresses of the term nodes `retained` counts ([`NormalForms::count_new_nodes`]).
    counted: FxHashSet<usize>,
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
    /// The iteration budget it left its caller's lineage, from the budget keyed
    /// ([`Scalars::budget`]): a reuse leaves as much.
    budget: usize,
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
    /// The path condition a subterm is simplified under, the record's copy
    /// ([`NormalForms::path_conditions`]); `None` at a destination, whose path condition is the
    /// one its known predicates give (`simplify::simplify_term_entry`).
    path_condition: Option<Interned<PathConditionReplacements>>,
    scalars: Scalars,
}

impl NormalFormKey {
    fn path_condition_address(&self) -> Option<usize> {
        self.path_condition.as_ref().map(Interned::address)
    }
}

impl PartialEq for NormalFormKey {
    fn eq(&self, other: &Self) -> bool {
        self.subject.ptr_eq(&other.subject)
            && self.known.address() == other.known.address()
            && self.path_condition_address() == other.path_condition_address()
            && self.scalars == other.scalars
            && self.renaming == other.renaming
    }
}

impl Eq for NormalFormKey {}

impl Hash for NormalFormKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.subject.node_address().hash(state);
        self.known.address().hash(state);
        self.path_condition_address().hash(state);
        self.scalars.hash(state);
        self.renaming.hash(state);
    }
}

/// The parts of a key that are plain values: the definition and the solver by address, the
/// options, the iteration budget, and the thread's modes that change how a condition is
/// simplified.
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct Scalars {
    definition: usize,
    solver: usize,
    max_iterations: usize,
    keep_partial: bool,
    /// The iteration budget left to the lineage the simplification runs in: a subterm's is its
    /// caller's (`simplify::simplify_on_stack`'s `remaining`), which an exhausted budget cuts
    /// short; a destination's is `max_iterations`, since its simplification starts a lineage.
    budget: usize,
    /// Whether contradicted claims are checked (`path_facts::checking_claims`): a lineage then
    /// reports where it found `\bottom` (`FoundBottom`), which it does not report otherwise.
    claims_checked: bool,
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
    /// The subterm refusals found after the simplification ([`Watch::verdict`]) counted on this
    /// thread so far, by reason (`Refusal as usize`): such a reason (an undecided answer, a
    /// stop, a minted name the result holds) reaches every routed simplification that holds the
    /// one that met it, and [`Watch::counts`] counts it at the innermost only.
    static SUBTERM_REFUSALS: Cell<[u64; Refusal::COUNT]> = const { Cell::new([0; Refusal::COUNT]) };
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

/// Keep the clean simplifications routed through [`simplified_through_record`] and
/// [`subterm_lookup`] while the scope is open: a proof opens one, so that a destination
/// simplified again under the same state constraints at a later check is served, and so is a
/// non-ground subterm the term simplifier enters again under an equal path condition and budget
/// (`simplify::simplify_on_stack`). A scope opened inside another shares its record; the
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
    /// The number of reasons, for [`SUBTERM_REFUSALS`].
    const COUNT: usize = 10;

    /// The counter of this refusal at `site`.
    fn counter(self, site: Site) -> Counter {
        match site {
            Site::Destination => match self {
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
            },
            Site::Subterm => match self {
                Self::Console => Counter::SimplifyNormalFormsSubtermRefusedConsole,
                Self::Unspecified => Counter::SimplifyNormalFormsSubtermRefusedUnspecified,
                Self::Coverage => Counter::SimplifyNormalFormsSubtermRefusedCoverage,
                Self::Stop => Counter::SimplifyNormalFormsSubtermRefusedStop,
                Self::Failed => Counter::SimplifyNormalFormsSubtermRefusedFailed,
                Self::Diagnostic => Counter::SimplifyNormalFormsSubtermRefusedDiagnostic,
                Self::PathFact => Counter::SimplifyNormalFormsSubtermRefusedPathFact,
                Self::Unknown => Counter::SimplifyNormalFormsSubtermRefusedUnknown,
                Self::Effect => Counter::SimplifyNormalFormsSubtermRefusedEffect,
                Self::Apart => Counter::SimplifyNormalFormsSubtermRefusedApart,
            },
        }
    }
}

/// Where a caller routes a simplification through the record; the recorded and served ones
/// are counted by site.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Site {
    /// A proof's destination, prepared at an implication check (`Destination::prepare`).
    Destination,
    /// A non-ground subterm the term simplifier enters with no rule condition active
    /// (`simplify::simplify_on_stack`).
    Subterm,
}

impl Site {
    fn recorded(self) -> Counter {
        match self {
            Self::Destination => Counter::SimplifyNormalFormsRecorded,
            Self::Subterm => Counter::SimplifyNormalFormsSubtermRecorded,
        }
    }

    fn served(self) -> Counter {
        match self {
            Self::Destination => Counter::SimplifyNormalFormsServed,
            Self::Subterm => Counter::SimplifyNormalFormsSubtermServed,
        }
    }
}

/// What a caller routes through the record: the node and what it is simplified under, borrowed
/// where they are.
struct Subject<'a> {
    site: Site,
    node: &'a Term,
    known: &'a [Predicate],
    /// `None` where the path condition is the one `known` gives ([`NormalFormKey::path_condition`]).
    path_condition: Option<&'a PathConditionReplacements>,
}

/// A simplification's inputs, borrowed where they are but the renaming, for a lookup and a
/// record.
struct Probe<'a> {
    subject: Subject<'a>,
    /// The renaming applied to the subject ([`NormalFormKey::renaming`]).
    renaming: Box<[(Variable, Term)]>,
    scalars: Scalars,
}

impl<'a> Probe<'a> {
    /// The probe of a simplification now, from the iteration budget `budget`; `None` where no
    /// record is open or no `rule::ApartScope` is (the renaming-apart argument of the module doc
    /// needs one; a proof opens one around its record), and a refusal where the thread holds
    /// open something the key does not, or the simplification runs in an execution
    /// (`execution`), which reads and advances its input and output.
    fn new(
        definition: &BackendDefinition,
        subject: Subject<'a>,
        renaming: &Substitution,
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
        budget: usize,
        execution: bool,
    ) -> Option<Result<Self, Refusal>> {
        #[cfg(test)]
        if NORMAL_FORMS_OFF.get() {
            return None;
        }
        if DEPTH.get() == 0 || !crate::rule::apart_scope_open() {
            return None;
        }
        let mode = crate::evaluation::current();
        if execution || mode == EvaluationMode::Execution || crate::evaluation::console_attached() {
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
            renaming: renaming
                .iter()
                .map(|(original, renamed)| (original.clone(), renamed.clone()))
                .collect(),
            scalars: Scalars {
                definition: std::ptr::from_ref(definition).addr(),
                solver: solver_address(solver),
                max_iterations: options.max_iterations,
                keep_partial: options.budget == super::BudgetPolicy::KeepPartial,
                budget,
                claims_checked: crate::path_facts::checking_claims(),
                mode,
                general_path: crate::condition::on_general_condition_path(),
                stated_ceil_conditions: crate::definedness::ceil_conditions_stated(),
                seed: crate::choice_sampling::seed(),
            },
        }))
    }
}

/// The place of a path condition, for [`InternTable::find`].
fn path_condition_place(path_condition: &PathConditionReplacements) -> (usize, usize) {
    (
        std::ptr::from_ref(path_condition).addr(),
        path_condition.substitution.len(),
    )
}

/// Whether a record is open on this thread ([`scope`]): a caller with work to do before it can
/// route a simplification ([`subterm_lookup`]) asks first.
#[inline]
pub(super) fn open() -> bool {
    DEPTH.get() > 0
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
    // A destination's simplification starts a lineage of its own, with the whole budget, and
    // leaves its caller none to read.
    let mut budget = options.max_iterations;
    let subject = Subject {
        site: Site::Destination,
        node: subject,
        known,
        path_condition: None,
    };
    match consult(
        definition, subject, renaming, options, solver, budget, false,
    ) {
        Consulted::Unrecorded => simplify(),
        Consulted::Served(served) => Ok(Ok(serve(Site::Destination, served, &mut budget, |_| {
            simplify()
        }))),
        Consulted::Missed(probe) => {
            let pending = Pending::start(probe);
            let result = simplify();
            let outcome = match &result {
                Err(_) => Err(Refusal::Stop),
                Ok(Err(_)) => Err(Refusal::Failed),
                Ok(Ok(simplification)) => Ok(simplification),
            };
            pending.finish(outcome, budget);
            result
        }
    }
}

/// What the record holds for a non-ground subterm the term simplifier enters
/// ([`subterm_lookup`]).
pub(super) enum Lookup<'a> {
    /// No record is consulted, or the thread holds open what the key does not (counted): the
    /// subterm is simplified, and nothing is recorded.
    Unrecorded,
    /// The recorded simplification, its reuse replayed: the thread counters it moved are moved
    /// as far, and the iteration budget is left where it left it.
    Served(Box<Simplification>),
    /// Nothing recorded under the key: the subterm is simplified, and the simplification
    /// recorded when it was clean ([`subterm_recorded`]).
    Missed(Box<Pending<'a>>),
}

/// [`simplified_through_record`] for a non-ground subterm the term simplifier enters
/// (`simplify::simplify_on_stack`), simplified as it is (an empty renaming) under `assumptions`,
/// in a lineage whose iteration budget is `remaining`, with no rule condition active against
/// re-entry; `execution` says whether it runs in an execution, which is refused. The budget is
/// part of the key, and a serve leaves in `remaining` what the recorded simplification left.
///
/// In two halves, so that the record's state is off the recursion path: the caller simplifies
/// the subterm itself where this misses, from `remaining`, and hands the result to
/// [`subterm_recorded`]; nothing the record holds is on its frame meanwhile but the boxed
/// [`Pending`]. `simplify` is that simplification, run from scratch only to check a serve
/// (`check-normal-forms`).
#[allow(clippy::too_many_arguments)]
pub(super) fn subterm_lookup<'a>(
    definition: &BackendDefinition,
    subject: &'a Term,
    assumptions: &TermAssumptions<'a>,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    remaining: &mut usize,
    execution: bool,
    simplify: impl FnOnce(&mut usize) -> Stoppable<Result<Simplification, SimplificationError>>,
) -> Lookup<'a> {
    let subject = Subject {
        site: Site::Subterm,
        node: subject,
        known: assumptions.predicates,
        path_condition: Some(assumptions.path_condition),
    };
    let renaming = Substitution::new();
    match consult(
        definition, subject, &renaming, options, solver, *remaining, execution,
    ) {
        Consulted::Unrecorded => Lookup::Unrecorded,
        Consulted::Served(served) => {
            Lookup::Served(Box::new(serve(Site::Subterm, served, remaining, simplify)))
        }
        Consulted::Missed(probe) => Lookup::Missed(Box::new(Pending::start(probe))),
    }
}

/// The second half of [`subterm_lookup`]: `result` is the subterm's simplification, which left
/// the iteration budget `remaining`; it is recorded when it was clean.
pub(super) fn subterm_recorded(
    pending: Box<Pending<'_>>,
    result: &super::SimplifyResult<Simplification>,
    remaining: usize,
) {
    let outcome = match result {
        Err(super::Unwind::Stop(_)) => Err(Refusal::Stop),
        Err(super::Unwind::Fail(_)) => Err(Refusal::Failed),
        Ok(simplification) => Ok(simplification),
    };
    pending.finish(outcome, remaining);
}

/// What a consultation of the record found ([`consult`]).
enum Consulted<'a> {
    /// No record is consulted, or the thread holds open what the key does not (counted).
    Unrecorded,
    /// The simplification recorded under the probe's key, not replayed yet ([`serve`]).
    Served(Served),
    /// Nothing recorded under the probe's key.
    Missed(Probe<'a>),
}

/// The record's lookup of `subject` renamed by `renaming`, simplified from the iteration budget
/// `budget` ([`Probe::new`], [`NormalForms::served`]); a refusal is counted at its site.
fn consult<'a>(
    definition: &BackendDefinition,
    subject: Subject<'a>,
    renaming: &Substitution,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    budget: usize,
    execution: bool,
) -> Consulted<'a> {
    let site = subject.site;
    match Probe::new(
        definition, subject, renaming, options, solver, budget, execution,
    ) {
        None => Consulted::Unrecorded,
        Some(Err(refusal)) => {
            measure::bump(refusal.counter(site));
            Consulted::Unrecorded
        }
        Some(Ok(probe)) => match NormalForms::served(&probe) {
            Some(served) => Consulted::Served(served),
            None => Consulted::Missed(probe),
        },
    }
}

/// The reuse of `served` where a simplification of it from the iteration budget `budget` would
/// run (`simplify`, run from scratch only to check it, `check-normal-forms`): the thread counters
/// it moved are moved as far, and the budget is left where it left it.
fn serve(
    site: Site,
    served: Served,
    budget: &mut usize,
    simplify: impl FnOnce(&mut usize) -> Stoppable<Result<Simplification, SimplificationError>>,
) -> Simplification {
    measure::bump(site.served());
    // Checked where a new simplification would run: before the reuse moves any counter.
    #[cfg(feature = "check-normal-forms")]
    check_served(&served, *budget, simplify);
    #[cfg(not(feature = "check-normal-forms"))]
    let _ = simplify;
    crate::rule::skip_apart_names(served.replayed.apart);
    super::note_undecided_times(served.replayed.undecided);
    *budget = served.replayed.budget;
    served.simplification
}

/// A simplification the record missed, while it runs: its probe, the thread's counters at its
/// start ([`Watch`]), and the count of stack stops open around it.
pub(super) struct Pending<'a> {
    probe: Probe<'a>,
    watch: Watch,
    stack_stops: stop::StackStopCount,
}

impl<'a> Pending<'a> {
    /// Opened where the simplification starts, after the lookup.
    fn start(probe: Probe<'a>) -> Self {
        let watch = Watch::start();
        Self {
            probe,
            watch,
            stack_stops: stop::StackStopCount::start(),
        }
    }

    /// The simplification ended with `outcome` (a stop or a failure already named), leaving the
    /// iteration budget `budget`: recorded when it was clean, and the refusal counted otherwise.
    #[inline(never)]
    fn finish(self, outcome: Result<&Simplification, Refusal>, budget: usize) {
        let Self {
            probe,
            watch,
            stack_stops,
        } = self;
        let stack_stops = stack_stops.finish();
        let site = probe.subject.site;
        match watch.verdict(outcome, stack_stops, budget) {
            Err(refusal) => {
                if watch.counts(site, refusal) {
                    measure::bump(refusal.counter(site));
                }
            }
            Ok((simplification, replayed)) => {
                NormalForms::record(
                    &probe,
                    simplification.clone(),
                    watch.facts_open,
                    watch.collected,
                    replayed,
                );
                measure::bump(site.recorded());
            }
        }
    }
}

/// The thread's counters at the start of a simplification, read again at its end to say
/// whether it was clean ([`Watch::verdict`]).
struct Watch {
    /// [`SUBTERM_REFUSALS`] at the start.
    refusals: [u64; Refusal::COUNT],
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
            refusals: SUBTERM_REFUSALS.get(),
            emitted: crate::diagnostic::emitted(),
            collected: crate::diagnostic::collecting(),
            facts: crate::path_facts::marker(),
            facts_open: crate::path_facts::is_open(),
            unknown: crate::smt::undecided_on_thread(),
            undecided: super::undecided_so_far(),
            apart: crate::rule::apart_counter(),
        }
    }

    /// Whether the refusal of the simplification at `site` that ended for `refusal`
    /// ([`Watch::verdict`]) is counted: a destination's always; a subterm's only where no
    /// subterm simplification inside it was counted for the same reason since the start, since
    /// a reason found after the simplification reaches every simplification that holds the one
    /// that met it (an undecided answer `d` routed levels deep is counted once, not `d + 1`
    /// times). An enclosing simplification that met the same reason on its own is not counted
    /// either: the counters count the routed simplifications that met a reason first, not every
    /// one refused for it.
    fn counts(&self, site: Site, refusal: Refusal) -> bool {
        if site == Site::Destination {
            return true;
        }
        let index = refusal as usize;
        let mut counted = SUBTERM_REFUSALS.get();
        if counted[index] != self.refusals[index] {
            return false;
        }
        counted[index] += 1;
        SUBTERM_REFUSALS.set(counted);
        true
    }

    /// The names the renamings apart minted since the start; `None` where the counter went
    /// back, which only the opening of an outermost `rule::ApartScope` since the start does
    /// (it restarts the counter at 0; [`Probe::new`] consults the record only inside one).
    fn apart(&self) -> Option<u64> {
        crate::rule::apart_counter().checked_sub(self.apart)
    }

    /// The simplification that ended with `result`, having dismissed `stack_stops` stops for
    /// lack of native stack and left the iteration budget `budget`, with the counters a reuse of
    /// it moves, when it was clean; why it is not recorded otherwise, the first reason found.
    fn verdict<'r>(
        &self,
        outcome: Result<&'r Simplification, Refusal>,
        stack_stops: usize,
        budget: usize,
    ) -> Result<(&'r Simplification, Replayed), Refusal> {
        let simplification = match outcome {
            Err(Refusal::Stop) => return Err(Refusal::Stop),
            _ if stack_stops > 0 => return Err(Refusal::Stop),
            Err(refusal) => return Err(refusal),
            Ok(simplification) => simplification,
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
        Ok((
            simplification,
            Replayed {
                apart,
                undecided,
                budget,
            },
        ))
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

/// The bytes a term node takes in place, by the estimate of [`NormalForms::count_new_nodes`],
/// with its address's place in [`NormalForms::counted`].
const NODE_BYTES: usize = std::mem::size_of::<crate::term::TermKind>()
    + std::mem::size_of::<crate::term::TermAttributes>()
    + 4 * std::mem::size_of::<usize>();

impl NormalForms {
    /// The simplification recorded under `probe`'s key, with the counters its reuse moves;
    /// `None` when there is none, or where a reuse would not replay what a new simplification
    /// notes or emits: a path-fact record is open that was not open when it was recorded, or a
    /// collector is that was not.
    fn served(probe: &Probe<'_>) -> Option<Served> {
        NORMAL_FORMS.with_borrow_mut(|record| {
            let record = record.as_mut()?;
            // A list or a path condition no key names is in no key.
            let known = probe.subject.known;
            let known = Arc::clone(record.knowns.find(known, slice_place(known))?);
            let path_condition = match probe.subject.path_condition {
                None => None,
                Some(path_condition) => Some(Interned(Arc::clone(
                    record
                        .path_conditions
                        .find(path_condition, path_condition_place(path_condition))?,
                ))),
            };
            let key = NormalFormKey {
                subject: probe.subject.node.clone(),
                renaming: probe.renaming.clone(),
                known: Interned(known),
                path_condition,
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
        let renaming = probe.renaming.clone();
        let own_bytes = std::mem::size_of::<(NormalFormKey, Recorded)>()
            + std::mem::size_of_val(&*renaming)
            + simplification.conjoined().len() * std::mem::size_of::<Predicate>()
            + simplification.applied_rules.len() * std::mem::size_of::<String>();
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
                record.path_conditions.clear();
                record.counted.clear();
                record.retained = 0;
                measure::bump(Counter::SimplifyNormalFormsCleared);
            }
            let known = record.intern_known(probe.subject.known);
            let path_condition = probe
                .subject
                .path_condition
                .map(|path_condition| record.intern_path_condition(path_condition));
            let bytes = own_bytes
                + record.count_new_nodes(probe.subject.node, &simplification) * NODE_BYTES;
            let key = NormalFormKey {
                subject: probe.subject.node.clone(),
                renaming,
                known,
                path_condition,
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

    /// The one copy of `path_condition` the record holds, made now if there is none.
    fn intern_path_condition(
        &mut self,
        path_condition: &PathConditionReplacements,
    ) -> Interned<PathConditionReplacements> {
        let place = path_condition_place(path_condition);
        if let Some(held) = self.path_conditions.find(path_condition, place) {
            return Interned(Arc::clone(held));
        }
        self.retained += std::mem::size_of::<PathConditionReplacements>()
            + path_condition.substitution.len() * std::mem::size_of::<(Variable, Term)>()
            + path_condition.replacements.len() * std::mem::size_of::<(Term, Term)>()
            + 2 * std::mem::size_of::<Arc<PathConditionReplacements>>();
        Interned(
            self.path_conditions
                .insert(place, Arc::new(path_condition.clone())),
        )
    }

    /// The number of distinct term nodes of `subject` and of `simplification`
    /// ([`visit_result_terms`]) that the record has not counted yet, counted now
    /// ([`NormalForms::counted`]): an entry keeps them alive until the record clears. A node
    /// counted once is not walked again, nor are the nodes below it, so the walks of all entries
    /// together visit each node held once, however the entries nest (a subterm's entry inside
    /// the entry of the term that holds it). A node freed while its address stays counted (an
    /// entry replaced by a new record of its key) leaves the estimate low by the nodes a later
    /// allocation at that address holds.
    fn count_new_nodes(&mut self, subject: &Term, simplification: &Simplification) -> usize {
        let counted = &mut self.counted;
        let mut new = 0;
        let mut walk = |root: &Term| {
            let mut pending = vec![root];
            while let Some(term) = pending.pop() {
                if counted.insert(term.node_address()) {
                    new += 1;
                    pending.extend(crate::term::immediate_children(term.kind()));
                }
            }
        };
        walk(subject);
        visit_result_terms(simplification, &mut walk);
        new
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
    budget: usize,
    simplify: impl FnOnce(&mut usize) -> Stoppable<Result<Simplification, SimplificationError>>,
) {
    let collecting = crate::diagnostic::collecting();
    let facts_open = crate::path_facts::is_open();
    let recompute = || {
        let emitted = crate::diagnostic::emitted();
        let facts = crate::path_facts::marker();
        let unknown = crate::smt::undecided_on_thread();
        let undecided = super::undecided_so_far();
        let apart = crate::rule::apart_counter();
        let mut budget = budget;
        let (result, stack_stops) = stop::counting_stack_stops(|| simplify(&mut budget));
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
                budget,
            });
        (
            outcome,
            crate::diagnostic::emitted() != emitted,
            crate::path_facts::noted_since(facts),
            replayed,
        )
    };
    // The subterm refusals the recompute counts are none of the run's either.
    let refusals = SUBTERM_REFUSALS.get();
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
    SUBTERM_REFUSALS.set(refusals);
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use k_rust_kore::{
        kore::parser::{parse_definition, parse_pattern},
        measure::{self, Counter},
    };

    use super::*;
    use crate::{
        simplify::{self, PathConditionReplacements, TermAssumptions},
        smt::{Satisfiability, SmtError, Validity},
    };

    /// `f(X) = X` only under `X >Int 0`, which the solver is asked about; `pair` is a
    /// constructor that holds two of them.
    fn definition() -> BackendDefinition {
        let source = r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortP{} []
                symbol f{}(SortInt{}) : SortInt{} [function{}()]
                symbol pair{}(SortInt{}, SortInt{}) : SortP{} [constructor{}()]
                hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
                axiom{R} \implies{R}(
                    \and{R}(
                        \equals{SortBool{}, R}(
                            gtInt{}(X0:SortInt{}, \dv{SortInt{}}("0")),
                            \dv{SortBool{}}("true")
                        ),
                        \and{R}(\in{SortInt{}, R}(X0:SortInt{}, Z:SortInt{}), \top{R}())
                    ),
                    \equals{SortInt{}, R}(
                        f{}(X0:SortInt{}),
                        \and{SortInt{}}(Z:SortInt{}, \top{SortInt{}}())
                    )
                ) [label{}("f-guarded")]
            endmodule []"#;
        let syntax = parse_definition(source).expect("the definition parses");
        BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(source).expect("the term parses"), &[])
            .expect("the term internalizes")
    }

    /// `W >Int bound`, of a variable `f`'s condition on `Y` does not mention.
    fn above(definition: &BackendDefinition, bound: &str) -> Predicate {
        Predicate::Term(term(
            definition,
            &format!(r#"gtInt{{}}(W:SortInt{{}}, \dv{{SortInt{{}}}}("{bound}"))"#),
        ))
    }

    /// Every satisfiability check is `Sat` and every validity check `Contingent`, so that `f`'s
    /// condition is left undecided on decided answers (as `#bufStrict`'s on KEVM).
    struct Contingent;

    impl SmtSolver for Contingent {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            Ok(Ok(Satisfiability::Sat))
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(Ok(Validity::Contingent))
        }
    }

    /// What one simplification of a subterm did.
    #[derive(Debug)]
    struct Run {
        simplification: Simplification,
        /// The iteration budget it left.
        remaining: usize,
        /// Equation attempts, `f-guarded`'s, each deciding its condition (the check of a served
        /// simplification counts none).
        attempts: u64,
        undecided: u64,
        recorded: u64,
        served: u64,
        /// Subterm refusals for a console, and for an undecided answer.
        console: u64,
        unknown: u64,
        /// The destination's refusals for the same two reasons, which a subterm does not count.
        destination_refusals: [u64; 2],
    }

    /// Where a subterm is simplified, besides its term: the known predicates, the rule
    /// conditions active against re-entry, the budget, and whether it runs in an execution.
    struct Given<'a> {
        known: &'a [Predicate],
        /// The predicates the path condition is built from, where it is not built from `known`
        /// (as for a conjunct of a conjunction, simplified under the others' equalities).
        path_condition: Option<&'a [Predicate]>,
        active: BTreeSet<(String, Term)>,
        remaining: usize,
        execution: bool,
    }

    impl<'a> Given<'a> {
        fn under(known: &'a [Predicate]) -> Self {
            Self {
                known,
                path_condition: None,
                active: BTreeSet::new(),
                remaining: SimplificationOptions::default().max_iterations,
                execution: false,
            }
        }
    }

    /// Simplify `subject` as the term simplifier enters a subterm (`simplify_with_budget`), with
    /// the condition memo set aside, so that every condition met is decided.
    fn simplify_subterm(
        definition: &BackendDefinition,
        subject: &Term,
        given: &Given<'_>,
        solver: &dyn SmtSolver,
    ) -> Run {
        let path_condition =
            PathConditionReplacements::new(given.path_condition.unwrap_or(given.known));
        let assumptions = TermAssumptions {
            predicates: given.known,
            path_condition: &path_condition,
        };
        let _domain = crate::term::domain::DomainScope::enter(definition);
        let _hook_values = crate::deferred::HookValueScope::enter(definition);
        let mut io = given
            .execution
            .then(|| crate::transition::ExecutionIoState::default().begin_evaluation());
        let before = measure::snapshot();
        let undecided = simplify::undecided_count();
        let mut remaining = given.remaining;
        let simplification = simplify::without_condition_memo(|| {
            simplify::simplify_with_budget(
                definition,
                subject,
                &assumptions,
                SimplificationOptions::default(),
                &mut remaining,
                &given.active,
                solver,
                io.as_mut(),
            )
        })
        .expect("the subterm simplifies");
        let delta = measure::snapshot().delta(&before);
        Run {
            simplification,
            remaining,
            attempts: delta.get(Counter::SimplifyEquationAttempts),
            undecided: simplify::undecided_count() - undecided,
            recorded: delta.get(Counter::SimplifyNormalFormsSubtermRecorded),
            served: delta.get(Counter::SimplifyNormalFormsSubtermServed),
            console: delta.get(Counter::SimplifyNormalFormsSubtermRefusedConsole),
            unknown: delta.get(Counter::SimplifyNormalFormsSubtermRefusedUnknown),
            destination_refusals: [
                Counter::SimplifyNormalFormsRefusedConsole,
                Counter::SimplifyNormalFormsRefusedUnknown,
            ]
            .map(|counter| delta.get(counter)),
        }
    }

    /// Run `action` as a proof runs its steps: inside a renaming-apart scope and the record's.
    fn in_a_proof<T>(action: impl FnOnce() -> T) -> T {
        let _apart = crate::rule::ApartScope::enter();
        let _record = scope();
        action()
    }

    /// GAP K17 part b: a non-ground subterm whose equation's `requires` stays undecided on
    /// decided answers is decided once per key: entered again under an equal path condition and
    /// budget it is served, decides nothing, counts its undecided condition again and leaves the
    /// budget a new simplification leaves; under a stronger path condition, or from a smaller
    /// budget, it is simplified again and recorded under its own key. Every result is the one a
    /// simplification with nothing recorded gives (and `check-normal-forms` compares each serve
    /// with a new simplification).
    #[test]
    fn a_subterm_left_undecided_is_decided_once_per_path_condition_and_budget() {
        let definition = definition();
        let solver = Contingent;
        let subject = term(&definition, "f{}(Y:SortInt{})");
        let weaker = [above(&definition, "0")];
        let stronger = [above(&definition, "0"), above(&definition, "5")];
        let runs = || {
            in_a_proof(|| {
                let under = |given: &Given<'_>| {
                    (
                        simplify_subterm(&definition, &subject, given, &solver),
                        simplify_subterm(&definition, &subject, given, &solver),
                    )
                };
                let smaller = Given {
                    remaining: 7,
                    ..Given::under(&weaker)
                };
                [
                    under(&Given::under(&weaker)),
                    under(&Given::under(&stronger)),
                    under(&smaller),
                ]
            })
        };
        let recorded = runs();
        let fresh = without_normal_forms(runs);
        for ((first, again), (fresh_first, fresh_again)) in recorded.iter().zip(&fresh) {
            assert!(first.attempts > 0 && first.undecided > 0, "{first:#?}");
            assert_eq!((first.recorded, first.served), (1, 0), "{first:#?}");
            // Undecided: `f` was not applied.
            assert!(matches!(
                first.simplification.term.kind(),
                crate::term::TermKind::Application { .. }
            ));
            assert_eq!(
                (again.recorded, again.served, again.attempts),
                (0, 1, 0),
                "{again:#?}"
            );
            for run in [again, fresh_first, fresh_again] {
                assert_eq!(run.simplification, first.simplification);
                assert_eq!(
                    (run.undecided, run.remaining),
                    (first.undecided, first.remaining)
                );
            }
            for run in [fresh_first, fresh_again] {
                assert_eq!((run.recorded, run.served), (0, 0));
                assert_eq!(run.attempts, first.attempts);
            }
        }
    }

    /// GAP K17 part b: a subterm's key holds the path condition it is simplified under, which is
    /// not always the one its known predicates give: `f(Y)` under the known `W >Int 0` and a
    /// path condition that replaces `Y` by `3` is `f(3)`, which is `3`, while under the path
    /// condition of the known predicates alone it stays undecided. Neither is served the
    /// other's simplification.
    #[test]
    fn a_subterm_is_served_only_under_the_path_condition_it_was_recorded_under() {
        let definition = definition();
        let subject = term(&definition, "f{}(Y:SortInt{})");
        let known = [above(&definition, "0")];
        let replacing = [Predicate::Equals(
            term(&definition, "Y:SortInt{}"),
            term(&definition, r#"\dv{SortInt{}}("3")"#),
        )];
        let three = term(&definition, r#"\dv{SortInt{}}("3")"#);
        in_a_proof(|| {
            let plain = Given::under(&known);
            let replaced = Given {
                path_condition: Some(&replacing),
                ..Given::under(&known)
            };
            let first = simplify_subterm(&definition, &subject, &plain, &Contingent);
            assert!(first.undecided > 0, "{first:#?}");
            let other = simplify_subterm(&definition, &subject, &replaced, &Contingent);
            assert_eq!(other.simplification.term, three, "{other:#?}");
            assert_eq!(other.served, 0, "{other:#?}");
            let again = simplify_subterm(&definition, &subject, &plain, &Contingent);
            assert_eq!((again.served, again.attempts), (1, 0), "{again:#?}");
            assert_eq!(again.simplification, first.simplification);
            let other_again = simplify_subterm(&definition, &subject, &replaced, &Contingent);
            assert_eq!(other_again.simplification, other.simplification);
        });
    }

    /// GAP K17 part b: under a rule condition active against re-entry (inside an equation
    /// condition's decision), the term simplifier does not route a subterm through the record,
    /// whose key does not hold the active conditions: it is neither recorded nor served, and is
    /// decided each time. With no condition active the same subterm is served.
    #[test]
    fn a_subterm_under_an_active_rule_condition_is_neither_recorded_nor_served() {
        let definition = definition();
        let solver = Contingent;
        let subject = term(&definition, "f{}(Y:SortInt{})");
        let known = [above(&definition, "0")];
        in_a_proof(|| {
            let active = Given {
                active: BTreeSet::from([("another-rule".to_owned(), subject.clone())]),
                ..Given::under(&known)
            };
            for _ in 0..2 {
                let run = simplify_subterm(&definition, &subject, &active, &solver);
                assert!(run.attempts > 0, "{run:#?}");
                assert_eq!((run.recorded, run.served), (0, 0), "{run:#?}");
            }
            let inactive = Given::under(&known);
            let first = simplify_subterm(&definition, &subject, &inactive, &solver);
            let again = simplify_subterm(&definition, &subject, &inactive, &solver);
            assert_eq!((first.recorded, first.served), (1, 0), "{first:#?}");
            assert_eq!(
                (again.recorded, again.served, again.attempts),
                (0, 1, 0),
                "{again:#?}"
            );
        });
    }

    /// GAP K17 part b: a subterm simplified in an execution (with the execution's input and
    /// output, which the simplification reads and advances) is refused before the lookup,
    /// counted as `console`, and never served, though the same subterm outside it was recorded.
    #[test]
    fn a_subterm_in_an_execution_is_never_served() {
        let definition = definition();
        let solver = Contingent;
        let subject = term(&definition, "pair{}(f{}(Y:SortInt{}), f{}(Y:SortInt{}))");
        let known = [above(&definition, "0")];
        in_a_proof(|| {
            let outside = simplify_subterm(&definition, &subject, &Given::under(&known), &solver);
            // `pair(..)` and each `f(Y)`, two nodes.
            assert_eq!((outside.recorded, outside.served), (3, 0), "{outside:#?}");
            let execution = Given {
                execution: true,
                ..Given::under(&known)
            };
            for _ in 0..2 {
                let run = simplify_subterm(&definition, &subject, &execution, &solver);
                assert!(run.attempts > 0, "{run:#?}");
                assert_eq!((run.recorded, run.served), (0, 0), "{run:#?}");
                // `pair(..)` and each `f(Y)`.
                assert_eq!(run.console, 3, "{run:#?}");
                assert_eq!(run.simplification, outside.simplification);
            }
        });
    }

    /// Every satisfiability check is `Sat` and every validity check `Unknown` (as a timeout).
    struct Unknowing;

    impl SmtSolver for Unknowing {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            Ok(Ok(Satisfiability::Sat))
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(Ok(Validity::Unknown("timeout".to_owned())))
        }
    }

    /// GAP K17 part b, the fix round: a subterm refusal is counted at the subterm site, once per
    /// routed simplification that met its reason, not again at every routed simplification that
    /// holds it. In `pair(f(Y), f(Z))` each `f(..)` receives an undecided answer and is refused,
    /// counted once each; `pair(..)` is refused for the same answers and not counted again (3
    /// with every level counting); the destination's counters count none of them.
    #[test]
    fn a_subterm_refusal_is_counted_once_at_the_simplification_that_met_it() {
        let definition = definition();
        let unknowing = Unknowing;
        let solver = crate::smt::UndecidedCounting::new(&unknowing);
        let subject = term(&definition, "pair{}(f{}(Y:SortInt{}), f{}(Z:SortInt{}))");
        let known = [above(&definition, "0")];
        in_a_proof(|| {
            for _ in 0..2 {
                let run = simplify_subterm(&definition, &subject, &Given::under(&known), &solver);
                assert_eq!((run.recorded, run.served), (0, 0), "{run:#?}");
                assert_eq!(run.unknown, 2, "{run:#?}");
                assert_eq!(run.destination_refusals, [0, 0], "{run:#?}");
            }
        });
    }

    /// `h(X) = \bottom` for every `X`, and `t`, a `total` symbol whose equation makes the
    /// definition one that declares a claim (`BackendDefinition::declares_claims`).
    fn bottom_definition() -> BackendDefinition {
        let source = r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol h{}(SortInt{}) : SortInt{} [function{}()]
                symbol t{}(SortInt{}) : SortInt{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, Z:SortInt{}), \top{R}())),
                    \equals{SortInt{}, R}(h{}(X0:SortInt{}), \and{SortInt{}}(\bottom{SortInt{}}(), \top{SortInt{}}()))
                ) [label{}("h-bottom")]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, Z:SortInt{}), \top{R}())),
                    \equals{SortInt{}, R}(t{}(X0:SortInt{}), \and{SortInt{}}(Z:SortInt{}, \top{SortInt{}}()))
                ) [label{}("t-id")]
            endmodule []"#;
        let syntax = parse_definition(source).expect("the definition parses");
        BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
    }

    /// GAP K17 part b, the fix round: whether contradicted claims are checked is in the key. A
    /// lineage reports where it found `\bottom` (`Simplification::bottom`) only where claims
    /// are checked (a path-fact record is open); `h(Y)` recorded inside one is not served where
    /// none is open, since a new simplification there reports nothing (with the key part left
    /// out, `check-normal-forms` finds the served simplification differs from a new one).
    #[test]
    fn a_subterm_recorded_where_claims_are_checked_is_not_served_where_they_are_not() {
        let definition = bottom_definition();
        assert!(definition.declares_claims());
        let solver = Contingent;
        let subject = term(&definition, "h{}(Y:SortInt{})");
        let known = [];
        let given = Given::under(&known);
        let runs = || {
            in_a_proof(|| {
                let (checked, _facts) = crate::path_facts::collect(|| {
                    simplify_subterm(&definition, &subject, &given, &solver)
                });
                let unchecked = simplify_subterm(&definition, &subject, &given, &solver);
                let again = simplify_subterm(&definition, &subject, &given, &solver);
                (checked, unchecked, again)
            })
        };
        let (checked, unchecked, again) = runs();
        assert!(checked.simplification.bottom.is_some(), "{checked:#?}");
        assert!(unchecked.simplification.bottom.is_none(), "{unchecked:#?}");
        assert_eq!((checked.recorded, checked.served), (1, 0), "{checked:#?}");
        assert_eq!(
            (unchecked.recorded, unchecked.served),
            (1, 0),
            "{unchecked:#?}"
        );
        assert_eq!((again.recorded, again.served), (0, 1), "{again:#?}");
        let (fresh_checked, fresh_unchecked, _) = without_normal_forms(runs);
        assert_eq!(checked.simplification, fresh_checked.simplification);
        assert_eq!(unchecked.simplification, fresh_unchecked.simplification);
    }
}
