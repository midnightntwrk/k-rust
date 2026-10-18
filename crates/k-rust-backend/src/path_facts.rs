//! Path facts: facts about the model-dependence of a run that its leaves must carry whatever
//! became of the work that found them, collected on the thread that runs it, and the run-level
//! record of what the run met that undone work never rolls back.
//!
//! The kinds of fact:
//!
//! - an evaluation that read a value the definition leaves open ([`PathFact::ChosenValue`],
//!   `builtin::chosen_value`): a leaf whose path read one is one model's answer;
//! - an evaluation that found a claim of the definition contradicted by its own equations
//!   ([`PathFact::ContradictedClaim`]): a `total` claim one of the symbol's equations refutes,
//!   or a rule's `preserves-definedness` claim its result term's normalization refutes; a leaf
//!   whose path's decisions rest on one rests on an input where the definition has no model
//!   with the claim;
//! - a `Bytes` result the memory allowance refused ([`PathFact::AllowanceRefusal`]) and an
//!   application left unevaluated as an unsupported hook ([`PathFact::UnsupportedHook`]): facts
//!   of the run only ([`PathFact::on_paths`]), which reach the run record and no path.
//!
//! Such a fact is a fact about the decisions a path rests on, not about the result the work
//! contributed to, so it is never withdrawn with that work. The diagnostic channel
//! (`crate::diagnostic`) drops the reports of work on no path (an attempt that did not apply, an
//! undone `Unspecified` attempt, a speculative attempt, a superseded or retracted one); this
//! collector has no drop, rewind, discard or retraction at all. Every rule below is stated per
//! fact, so a further kind of fact is a further variant and needs no new rule.
//!
//! - A phase of a run collects what it noted ([`collect`]); closing a collection adds what it
//!   holds to the enclosing collection. A fact noted inside a candidate-owned scope ([`owned`])
//!   is kept apart from the enclosing phase's own facts (`Facts::owned`), so that the phase can
//!   attribute it to the candidate alone. A fact of the run only reaches no collection.
//! - A structure that lets a later step skip an evaluation stores the facts its evaluation noted
//!   ([`marker`], [`since`]) and notes them again where it is served ([`replay`]).
//! - An evaluation whose value only decides a definedness that is the same in every model runs
//!   with the notes of chosen values suspended ([`suspend`]): they reach no collection and no
//!   run record, and a memo filled there still learns them, so it replays them where they count.
//!   Every other kind is noted there too, since it can steer the definedness the evaluation
//!   decides: a definedness-only fold reads an allowance refusal as "not defined without a
//!   value" where a larger allowance gives a value (`deferred::defined_without_value`).
//! - A contradicted claim names the rewrite rule whose attempt (its match, its conditions, its
//!   right-hand side) or whose successor's normalization observed it ([`observed_by`]), so that
//!   the same contradiction observed by two rules is two records.
//! - The run-level record ([`run`]) holds every distinct fact the run noted outside a
//!   suspension, in first-observed order, whatever became of the work and the paths that met it.
//!   A result lists the definition's load record before it ([`RunRecord::of`]), each entry
//!   tagged with who observed it ([`ObservedIn`]); a leaf carries the run's own facts only.
//!
//! With nothing open a note reads one thread-local flag and returns.

use std::{
    cell::{Cell, RefCell},
    cmp::Ordering,
    collections::BTreeSet,
    hash::{Hash, Hasher},
    sync::Arc,
};

use crate::{
    builtin::{ChosenValue, UnsupportedHookReason},
    diagnostic::{self, BackendDiagnostic},
    rule::{RewriteRule, RuleOrigin, RuleRhs},
    simplify::ContradictedTotal,
    term::Term,
};

/// A fact a path's leaves carry whatever became of the work that found it, or, for the kinds
/// that are facts of the run only ([`Self::on_paths`]), that the run record holds whatever
/// became of that work.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum PathFact {
    /// An evaluation took one of several values the definition admits (`builtin::chosen_value`).
    ChosenValue(ChosenValue),
    /// An evaluation found a claim of the definition contradicted by the definition's own
    /// equations ([`ContradictedClaim`]).
    ContradictedClaim(Box<ContradictedClaim>),
    /// A `Bytes` hook bounded by the memory allowance refused to build a result
    /// (`crate::allowance`): under an allowance of more bytes the application has a value.
    AllowanceRefusal(UnevaluatedHook),
    /// An application was left unevaluated as an unsupported hook, the report a
    /// `BackendDiagnostic::UnsupportedHookUnevaluated` or an unsupported-hook failure makes.
    UnsupportedHook(UnevaluatedHook),
}

impl PathFact {
    /// Whether the fact goes to the paths whose decisions rest on it, besides the run record.
    /// A refusal or an unsupported hook is a fact of the run only: its diagnostic is the path
    /// report, and the run record keeps what undone work dropped of it.
    pub(crate) fn on_paths(&self) -> bool {
        match self {
            Self::ChosenValue(_) | Self::ContradictedClaim(_) => true,
            Self::AllowanceRefusal(_) | Self::UnsupportedHook(_) => false,
        }
    }

    /// Whether a [`suspend`]ed evaluation leaves the fact unnoted: only a chosen value, whose
    /// definedness is the same in every model.
    fn suspends(&self) -> bool {
        matches!(self, Self::ChosenValue(_))
    }

    /// The fact as the load of a definition observed it ([`ObservedIn::Load`]).
    pub(crate) fn observed_at_load(self) -> Self {
        match self {
            Self::ChosenValue(chosen) => Self::ChosenValue(chosen),
            Self::ContradictedClaim(mut claim) => {
                claim.observed_in = ObservedIn::Load;
                Self::ContradictedClaim(claim)
            }
            Self::AllowanceRefusal(hook) => Self::AllowanceRefusal(UnevaluatedHook {
                observed_in: ObservedIn::Load,
                ..hook
            }),
            Self::UnsupportedHook(hook) => Self::UnsupportedHook(UnevaluatedHook {
                observed_in: ObservedIn::Load,
                ..hook
            }),
        }
    }

    /// The fact as a diagnostic of the paths it is attributed to, `None` for a fact of the run
    /// only.
    pub(crate) fn diagnostic(&self) -> Option<BackendDiagnostic> {
        match self {
            Self::ChosenValue(chosen) => Some(BackendDiagnostic::ImplementationChosenValue {
                hook: chosen.hook.to_string(),
                class: chosen.class,
            }),
            Self::ContradictedClaim(claim) => {
                Some(BackendDiagnostic::ContradictedClaim(claim.clone()))
            }
            Self::AllowanceRefusal(_) | Self::UnsupportedHook(_) => None,
        }
    }

    /// The fact a diagnostic of [`Self::diagnostic`] states, `None` for any other diagnostic.
    pub(crate) fn of_diagnostic(diagnostic: &BackendDiagnostic) -> Option<Self> {
        match diagnostic {
            BackendDiagnostic::ImplementationChosenValue { hook, class } => Some(
                Self::ChosenValue(ChosenValue::new(Arc::from(hook.as_str()), *class)),
            ),
            BackendDiagnostic::ContradictedClaim(claim) => {
                Some(Self::ContradictedClaim(claim.clone()))
            }
            _ => None,
        }
    }

    /// The chosen value, when the fact is one.
    pub(crate) fn chosen_value(&self) -> Option<&ChosenValue> {
        match self {
            Self::ChosenValue(chosen) => Some(chosen),
            _ => None,
        }
    }
}

/// A claim of the definition that an evaluation found contradicted by the definition's own
/// equations, and where: the rewrite rule whose attempt or successor observed it.
///
/// A record is a fact about the definition at the contradicted application (for a
/// `preserves-definedness` claim, the rule's result term). When it is
/// [`ground`](Self::ground), the application is variable-free (and, for a
/// `preserves-definedness` claim, the step's premises were decided to hold), so the definition
/// has no model with the claim at that input. A non-ground record comes from a state whose
/// constraints may be unsatisfiable without being refuted, or from a step whose `requires` was
/// carried rather than decided, and refutes nothing.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct ContradictedClaim {
    pub claim: Claim,
    /// The rewrite rule whose attempt (its match, its conditions, its right-hand side) or whose
    /// produced successor's normalization observed the contradiction; `None` when no rule's
    /// work did (the normalization of an initial state, or work outside a run's steps).
    pub rule: Option<ObservingRule>,
    /// Whether the contradicted application is ground (variable-free). For a
    /// `preserves-definedness` claim: the result term is variable-free and every constraint of
    /// the successor (the pre-step state's and what the step added: a carried `requires`,
    /// `ensures` or obligation) simplified to `\top`, so the step's premises hold on the
    /// instance alone.
    pub ground: bool,
    /// Whether the definition's load or the run that reports it observed the contradiction. A
    /// leaf's records are the run's; the load's are on the result's lists only.
    pub observed_in: ObservedIn,
}

/// Who observed a run-level record: the load of the definition, whose analyses' verdicts every
/// run of it reads, or the run that reports it.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ObservedIn {
    /// The load's analyses (`BackendDefinition::internalize`): a fact about the definition, the
    /// same for every run and every leaf.
    Load,
    /// The run that reports it.
    #[default]
    Run,
}

/// The kinds of claim a [`ContradictedClaim`] can name.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Claim {
    /// A symbol declared `total` (or `functional`) whose own equation reduced an application to
    /// defined arguments to bottom.
    Total(ContradictedTotal),
    /// A rewrite rule declared `preserves-definedness` whose result term, as a step that applied
    /// it built it, the normalization found `\bottom`.
    PreservesDefinedness(ContradictedPreservation),
}

/// A rewrite rule's `preserves-definedness` claim refuted at one instance: the attribute claims
/// that the result term is defined wherever the left-hand side and the `requires` hold, so a
/// step that applied the rule (its match and its `requires` held on a defined state) and whose
/// result term the normalization found `\bottom`, by any route (an undefined builtin
/// application, an equation whose own result is `\bottom`), shows the claim false there, when
/// the premises were decided rather than carried ([`ContradictedClaim::ground`]). The
/// definedness of a disjunctive right-hand side is the disjunction of its alternatives', so
/// such a rule is named only when every alternative's result is `\bottom`. An `ensures` and a
/// condition the step carries are no part of the result term, so their failures refute nothing
/// of it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContradictedPreservation {
    /// The rule's `UNIQUE_ID`.
    pub rule_id: String,
    pub label: Option<String>,
    /// Where the rule is written (its first origin), when the KORE carries it.
    pub origin: Option<RuleOrigin>,
    /// The rule's result term as the step built it (for a disjunctive right-hand side, its first
    /// alternative).
    pub instance: Term,
    /// The undefined term the normalization of `instance` reached: a subterm of it, or of a
    /// callee's equation result; where the normalization found `\bottom` otherwise.
    pub undefined_term: Term,
}

/// A rewrite rule by the parts a report names it by, and whether it claims that its result term
/// is defined (`claims_defined_result`), the claim a normalization of its result can refute
/// ([`note_contradicted_preservation`]).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ObservingRule {
    /// The rule's `UNIQUE_ID`.
    pub unique_id: String,
    pub label: Option<String>,
    /// Where the rule is written (its first origin), when the KORE carries it.
    pub origin: Option<RuleOrigin>,
    /// Whether one successor's normalization can refute the rule's `preserves-definedness`
    /// ([`claims_defined_result`]), a function of the rule.
    pub(crate) claims_defined_result: bool,
}

/// Whether `rule` is declared `preserves-definedness` (the author's claim, as written,
/// `RuleAttributes::preserves_definedness`, not the load's `definedness_discharged`) with one
/// right-hand side term, so that one successor's result found `\bottom` refutes the claim. The
/// definedness of a disjunctive right-hand side is the disjunction of its alternatives'
/// definedness, so its claim is refuted only when every alternative is found `\bottom`, which
/// the step that builds them all decides (`rewrite::apply`).
pub(crate) fn claims_defined_result(rule: &RewriteRule) -> bool {
    rule.attributes.preserves_definedness && matches!(rule.rhs, RuleRhs::Term(_))
}

impl ObservingRule {
    pub(crate) fn of(rule: &RewriteRule) -> Self {
        Self {
            unique_id: rule.attributes.unique_id.clone(),
            label: rule.attributes.label.clone(),
            origin: rule.attributes.origins.first().cloned(),
            claims_defined_result: claims_defined_result(rule),
        }
    }
}

/// What tells two claims apart: for a `total` claim everything but the equation's attributes,
/// which its id and origin fix; for a `preserves-definedness` claim every field.
#[derive(Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ClaimPart<'a> {
    Total(
        &'a Term,
        &'a str,
        Option<&'a str>,
        Option<&'a RuleOrigin>,
        &'a Term,
    ),
    PreservesDefinedness(
        &'a str,
        Option<&'a str>,
        Option<&'a RuleOrigin>,
        &'a Term,
        &'a Term,
    ),
}

/// What tells two records apart: the claim, the observing rule, groundness and who observed it.
type ClaimKey<'a> = (ClaimPart<'a>, &'a Option<ObservingRule>, bool, ObservedIn);

impl ContradictedClaim {
    fn key(&self) -> ClaimKey<'_> {
        let claim = match &self.claim {
            Claim::Total(total) => ClaimPart::Total(
                &total.application,
                &total.rule_id,
                total.label.as_deref(),
                total.origin.as_ref(),
                &total.undefined_term,
            ),
            Claim::PreservesDefinedness(preservation) => ClaimPart::PreservesDefinedness(
                &preservation.rule_id,
                preservation.label.as_deref(),
                preservation.origin.as_ref(),
                &preservation.instance,
                &preservation.undefined_term,
            ),
        };
        (claim, &self.rule, self.ground, self.observed_in)
    }

    /// The contradicted `total` application, when the claim is one.
    pub fn total(&self) -> Option<&ContradictedTotal> {
        match &self.claim {
            Claim::Total(total) => Some(total),
            Claim::PreservesDefinedness(_) => None,
        }
    }

    /// The contradicted `preserves-definedness` claim, when the claim is one.
    pub fn preservation(&self) -> Option<&ContradictedPreservation> {
        match &self.claim {
            Claim::PreservesDefinedness(preservation) => Some(preservation),
            Claim::Total(_) => None,
        }
    }
}

impl PartialEq for ContradictedClaim {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl Eq for ContradictedClaim {}

impl PartialOrd for ContradictedClaim {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ContradictedClaim {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key().cmp(&other.key())
    }
}

impl Hash for ContradictedClaim {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key().hash(state);
    }
}

/// A hook application left unevaluated, by its hook and why, and who met it.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct UnevaluatedHook {
    pub hook: String,
    pub reason: UnsupportedHookReason,
    /// Whether the definition's load or the run that reports it met the application.
    pub observed_in: ObservedIn,
}

/// The run-level lists a result reports of the facts of the run that are not chosen values:
/// each distinct one once, in first-observed order, with an unsupported hook that is also an
/// allowance refusal listed as the refusal only. A result builds them from its definition's load
/// record followed by its run's record, so a fact both observed is listed once for each
/// ([`ObservedIn`]).
#[derive(Debug, Default)]
pub(crate) struct RunRecord {
    pub(crate) contradicted_claims: Vec<ContradictedClaim>,
    pub(crate) allowance_refusals: Vec<UnevaluatedHook>,
    pub(crate) unsupported_hooks: Vec<UnevaluatedHook>,
}

impl RunRecord {
    pub(crate) fn of<'a>(facts: impl IntoIterator<Item = &'a PathFact>) -> Self {
        let mut record = Self::default();
        let mut unsupported = Vec::new();
        for fact in facts {
            match fact {
                PathFact::ChosenValue(_) => {}
                PathFact::ContradictedClaim(claim) => {
                    if !record.contradicted_claims.contains(claim) {
                        record
                            .contradicted_claims
                            .push(ContradictedClaim::clone(claim));
                    }
                }
                PathFact::AllowanceRefusal(refusal) => {
                    if !record.allowance_refusals.contains(refusal) {
                        record.allowance_refusals.push(refusal.clone());
                    }
                }
                PathFact::UnsupportedHook(hook) => {
                    if !unsupported.contains(hook) {
                        unsupported.push(hook.clone());
                    }
                }
            }
        }
        record.unsupported_hooks = unsupported
            .into_iter()
            .filter(|hook| !record.allowance_refusals.contains(hook))
            .collect();
        record
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
    facts.into_iter().filter_map(PathFact::diagnostic).collect()
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
    /// Inside [`aside`]: notes are stamped and go nowhere.
    aside: bool,
    /// The rules whose work is under way, innermost last ([`observed_by`]).
    rules: Vec<Option<ObservingRule>>,
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
        if self.aside || (self.suspended && fact.suspends()) {
            return None;
        }
        let on_paths = fact.on_paths();
        let stray = (on_paths && self.run.is_some() && self.sinks.is_empty()).then(|| fact.clone());
        if let Some(run) = &mut self.run
            && !run.contains(&fact)
        {
            run.push(fact.clone());
        }
        if on_paths && let Some(sink) = self.sinks.last_mut() {
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

/// Whether a note has somewhere to go: a collection or a run record is open, so that work done
/// only to note a fact is worth doing.
pub(crate) fn is_open() -> bool {
    OPEN.get()
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

/// Note that an equation reduced `total`, an application of a symbol declared `total` to
/// defined arguments, to bottom: a contradicted claim, observed by the innermost rule whose work
/// is under way ([`observed_by`]).
pub(crate) fn note_contradicted_total(total: &ContradictedTotal) {
    if !OPEN.get() {
        return;
    }
    let rule = STATE.with_borrow(|state| state.rules.last().cloned().flatten());
    note(PathFact::ContradictedClaim(Box::new(ContradictedClaim {
        ground: total.application.attributes().variables.is_empty(),
        claim: Claim::Total(total.clone()),
        rule,
        observed_in: ObservedIn::Run,
    })));
}

/// Note that the normalization of `instance`, the result term a step of the innermost rule whose
/// work is under way built ([`observed_by`]), is `\bottom`, when that rule claims its result
/// defined ([`claims_defined_result`]): `found` (called only then) gives the term where
/// `\bottom` was found and whether the step's premises hold (every constraint `\top`), or
/// `None` when the result is not `\bottom`. The claim is refuted at this instance, a
/// contradicted claim observed by the rule itself; it is [`ground`](ContradictedClaim::ground)
/// when the instance is variable-free and the premises hold. A rule that is not declared so
/// claims nothing (a discharged rule's obligation is a load fact, not an attribute), and
/// nothing is noted.
pub(crate) fn note_contradicted_preservation(
    instance: &Term,
    found: impl FnOnce() -> Option<(Term, bool)>,
) {
    if !OPEN.get() {
        return;
    }
    let Some(rule) = STATE.with_borrow(|state| state.rules.last().cloned().flatten()) else {
        return;
    };
    if !rule.claims_defined_result {
        return;
    }
    let Some((undefined_term, premises_hold)) = found() else {
        return;
    };
    note_preservation(rule, instance, undefined_term, premises_hold);
}

/// Note that `rule`'s result `instance` is `\bottom` at `undefined_term`: its
/// `preserves-definedness` is refuted there, ground when `instance` is variable-free and the
/// step's premises hold (`premises_hold`).
pub(crate) fn note_preservation(
    rule: ObservingRule,
    instance: &Term,
    undefined_term: Term,
    premises_hold: bool,
) {
    note(PathFact::ContradictedClaim(Box::new(ContradictedClaim {
        ground: premises_hold && instance.attributes().variables.is_empty(),
        claim: Claim::PreservesDefinedness(ContradictedPreservation {
            rule_id: rule.unique_id.clone(),
            label: rule.label.clone(),
            origin: rule.origin.clone(),
            instance: instance.clone(),
            undefined_term,
        }),
        rule: Some(rule),
        observed_in: ObservedIn::Run,
    })));
}

/// Note that an application of `hook` was left unevaluated for `reason`, by the memory
/// allowance when `allowance` is set.
pub(crate) fn note_unevaluated_hook(hook: &str, reason: &UnsupportedHookReason, allowance: bool) {
    if !OPEN.get() {
        return;
    }
    let unevaluated = UnevaluatedHook {
        hook: hook.to_owned(),
        reason: reason.clone(),
        observed_in: ObservedIn::Run,
    };
    note(if allowance {
        PathFact::AllowanceRefusal(unevaluated)
    } else {
        PathFact::UnsupportedHook(unevaluated)
    });
}

/// Run `action`, the work of one rewrite rule (an attempt, or the normalization of a successor
/// it produced), so that each contradicted claim noted in it names the rule ([`rule`], built only
/// when something is open). `None` names no rule, for work of no rule's inside such work.
/// Restored on every exit.
pub(crate) fn observed_by<T>(
    rule: impl FnOnce() -> Option<ObservingRule>,
    action: impl FnOnce() -> T,
) -> T {
    struct Pop;
    impl Drop for Pop {
        fn drop(&mut self) {
            with_state(|state| {
                state.rules.pop();
            });
        }
    }
    if !OPEN.get() {
        return action();
    }
    let rule = rule();
    with_state(|state| state.rules.push(rule));
    let _pop = Pop;
    action()
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
    for diagnostic in diagnostics(facts) {
        diagnostic::emit(diagnostic);
    }
}

/// Run `action`, an evaluation whose outcome decides nothing in the run, with what it notes going
/// to no collection and no run record. The notes are still stamped ([`since`], [`noted_since`]),
/// so a memo entry made inside it carries them, and a later use of the entry replays them where
/// the run does decide on it. Restored on every exit.
pub(crate) fn aside<T>(action: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            let previous = self.0;
            with_state(|state| state.aside = previous);
        }
    }
    let _restore = Restore(with_state(|state| {
        std::mem::replace(&mut state.aside, true)
    }));
    action()
}

/// Run `action` with the notes of chosen values suspended: an evaluation whose value decides
/// nothing that depends on which admitted value it took. Every other kind of fact is noted as
/// anywhere else, because it can steer the definedness the evaluation decides: the
/// definedness-only fold of a pure hook reads an allowance refusal as "not defined without a
/// value" (`deferred::defined_without_value`), where a larger allowance gives the value and the
/// application is defined; one that reads a refusal as defined (`simplify::defined_uncomputed`)
/// over-reports it, which is sound. Restored on every exit.
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

    /// A refusal or an unsupported hook is a fact of the run only: it reaches the run record,
    /// whatever became of the work that met it, and no collection, so no path; noted outside
    /// every phase it is no stray note. A suspension leaves it noted, as it leaves every kind but
    /// a chosen value, and a memo learns it alike.
    #[test]
    fn a_fact_of_the_run_only_reaches_the_record_and_no_path() {
        let ((), run) = run(|| {
            note_unevaluated_hook(
                "BYTES.padRight",
                &UnsupportedHookReason::NotImplemented,
                true,
            );
            let ((), facts) = collect(|| {
                let marker = marker();
                suspend(|| {
                    note_unevaluated_hook(
                        "STRING.countAllOccurrences",
                        &UnsupportedHookReason::NotImplemented,
                        false,
                    );
                    note(fact("S"));
                });
                assert_eq!(since(marker).len(), 2);
            });
            assert!(facts.owned.is_empty());
            assert!(facts.shared.is_empty(), "{facts:?}");
        });
        let refusal = UnevaluatedHook {
            hook: "BYTES.padRight".to_owned(),
            reason: UnsupportedHookReason::NotImplemented,
            observed_in: ObservedIn::Run,
        };
        let hook = UnevaluatedHook {
            hook: "STRING.countAllOccurrences".to_owned(),
            reason: UnsupportedHookReason::NotImplemented,
            observed_in: ObservedIn::Run,
        };
        assert_eq!(
            run,
            [
                PathFact::AllowanceRefusal(refusal.clone()),
                PathFact::UnsupportedHook(hook.clone())
            ]
        );
        // An unsupported hook that is also a refusal is listed as the refusal only.
        let record = RunRecord::of(&[
            PathFact::UnsupportedHook(refusal.clone()),
            PathFact::AllowanceRefusal(refusal.clone()),
            PathFact::UnsupportedHook(hook.clone()),
        ]);
        assert_eq!(record.allowance_refusals, std::slice::from_ref(&refusal));
        assert_eq!(record.unsupported_hooks, [hook]);
        assert!(record.contradicted_claims.is_empty());
        // The load's refusal and the run's are two entries, the load's first.
        let at_load = PathFact::AllowanceRefusal(refusal.clone()).observed_at_load();
        let record = RunRecord::of(&[at_load, PathFact::AllowanceRefusal(refusal.clone())]);
        assert_eq!(
            record
                .allowance_refusals
                .iter()
                .map(|refusal| refusal.observed_in)
                .collect::<Vec<_>>(),
            [ObservedIn::Load, ObservedIn::Run]
        );
    }

    /// A rule scope is opened only while something is open, and closed on every exit.
    #[test]
    fn a_rule_scope_is_restored_on_every_exit() {
        let rule = || {
            Some(ObservingRule {
                unique_id: "r".to_owned(),
                label: None,
                origin: None,
                claims_defined_result: false,
            })
        };
        assert_eq!(observed_by(rule, || 1), 1);
        assert!(STATE.with_borrow(|state| state.rules.is_empty()));
        let ((), _) = run(|| {
            let ((), _) = collect(|| {
                let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    observed_by(rule, || {
                        assert_eq!(STATE.with_borrow(|state| state.rules.len()), 1);
                        panic!("unwinds");
                    })
                }));
                assert!(unwound.is_err());
                assert!(STATE.with_borrow(|state| state.rules.is_empty()));
            });
        });
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
