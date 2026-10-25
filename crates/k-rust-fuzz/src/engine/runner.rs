//! The seam between the engine's loop and case execution. Owner: FZ-06.
//!
//! The loop ([`super::campaign_loop`]) sees a case only through [`CaseRunner`]: run it on the
//! campaign's own backend, confirm it on a fresh one, and say whether a shrink move keeps a
//! value admissible. [`super::live::LiveCases`] implements it over holes, assembly, execution
//! and the target judge; the engine's unit tests implement it with scripted results.

use std::collections::BTreeMap;

use k_rust::backend::CancellationToken;

use crate::{
    exec::{Abort, OutcomeClass, UnjudgedReason},
    report::{
        Comparability, CrashKind, CrashSide, CrashSignature, CrashStage, HoleValue, IncidentalCase,
        KillKind, LoadRecord, Reaching, RejectionReason, WitnessSide,
    },
    score::{Guards, records::Compared},
    values::Value,
};

/// What the engine needs of one execution of a case (ARCHITECTURE 5, 6.1).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CaseRun {
    /// The case's class as judged; `hit` here means a candidate until confirmation agrees.
    pub(crate) class: OutcomeClass,
    /// Backend work over every execution of the case (both sides of a differential case).
    pub(crate) work: u64,
    /// Rule ids in coverage `applied`.
    pub(crate) applied: Vec<String>,
    /// Rule ids in coverage `matched`.
    pub(crate) matched: Vec<String>,
    /// Each rule id of `applied` with how many times the run applied it (coverage
    /// `appliedCounts`), when the campaign asks for counts (a campaign that weighs the corpus);
    /// empty otherwise.
    pub(crate) applied_counts: BTreeMap<String, u64>,
    /// The target rule was blocked (ARCHITECTURE 6.2).
    pub(crate) blocked: bool,
    /// Per rule whose condition entries the run recorded (only when the climb asks for them),
    /// the guard distance of each entry (`crate::score`); empty otherwise.
    pub(crate) guards: Guards,
    /// The comparisons the refuted guards of the recorded rules needed the other way round
    /// (`crate::score::records::comparisons`), for the run-time dictionary; empty when the run
    /// recorded no conditions.
    pub(crate) comparisons: Vec<Compared>,
    /// For an observer target, the greatest progress the observer answered on the run
    /// (`target::JudgedRun::progress`); `None` otherwise.
    pub(crate) progress: Option<u32>,
    /// The case is outside the determinism contract (ARCHITECTURE 5.4).
    pub(crate) outside_determinism: bool,
    /// Why the case was rejected; `Some` exactly when `class` is `rejected`.
    pub(crate) rejection: Option<RejectionReason>,
    /// Why the case could not be judged; `Some` exactly when `class` is `unsupported` or
    /// `baseline-incomplete` ([`crate::exec::reasons`]).
    pub(crate) unjudged: Option<UnjudgedReason>,
    /// Records the definitions' loads observed (T-5).
    pub(crate) load_records: Vec<LoadRecord>,
    /// Engine defects the case's judgement met, without their case number.
    pub(crate) defects: Vec<String>,
    /// Warnings about the case for the report, which lists each distinct text once.
    pub(crate) warnings: Vec<String>,
    /// For a (candidate) hit, what a witness reports of it.
    pub(crate) hit: Option<HitDetail>,
    /// When the case's run of the semantics under test (the case's run; a differential case's
    /// baseline) is `stuck` or `undefined` and that run is inside the determinism contract (a
    /// differential case's mutant run does not count), that class and what the report's
    /// incidental finding holds of it
    /// ([`crate::report::Incidentals`]), with `case` 0: the loop numbers it. `None` otherwise,
    /// and for a class the loop has already kept ([`CaseRunner::incidental_kept`]).
    pub(crate) incidental: Option<(OutcomeClass, Box<IncidentalCase>)>,
    /// What stopped paths of the result the class rests on, which the no-witness statement
    /// reads for `reached-unfinished` and `baseline-incomplete` cases.
    pub(crate) cut: Cut,
    /// For a differential case whose baseline run no bound and no clock cut (every path of it
    /// reached its end), the baseline's work; `None` otherwise and for every other target. The
    /// no-witness statement reads it for a case the work bound stopped on the mutant: the
    /// baseline needed this much, the mutant more than the bound (FZ-POLISH S-T5).
    pub(crate) baseline_ended_within: Option<u64>,
    /// For a pattern target, how many clean end leaves matched the pattern's configuration
    /// without its `requires` ([`crate::report::Totals::pattern_body_matches`]); `None` for
    /// every other target.
    pub(crate) pattern_body_matches: Option<u64>,
    /// The case crashed: a panic or an internal error of a run or its judgement
    /// ([`crate::exec::CaseFailure::crash_kind`]), or of the engine around them (FZ-CRASH).
    pub(crate) crash: Option<Box<CaseCrash>>,
    /// A panic was caught while the case ran, so the runner's backends may be half-changed and
    /// must be rebuilt before another case runs on them ([`CaseRunner::recover`]).
    pub(crate) poisoned: bool,
}

/// What a crashed case tells of its crash (FZ-CRASH): what crashed, where, and how to re-run it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CaseCrash {
    /// A panic or an internal error.
    pub(crate) kind: CrashKind,
    /// Which run, or the engine.
    pub(crate) side: CrashSide,
    /// Which stage.
    pub(crate) stage: CrashStage,
    /// The panic's or the error's message.
    pub(crate) message: String,
    /// The panic's location, when the hook saw it.
    pub(crate) location: Option<String>,
    /// The clock stopped the run: the per-case safety limit fired, or the caller's token was
    /// cancelled.
    pub(crate) clock: bool,
    /// The `krun` command line equivalent to the crashed run, for a crash in `execute` on a
    /// route `krun` runs.
    pub(crate) krun_command: Option<String>,
    /// The instantiated program text, when the case assembled one.
    pub(crate) program: Option<String>,
    /// The instantiated configuration-variable bindings.
    pub(crate) config_vars: BTreeMap<String, String>,
}

impl CaseCrash {
    /// A crash of the engine around the runs: a panic the loop caught outside every run.
    pub(crate) fn engine(message: String, location: Option<String>, clock: bool) -> Self {
        Self {
            kind: CrashKind::Panic,
            side: CrashSide::Engine,
            stage: CrashStage::Engine,
            message,
            location,
            clock,
            krun_command: None,
            program: None,
            config_vars: BTreeMap::new(),
        }
    }

    /// The crash's signature (`crate::crash::signature`).
    pub(crate) fn signature(&self) -> CrashSignature {
        crate::crash::signature(
            self.kind,
            self.side,
            self.stage,
            &self.message,
            self.location.as_deref(),
        )
    }
}

/// Which bounds stopped some path of the result a case's class rests on: the judged result of a
/// rule or pattern case; of a differential case, the baseline's when the case is
/// `baseline-incomplete` and the mutant's otherwise. The class alone does not say whether
/// raising a bound could change a `reached-unfinished` or `baseline-incomplete` case: either
/// also covers paths that stopped abnormally, which no bound changes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Cut {
    /// A path stopped at the depth or breadth bound.
    pub(crate) depth: bool,
    /// A path stopped at the work bound.
    pub(crate) work: bool,
    /// The run or a path stopped at the clock: the per-case safety limit, a step deadline or
    /// the caller's token.
    pub(crate) clock: bool,
}

impl CaseRun {
    /// A case rejected before execution, or by the backend at depth 0, for `reason`.
    pub(crate) fn rejected(reason: RejectionReason, work: u64) -> Self {
        Self {
            class: OutcomeClass::Rejected,
            work,
            applied: Vec::new(),
            matched: Vec::new(),
            applied_counts: BTreeMap::new(),
            blocked: false,
            guards: Guards::new(),
            comparisons: Vec::new(),
            progress: None,
            outside_determinism: false,
            rejection: Some(reason),
            unjudged: None,
            load_records: Vec::new(),
            defects: Vec::new(),
            warnings: Vec::new(),
            hit: None,
            incidental: None,
            cut: Cut::default(),
            baseline_ended_within: None,
            pattern_body_matches: None,
            crash: None,
            poisoned: false,
        }
    }
}

/// What a witness reports of a hit (ARCHITECTURE 2.6, 9.3).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct HitDetail {
    /// The hole overlay with values, in declaration order.
    pub(crate) holes: Vec<HoleValue>,
    /// Each definition's initial and final configurations: the baseline, then the mutant of a
    /// differential case.
    pub(crate) sides: Vec<WitnessSide>,
    /// Which side's leaf reached the target, and its index in that side's configurations.
    pub(crate) reaching: Reaching,
    /// For a differential hit, whether the mutant added or removed an end; a confirmation and
    /// a kept shrink candidate must agree on it.
    pub(crate) kill: Option<KillKind>,
    /// The depth of the reaching leaf; `None` for a hit of the whole run, which names no leaf
    /// (ARCHITECTURE 5.3, D16).
    pub(crate) steps: Option<u64>,
    /// The reaching leaf's configuration (the killing mutant leaf of a differential case), or
    /// for a hit of the whole run every leaf's configuration in the backend's order, one per
    /// line, as KORE text: the case and its confirmation agree only when these are equal.
    pub(crate) reaching_state: String,
    /// The `krun` command line that re-runs the case on the baseline, when one is equivalent.
    pub(crate) krun_command: Option<String>,
    /// For a differential case, the `krun` command line on the mutant, when one is equivalent.
    pub(crate) mutant_krun_command: Option<String>,
    /// The instantiated program text, for a campaign with a program text.
    pub(crate) program: Option<String>,
    /// For a rule or pattern hit, whether the program's run of every path is comparable
    /// ([`crate::report::WitnessCase::comparable`]), when the case judged it; `None` for every
    /// other target, and for a hit whose judgement the loop makes outside the case
    /// ([`CaseRunner::comparability`]).
    pub(crate) comparable: Option<Comparability>,
    /// The instantiated configuration-variable bindings ([`crate::report::WitnessCase::config_vars`]).
    pub(crate) config_vars: BTreeMap<String, String>,
}

/// The comparable judgement of a witness case made outside its case
/// ([`CaseRunner::comparability`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct JudgedComparability {
    /// The judgement.
    pub(crate) comparable: Comparability,
    /// The work of the run of every path that made it.
    pub(crate) work: u64,
    /// That run crashed ([`CaseRun::crash`]).
    pub(crate) crash: Option<Box<CaseCrash>>,
    /// A panic was caught while it ran ([`CaseRun::poisoned`]).
    pub(crate) poisoned: bool,
}

/// Why a confirmation gave no run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ConfirmFailure {
    /// A failure every execution would repeat, such as a failed solver prelude on the fresh
    /// backend: the campaign aborts (ARCHITECTURE 5.3).
    Abort(Abort),
    /// The fresh backend, assembly or target did not build: the candidate is not confirmed, an
    /// engine defect.
    Failed(String),
}

/// Case execution as the loop sees it.
pub(crate) trait CaseRunner {
    /// Run one case (values in hole order) on the campaign's own backend(s), within `cancel`'s
    /// scope.
    ///
    /// # Errors
    ///
    /// [`Abort`] for a failure every case would repeat (a failed solver prelude).
    fn run_case(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, Abort>;

    /// Confirm a case independently of the path that found it (ARCHITECTURE 7): a fresh
    /// `Backend` (its own session and solver, so no solver cache is shared), a fresh program
    /// assembly that assembles the case from the instantiated text, public execute, and a
    /// re-resolved target. What is reused is immutable and independent of every earlier run:
    /// the internalized definition each fresh backend copies, and the hole resolution and
    /// round-trip positions, computed once on a build of their own
    /// ([`super::live::DefinitionCache`]).
    ///
    /// # Errors
    ///
    /// [`ConfirmFailure::Abort`] when the run aborts as every run would (a failed solver
    /// prelude), and [`ConfirmFailure::Failed`] when the fresh backend or assembly cannot be
    /// built.
    fn confirm(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, ConfirmFailure>;

    /// Whether `value` satisfies hole `hole`'s sort and constraints; shrink moves that leave
    /// them are never run.
    fn admissible(&self, hole: usize, value: &Value) -> bool;

    /// The comparable judgement of a witness case with `values` that its case did not make
    /// (`crate::target::ResolvedTarget::comparability`: a rule or pattern target without
    /// `comparable-end` whose cases run one path or stop at the target's rule), with the work
    /// of the run of every path it made, within `cancel`'s scope, on the campaign's own
    /// backend. The run is part of no case: the loop calls this once per reported witness
    /// case, after shrinking, and charges the work to the campaign's total alone, so that it
    /// moves no case's class, determinism, coverage or work. `None` when the case made the
    /// judgement or the target carries none, and by default.
    fn comparability(
        &mut self,
        _values: &[Value],
        _cancel: Option<&CancellationToken>,
    ) -> Option<JudgedComparability> {
        None
    }

    /// [`Self::comparability`] of `values` on fresh cases, built as a confirmation's are
    /// ([`Self::confirm`]): the re-run of a crash of the comparable judgement (FZ-CRASH). `None`
    /// when this runner cannot repeat the judgement, and by default.
    fn confirm_comparability(
        &mut self,
        _values: &[Value],
        _cancel: Option<&CancellationToken>,
    ) -> Option<Result<JudgedComparability, ConfirmFailure>> {
        None
    }

    /// Whether [`Self::comparability`] makes a judgement for this campaign's witness cases
    /// (a rule or pattern target that judges comparability outside its cases), for a witness
    /// whose judgement a failed rebuild stopped. `false` by default.
    fn comparability_pending(&self) -> bool {
        false
    }

    /// Rebuild the campaign's own backends after a caught panic (FZ-CRASH): a panic may leave a
    /// backend, its session, its solver or an assembler half-changed, so the loop calls this
    /// after every panic it or a run caught, before the next execution on the campaign's
    /// runner. The rebuilt runner must run every later case as the campaign's own would have
    /// run it. Nothing to do by default.
    ///
    /// # Errors
    ///
    /// Why the backends did not rebuild: the campaign then aborts (`rebuild-failed`).
    fn recover(&mut self) -> Result<(), String> {
        Ok(())
    }

    /// The loop kept an incidental finding of `class` ([`CaseRun::incidental`]): later cases
    /// of that class need not describe one, which spares building a finding no report holds.
    fn incidental_kept(&mut self, _class: OutcomeClass) {}
}
