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
        HoleValue, IncidentalCase, KillKind, LoadRecord, Reaching, RejectionReason, WitnessSide,
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

    /// The loop kept an incidental finding of `class` ([`CaseRun::incidental`]): later cases
    /// of that class need not describe one, which spares building a finding no report holds.
    fn incidental_kept(&mut self, _class: OutcomeClass) {}
}
