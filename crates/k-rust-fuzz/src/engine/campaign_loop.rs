//! The loop over cases, the budget, confirmation, shrinking and the report (ARCHITECTURE 7,
//! 9.2, 9.3). Owner: FZ-06.

use std::{collections::BTreeSet, fmt::Write as _};

use k_rust::backend::CancellationToken;

use super::{
    proposer::{CoverageFeedback, Feedback as _, Observation, Proposal},
    runner::{CaseRun, CaseRunner, HitDetail},
    schedule::Schedule,
    shrink::{Verdict, shrink},
};
use crate::{
    exec::OutcomeClass,
    report::{
        CampaignOutcome, EngineDefect, FuzzReport, HitLabel, KillKind, LoadRecord, NoWitness,
        REPORT_SCHEMA, REPORT_VERSION, RejectionReason, ReportIdentity, SortOverride, Totals,
        Witness, WitnessCase, digest_hex,
    },
    spec::{Budget, CaseOptions, PathMode},
    values::{Constraints, Value},
};

/// The most shrink candidates the engine executes for one witness. Shrinking is also bounded
/// by a work budget; under a case budget this cap alone bounds it.
pub(crate) const MAX_SHRINK_RUNS: u64 = 256;

/// Everything the loop reads besides the runner, the schedule, the budget and the token.
pub(crate) struct LoopSettings {
    /// The report's identity; the loop fills in the budget.
    pub(crate) identity: ReportIdentity,
    /// Rejected cases after which the campaign ends with `rejected-out`.
    pub(crate) rejection_cap: u64,
    /// The case options, for the no-witness statement.
    pub(crate) options: CaseOptions,
    /// How a hit is labelled.
    pub(crate) label: HitLabel,
    /// The clean-leaf facts a hit rests on.
    pub(crate) clean_leaf_facts: Vec<String>,
    /// Each hole's constraints, in hole order, which bound shrink moves.
    pub(crate) constraints: Vec<Constraints>,
    /// Holes whose refused sort an override admitted.
    pub(crate) sort_overrides: Vec<SortOverride>,
}

/// Run cases until the budget is spent, a witness is confirmed and shrunk, the rejection cap
/// is reached, the schedule is exhausted, a case aborts, or `cancel` is cancelled.
///
/// Budget accounting ([`Budget`]): every case is charged its work and at least 1; under
/// `Budget::Work` an execution starts only while the work spent is below the budget, except the
/// confirmation of a candidate, which always runs so that a found candidate is never left
/// unconfirmed. A case whose confirmation fails or disagrees is an engine defect and is counted
/// `unsupported`, never `hit` (ARCHITECTURE 7).
pub(crate) fn run_loop(
    runner: &mut dyn CaseRunner,
    schedule: &mut Schedule,
    settings: &LoopSettings,
    budget: Budget,
    cancel: Option<&CancellationToken>,
) -> FuzzReport {
    let mut state = State::new(budget);
    let mut feedback = CoverageFeedback::default();
    let ending = loop {
        if is_cancelled(cancel) {
            break Ending::Cancelled;
        }
        if state.rejected() >= settings.rejection_cap {
            break Ending::RejectedOut;
        }
        if !state.may_start_case() {
            break Ending::Budget;
        }
        let Some(proposal) = schedule.next() else {
            break Ending::Exhausted;
        };
        let case = state.totals.cases;
        state.sequence(&proposal.values);
        let run = match runner.run_case(&proposal.values, cancel) {
            Ok(run) => run,
            Err(abort) => {
                state.abort = Some(abort.reason);
                break Ending::Aborted;
            }
        };
        state.charge(run.work);
        state.totals.cases += 1;
        for defect in &run.defects {
            state.defect(Some(case), defect.clone());
        }
        let mut class = run.class;
        if class == OutcomeClass::Hit {
            match confirm(runner, &mut state, &proposal.values, &run, cancel) {
                Confirmed::Agrees(detail) => {
                    state.record(&run, OutcomeClass::Hit);
                    let witness = finish_witness(
                        runner, &mut state, settings, case, proposal, *detail, cancel,
                    );
                    return state.report(
                        settings,
                        budget,
                        CampaignOutcome::WitnessFound { witness },
                    );
                }
                Confirmed::Cancelled => {
                    // The candidate was not confirmed: a clock-dependent case, whose coverage
                    // the totals do not take, and a trace in the report (ARCHITECTURE 5.4).
                    state.totals.unconfirmed += 1;
                    state.warnings.push(format!(
                        "case {case} reached the target with the values {}; its confirmation \
                         was cancelled, so it is not a witness",
                        render(&proposal.values)
                    ));
                    let cancelled = CaseRun {
                        outside_determinism: true,
                        ..run
                    };
                    state.record(&cancelled, OutcomeClass::Timeout);
                    break Ending::Cancelled;
                }
                Confirmed::Disagrees(description) => {
                    state.totals.unconfirmed += 1;
                    state.defect(Some(case), description);
                    class = OutcomeClass::Unsupported;
                }
            }
        }
        state.record(&run, class);
        if is_cancelled(cancel) {
            break Ending::Cancelled;
        }
        let observation = Observation {
            case,
            class,
            applied: run.applied,
            matched: run.matched,
            work: run.work,
            score: None,
        };
        let interesting = feedback.is_interesting(&observation);
        schedule.observe(&proposal, &observation, interesting);
    };
    let no_witness = no_witness(
        ending,
        &state.totals_snapshot(),
        budget,
        &settings.options,
        settings.rejection_cap,
    );
    let outcome = match ending {
        Ending::Budget | Ending::Exhausted => CampaignOutcome::NoWitnessFound { no_witness },
        Ending::RejectedOut => CampaignOutcome::RejectedOut { no_witness },
        Ending::Cancelled => CampaignOutcome::Cancelled { no_witness },
        Ending::Aborted => CampaignOutcome::Aborted {
            reason: state.abort.take().unwrap_or_default(),
            no_witness,
        },
    };
    state.report(settings, budget, outcome)
}

/// The report of a run that executes no case (an equivalent differential pair, a failed
/// rebuild).
pub(crate) fn report_without_cases(
    settings: &LoopSettings,
    budget: Budget,
    outcome: CampaignOutcome,
) -> FuzzReport {
    State::new(budget).report(settings, budget, outcome)
}

fn is_cancelled(cancel: Option<&CancellationToken>) -> bool {
    cancel.is_some_and(CancellationToken::is_cancelled)
}

/// The verdict of a candidate's confirmation.
enum Confirmed {
    /// The confirmation is a hit with the same reaching state.
    Agrees(Box<HitDetail>),
    /// The caller cancelled while it ran.
    Cancelled,
    /// It failed or disagreed: an engine defect, described.
    Disagrees(String),
}

/// Confirm a candidate (ARCHITECTURE 7), charging its work.
fn confirm(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    values: &[Value],
    candidate: &CaseRun,
    cancel: Option<&CancellationToken>,
) -> Confirmed {
    let reaching = candidate
        .hit
        .as_ref()
        .map(|detail| (detail.reaching_state.clone(), detail.kill));
    match runner.confirm(values, cancel) {
        Err(message) => {
            state.charge(0);
            if is_cancelled(cancel) {
                Confirmed::Cancelled
            } else {
                Confirmed::Disagrees(format!(
                    "the case reached the target, but its confirmation failed: {message}"
                ))
            }
        }
        Ok(confirmation) => {
            state.charge(confirmation.work);
            if is_cancelled(cancel) && confirmation.class != OutcomeClass::Hit {
                return Confirmed::Cancelled;
            }
            match confirmation.hit {
                Some(detail)
                    if confirmation.class == OutcomeClass::Hit
                        && reaching.as_ref()
                            == Some(&(detail.reaching_state.clone(), detail.kill)) =>
                {
                    Confirmed::Agrees(Box::new(detail))
                }
                Some(_) if confirmation.class == OutcomeClass::Hit => Confirmed::Disagrees(
                    "the case reached the target, but its confirmation reached it in another \
                     configuration or by another kind of kill"
                        .into(),
                ),
                _ => Confirmed::Disagrees(format!(
                    "the case reached the target, but its confirmation classed it `{}`",
                    confirmation.class.name()
                )),
            }
        }
    }
}

/// Shrink a confirmed witness and build the report's witness (ARCHITECTURE 7).
fn finish_witness(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    settings: &LoopSettings,
    case: u64,
    proposal: Proposal,
    first: HitDetail,
    cancel: Option<&CancellationToken>,
) -> Witness {
    let Proposal { values, trees, .. } = proposal;
    let kind = first.kill;
    let mut last: Option<HitDetail> = None;
    let mut runs = 0_u64;
    let shrunk = {
        let mut test = |candidate: &[Value]| -> Verdict {
            if is_cancelled(cancel) || runs >= MAX_SHRINK_RUNS {
                return Verdict::Stop;
            }
            if candidate
                .iter()
                .enumerate()
                .any(|(hole, value)| !runner.admissible(hole, value))
            {
                return Verdict::Miss;
            }
            if !state.may_start_extra() {
                return Verdict::Stop;
            }
            runs += 1;
            let screened = match runner.run_case(candidate, cancel) {
                Ok(run) => run,
                Err(abort) => {
                    state
                        .warnings
                        .push(format!("shrinking stopped: {}", abort.reason));
                    return Verdict::Stop;
                }
            };
            state.charge(screened.work);
            // A shrink keeps the witness's kind of kill: a removed end never shrinks into an
            // added one, which is another behaviour (FZ-08 review S1).
            if screened.class != OutcomeClass::Hit
                || screened.hit.as_ref().map(|detail| detail.kill) != Some(kind)
            {
                return Verdict::Miss;
            }
            match confirm(runner, state, candidate, &screened, cancel) {
                Confirmed::Agrees(detail) => {
                    last = Some(*detail);
                    Verdict::Hit
                }
                Confirmed::Cancelled => Verdict::Stop,
                Confirmed::Disagrees(description) => {
                    state.defect(
                        Some(case),
                        format!("shrink candidate {}: {description}", render(candidate)),
                    );
                    Verdict::Miss
                }
            }
        };
        shrink(&values, trees, &settings.constraints, &mut test)
    };
    let to_case = |detail: HitDetail| WitnessCase {
        holes: detail.holes,
        class: OutcomeClass::Hit,
        sides: detail.sides,
        reaching: detail.reaching,
        kill: detail.kill,
        steps: detail.steps,
    };
    let (shrunk, krun_command) = match last {
        Some(detail) if shrunk != values => {
            let command = detail.krun_command.clone();
            (Some(to_case(detail)), command)
        }
        _ => (None, first.krun_command.clone()),
    };
    Witness {
        label: settings.label,
        first: to_case(first),
        shrunk,
        clean_leaf_facts: witness_facts(&settings.clean_leaf_facts, kind),
        krun_command,
    }
}

/// The facts a witness rests on: the clean-leaf facts of its target, and for a differential
/// witness the conditions of ARCHITECTURE 4.3 for its kind of kill (with D15's requirement that
/// every end of the complete side be data).
fn witness_facts(base: &[String], kind: Option<KillKind>) -> Vec<String> {
    let extra: &[&str] = match kind {
        None => &[],
        Some(KillKind::AddedEnd) => &[
            "baseline-complete",
            "every-baseline-end-constructor-only",
            "mutant-end-natural",
            "mutant-end-constructor-only",
            "mutant-end-not-in-baseline-ends",
        ],
        Some(KillKind::RemovedEnd) => &[
            "mutant-complete",
            "every-mutant-end-constructor-only",
            "baseline-end-natural",
            "baseline-end-constructor-only",
            "baseline-end-not-in-mutant-ends",
        ],
    };
    base.iter()
        .cloned()
        .chain(extra.iter().map(|fact| (*fact).to_owned()))
        .collect()
}

fn render(values: &[Value]) -> String {
    serde_json::to_string(values).expect("values serialize")
}

/// The loop's running totals.
struct State {
    budget: Budget,
    totals: Totals,
    load_records: BTreeSet<LoadRecord>,
    warnings: Vec<String>,
    defects: Vec<EngineDefect>,
    abort: Option<String>,
}

impl State {
    fn new(budget: Budget) -> Self {
        Self {
            budget,
            totals: Totals {
                case_sequence_digest: digest_hex(b""),
                ..Totals::default()
            },
            load_records: BTreeSet::new(),
            warnings: Vec::new(),
            defects: Vec::new(),
            abort: None,
        }
    }

    fn rejected(&self) -> u64 {
        self.totals
            .classes
            .get(&OutcomeClass::Rejected)
            .copied()
            .unwrap_or(0)
    }

    fn may_start_case(&self) -> bool {
        match self.budget {
            Budget::Cases(cases) => self.totals.cases < cases,
            Budget::Work(work) => self.totals.work < work,
        }
    }

    /// Whether a shrink run may start: confirmation and shrink runs are not cases, so only a
    /// work budget bounds them.
    fn may_start_extra(&self) -> bool {
        match self.budget {
            Budget::Cases(_) => true,
            Budget::Work(work) => self.totals.work < work,
        }
    }

    /// Charge one execution's work, at least 1 (a failed run reports none).
    fn charge(&mut self, work: u64) {
        self.totals.work = self.totals.work.saturating_add(work.max(1));
    }

    /// Chain one case's values into [`Totals::case_sequence_digest`].
    fn sequence(&mut self, values: &[Value]) {
        let mut bytes = self.totals.case_sequence_digest.clone().into_bytes();
        bytes.push(b'\n');
        bytes.extend(render(values).into_bytes());
        self.totals.case_sequence_digest = digest_hex(&bytes);
    }

    fn defect(&mut self, case: Option<u64>, description: String) {
        self.defects.push(EngineDefect { case, description });
    }

    /// Count a case under `class`.
    fn record(&mut self, run: &CaseRun, class: OutcomeClass) {
        *self.totals.classes.entry(class).or_insert(0) += 1;
        if class == OutcomeClass::Rejected {
            // `Totals::rejections` sums to the `rejected` count; every runner gives a reason.
            debug_assert!(run.rejection.is_some(), "a rejected case without a reason");
            let reason = run.rejection.unwrap_or(RejectionReason::BackendRefused);
            *self.totals.rejections.entry(reason).or_insert(0) += 1;
            return;
        }
        self.load_records.extend(run.load_records.iter().cloned());
        if run.blocked {
            self.totals.target_blocked += 1;
        }
        if run.outside_determinism {
            self.totals.outside_determinism += 1;
            return;
        }
        let coverage = &mut self.totals.coverage;
        coverage.applied.extend(run.applied.iter().cloned());
        coverage.matched.extend(run.matched.iter().cloned());
    }

    fn totals_snapshot(&mut self) -> Totals {
        self.totals.rejection_rate_permille = if self.totals.cases == 0 {
            0
        } else {
            self.rejected().saturating_mul(1000) / self.totals.cases
        };
        self.totals.clone()
    }

    fn report(
        mut self,
        settings: &LoopSettings,
        budget: Budget,
        outcome: CampaignOutcome,
    ) -> FuzzReport {
        let totals = self.totals_snapshot();
        FuzzReport {
            schema: REPORT_SCHEMA.into(),
            version: REPORT_VERSION,
            identity: ReportIdentity {
                budget,
                ..settings.identity.clone()
            },
            outcome,
            totals,
            load_records: self.load_records.into_iter().collect(),
            sort_overrides: settings.sort_overrides.clone(),
            warnings: self.warnings,
            engine_defects: self.defects,
        }
    }
}

/// Why a campaign ended without a witness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Ending {
    /// The budget was spent.
    Budget,
    /// Every proposer was exhausted before the budget.
    Exhausted,
    /// The rejection cap was reached.
    RejectedOut,
    /// The caller cancelled.
    Cancelled,
    /// A case aborted.
    Aborted,
}

/// The bounded statement of a campaign that ended without a witness (ARCHITECTURE 9.3): the
/// cases and work spent, that it is no proof, why it ended, the path mode followed, every count
/// of cases that could not yield a witness or could not be judged, and the bounds to raise. In
/// one-path mode it always names the all-paths option (see [`NoWitness::statement`]).
pub(crate) fn no_witness(
    ending: Ending,
    totals: &Totals,
    budget: Budget,
    options: &CaseOptions,
    rejection_cap: u64,
) -> NoWitness {
    let plural = |count: u64, noun: &str| {
        if count == 1 {
            format!("{count} {noun}")
        } else {
            format!("{count} {noun}s")
        }
    };
    let count = |class: OutcomeClass| totals.classes.get(&class).copied().unwrap_or(0);
    let mut text = format!(
        "No witness was found in {} ({} of work); this is not a proof that no witness exists.",
        plural(totals.cases, "case"),
        totals.work
    );
    match ending {
        Ending::Budget => text.push_str(" The budget was spent."),
        Ending::Exhausted => text.push_str(
            " The campaign ended before its budget because every proposer was exhausted; enable \
             the blind proposer to run more cases.",
        ),
        Ending::RejectedOut => {
            let reasons: Vec<String> = totals
                .rejections
                .iter()
                .map(|(reason, count)| {
                    let name = serde_json::to_value(reason)
                        .ok()
                        .and_then(|name| name.as_str().map(str::to_owned))
                        .unwrap_or_default();
                    format!("{count} {name}")
                })
                .collect();
            write!(
                text,
                " The campaign ended at the rejection cap of {rejection_cap} rejected cases ({}).",
                reasons.join(", ")
            )
            .expect("writing to a String");
        }
        Ending::Cancelled => text.push_str(" The caller cancelled the campaign."),
        Ending::Aborted => {
            text.push_str(" The campaign aborted on a failure every case would repeat.");
        }
    }
    let rejected = count(OutcomeClass::Rejected);
    if rejected > 0 && ending != Ending::RejectedOut {
        write!(text, " {} rejected and not run.", plural_were(rejected))
            .expect("writing to a String");
    }
    let unsupported = count(OutcomeClass::Unsupported);
    if unsupported > 0 {
        write!(
            text,
            " {} could not be judged (unsupported) and may hide a witness.",
            plural(unsupported, "case")
        )
        .expect("writing to a String");
    }
    let incomplete = count(OutcomeClass::BaselineIncomplete);
    if incomplete > 0 {
        write!(
            text,
            " {} had an incomplete baseline, so no kill could be judged.",
            plural(incomplete, "case")
        )
        .expect("writing to a String");
    }
    if totals.unconfirmed > 0 {
        write!(
            text,
            " {} reached the target but {} not confirmed (see the warnings and engine defects); \
             one of them may be a real witness.",
            plural(totals.unconfirmed, "candidate"),
            if totals.unconfirmed == 1 {
                "was"
            } else {
                "were"
            }
        )
        .expect("writing to a String");
    }
    if totals.outside_determinism > 0 {
        write!(
            text,
            " {} outside the determinism contract.",
            plural_were(totals.outside_determinism)
        )
        .expect("writing to a String");
    }
    let depth = count(OutcomeClass::DepthBound);
    let work = count(OutcomeClass::WorkBound);
    let timeouts = count(OutcomeClass::Timeout);
    let unfinished = count(OutcomeClass::ReachedUnfinished);
    match options.paths {
        PathMode::OnePath => text.push_str(
            " Only k-rust's first-applicable path of each input was explored (one-path mode); \
             the all-paths option explores every path.",
        ),
        PathMode::AllPaths if depth + work + timeouts + unsupported == 0 => {
            text.push_str(" Every path of each input was explored (all-paths mode).");
        }
        PathMode::AllPaths => text.push_str(
            " Every path of each input was followed up to the bounds below (all-paths mode); \
             the cases they cut or that could not be judged were not explored to their ends.",
        ),
    }
    if depth > 0 {
        let bound = options.max_depth.map_or_else(
            || "its depth or breadth bound".to_owned(),
            |d| format!("max-depth {d}"),
        );
        write!(
            text,
            " {} stopped at {bound}: raise max-depth.",
            plural(depth, "case")
        )
        .expect("writing to a String");
    }
    if work > 0 {
        let bound = options
            .effective_max_work()
            .map_or_else(|| "its work bound".to_owned(), |w| format!("max-work {w}"));
        write!(
            text,
            " {} stopped at {bound}: raise max-work.",
            plural(work, "case")
        )
        .expect("writing to a String");
    }
    if timeouts > 0 {
        let advice = if options.safety_limit_ms.is_some() {
            ": raise the per-case safety limit"
        } else {
            ""
        };
        write!(text, " {} timed out{advice}.", plural(timeouts, "case"))
            .expect("writing to a String");
    }
    if unfinished > 0 {
        write!(
            text,
            " {} reached the target without ending naturally: raise the bounds so that they \
             finish.",
            plural(unfinished, "case")
        )
        .expect("writing to a String");
    }
    if ending == Ending::Budget {
        match budget {
            Budget::Cases(cases) => write!(
                text,
                " To run more cases, raise the case budget above {cases}."
            ),
            Budget::Work(work) => write!(
                text,
                " To run more cases, raise the work budget above {work}."
            ),
        }
        .expect("writing to a String");
    }
    NoWitness {
        statement: text,
        path_mode: options.paths,
    }
}

/// "1 case was" or "N cases were".
fn plural_were(count: u64) -> String {
    if count == 1 {
        "1 case was".to_owned()
    } else {
        format!("{count} cases were")
    }
}
