//! The loop over cases, the budget, confirmation, shrinking and the report (ARCHITECTURE 7,
//! 9.2, 9.3). Owner: FZ-06.

use std::{collections::BTreeSet, fmt::Write as _, sync::Arc};

use k_rust::backend::CancellationToken;

use super::{
    proposer::{CoverageFeedback, Feedback as _, Observation, Proposal},
    runner::{CaseRun, CaseRunner, ConfirmFailure, Cut, HitDetail},
    schedule::Schedule,
    shrink::{Verdict, shrink},
};
use crate::{
    exec::{Abort, NormalEndKind, OutcomeClass, UnjudgedReason},
    report::{
        BestScore, CampaignOutcome, EngineDefect, FuzzReport, HitLabel, Incidentals, KillKind,
        LoadRecord, NoWitness, NormalEnds, REPORT_SCHEMA, REPORT_VERSION, RejectionReason,
        ReportIdentity, SortOverride, Totals, Witness, WitnessCase, digest_hex,
    },
    score::{Score, Scorer, Signals},
    spec::{Budget, CaseOptions, PathMode},
    target::RuleName,
    values::{Constraints, Value, ValueSort},
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
    /// Campaign-level warnings known before the first case (the rule graph's), which every
    /// report starts with.
    pub(crate) warnings: Vec<String>,
    /// The findings of the definitions' full critical-pair checks, which every report carries
    /// (`FuzzReport::definition_findings`).
    pub(crate) definition_findings: Vec<crate::report::DefinitionFinding>,
    /// The scorer of the campaign's target, when a proposer climbs a score (ARCHITECTURE 6.4).
    pub(crate) scorer: Option<Scorer>,
    /// The rank of each recorded rule in a case's pool of run-time literals, its rule-graph
    /// distance to the target (`crate::proposers::runtime::pool`); empty when no pool is read.
    pub(crate) pool_rank: std::collections::BTreeMap<String, u64>,
    /// Which normal end each definition's classes rest on, for the report.
    pub(crate) normal_end: Option<NormalEnds>,
    /// The names of every id in the catalog of the definition whose coverage the cases record,
    /// from which the report names the rules its coverage holds.
    pub(crate) rule_names: Arc<std::collections::BTreeMap<String, RuleName>>,
    /// The holes' finite domains, when every hole has one and their product is at most
    /// [`MAX_EXHAUSTIVE`]: the campaign ends once every assignment of them has run.
    pub(crate) domain: Option<FiniteDomain>,
}

/// The most assignments a campaign's finite domain may have for the loop to track which ran
/// and end when all have ([`FiniteDomain`]).
pub(crate) const MAX_EXHAUSTIVE: u64 = 4096;

/// The finite set of values one hole is generated from (FZ-POLISH N-T1).
#[derive(Clone, Debug, Eq, PartialEq)]
enum HoleDomain {
    /// The hole's choices.
    Choices(Vec<Value>),
    /// `true` and `false`.
    Bool,
    /// The integers of an inclusive range (an `Int` hole, or the unsigned values of an `MInt`
    /// hole, its range cut to the width).
    Ints {
        min: num_bigint::BigInt,
        max: num_bigint::BigInt,
        /// For an `MInt` hole, its width.
        width: Option<u32>,
    },
}

impl HoleDomain {
    /// The domain of a hole of `sort` generated under `constraints` (its effective
    /// constraints), when it is finite.
    fn of(sort: &ValueSort, constraints: &Constraints) -> Option<Self> {
        if let Some(choices) = &constraints.choices {
            let mut distinct: Vec<Value> = Vec::new();
            for choice in choices {
                if !distinct.contains(choice) {
                    distinct.push(choice.clone());
                }
            }
            return Some(Self::Choices(distinct));
        }
        let range = constraints.range.as_ref();
        match sort.generated() {
            ValueSort::Bool => Some(Self::Bool),
            ValueSort::Int => Some(Self::Ints {
                min: range?.min.clone()?,
                max: range?.max.clone()?,
                width: None,
            }),
            ValueSort::MInt { width } => {
                let top: num_bigint::BigInt = (num_bigint::BigInt::from(1) << *width) - 1;
                let min = range
                    .and_then(|range| range.min.clone())
                    .unwrap_or_default()
                    .max(num_bigint::BigInt::default());
                let max = range
                    .and_then(|range| range.max.clone())
                    .map_or_else(|| top.clone(), |max| max.min(top.clone()));
                Some(Self::Ints {
                    min,
                    max,
                    width: Some(*width),
                })
            }
            _ => None,
        }
    }

    /// The value of index `index` (below [`Self::size`]): a choice in order, `false` then
    /// `true`, the integers from the range's minimum.
    fn value(&self, index: u64) -> Value {
        match self {
            Self::Choices(choices) => {
                choices[usize::try_from(index).expect("an index below the domain's size")].clone()
            }
            Self::Bool => Value::Bool(index == 1),
            Self::Ints {
                min, width: None, ..
            } => Value::Int(min + index),
            Self::Ints {
                min,
                width: Some(width),
                ..
            } => Value::MInt {
                width: *width,
                value: (min + index).to_biguint().unwrap_or_default(),
            },
        }
    }

    /// How many values the domain has, when it fits a `u64`.
    fn size(&self) -> Option<u64> {
        match self {
            Self::Choices(choices) => u64::try_from(choices.len()).ok(),
            Self::Bool => Some(2),
            Self::Ints { min, max, .. } if max < min => Some(0),
            Self::Ints { min, max, .. } => u64::try_from(max - min + 1).ok(),
        }
    }

    fn contains(&self, value: &Value) -> bool {
        match (self, value) {
            (Self::Choices(choices), value) => choices.contains(value),
            (Self::Bool, Value::Bool(_)) => true,
            (
                Self::Ints {
                    min,
                    max,
                    width: None,
                },
                Value::Int(value),
            ) => min <= value && value <= max,
            (
                Self::Ints {
                    min,
                    max,
                    width: Some(width),
                },
                Value::MInt {
                    width: value_width,
                    value,
                },
            ) => {
                let value = num_bigint::BigInt::from(value.clone());
                width == value_width && *min <= value && value <= *max
            }
            _ => false,
        }
    }
}

/// The product of the holes' finite domains (FZ-POLISH N-T1): a campaign whose every hole takes
/// finitely many values (choices, a Boolean, a bounded integer range) has finitely many
/// assignments, and once each has run, more cases only repeat them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FiniteDomain {
    holes: Vec<HoleDomain>,
    size: u64,
}

impl FiniteDomain {
    /// The domain of holes of `sorts` generated under `constraints`, in hole order, when every
    /// hole's is finite and the product is at most [`MAX_EXHAUSTIVE`]; `None` otherwise, and for
    /// a campaign without holes (whose one assignment the anchors run).
    pub(crate) fn of<'a>(
        holes: impl IntoIterator<Item = (&'a ValueSort, &'a Constraints)>,
    ) -> Option<Self> {
        let holes = holes
            .into_iter()
            .map(|(sort, constraints)| HoleDomain::of(sort, constraints))
            .collect::<Option<Vec<_>>>()?;
        if holes.is_empty() {
            return None;
        }
        let mut size = 1_u64;
        for hole in &holes {
            size = size.checked_mul(hole.size()?)?;
            if size > MAX_EXHAUSTIVE {
                return None;
            }
        }
        (size > 0).then_some(Self { holes, size })
    }

    /// Whether `values` (in hole order) is an assignment of the domain.
    fn contains(&self, values: &[Value]) -> bool {
        values.len() == self.holes.len()
            && self
                .holes
                .iter()
                .zip(values)
                .all(|(hole, value)| hole.contains(value))
    }

    /// How many assignments the domain has.
    pub(crate) fn size(&self) -> u64 {
        self.size
    }

    /// The assignment of index `index` (below [`Self::size`]), the holes read as the digits
    /// of a mixed-radix number, the last hole the least significant.
    pub(crate) fn assignment(&self, mut index: u64) -> Vec<Value> {
        let mut values = Vec::with_capacity(self.holes.len());
        for hole in self.holes.iter().rev() {
            let size = hole.size().unwrap_or(1).max(1);
            values.push(hole.value(index % size));
            index /= size;
        }
        values.reverse();
        values
    }

    /// The indices of every assignment in an order drawn from `seed` (Fisher-Yates over a
    /// `ChaCha20` stream of its own purpose), so the walk is part of the determinism contract.
    pub(crate) fn permutation(&self, seed: u64) -> Vec<u64> {
        use rand::{Rng as _, SeedableRng as _};
        let mut rng =
            rand_chacha::ChaCha20Rng::from_seed(super::schedule::derive_seed(seed, "domain"));
        let mut order: Vec<u64> = (0..self.size).collect();
        for last in (1..order.len()).rev() {
            order.swap(last, rng.random_range(0..=last));
        }
        order
    }
}

/// Run cases until the budget is spent, a witness is confirmed and shrunk, the rejection cap
/// is reached, the schedule is exhausted, a case aborts, or `cancel` is cancelled.
///
/// Budget accounting ([`Budget`]): every case is charged its work and at least 1; under
/// `Budget::Work` an execution starts only while the work spent is below the budget, except the
/// confirmation of a candidate, which always runs so that a found candidate is never left
/// unconfirmed. A case whose confirmation fails or disagrees is an engine defect and is counted
/// `unsupported`, never `hit` (ARCHITECTURE 7). The run of every path that judges a witness
/// case's comparability outside its case ([`CaseRunner::comparability`]) is charged after
/// shrinking, when no execution is left for the budget to stop.
pub(crate) fn run_loop(
    runner: &mut dyn CaseRunner,
    schedule: &mut Schedule,
    settings: &LoopSettings,
    budget: Budget,
    cancel: Option<&CancellationToken>,
) -> FuzzReport {
    let mut state = State::new(budget);
    state.warnings.clone_from(&settings.warnings);
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
        let proposal = schedule.next();
        // Work a proposer spent to make the proposal (the solve proposer's symbolic run) is
        // charged before the case runs; the case still runs when it spent the rest of a work
        // budget, so a solved candidate is never dropped unrun.
        state.charge_extra(schedule.take_extra_work());
        let Some(proposal) = proposal else {
            break Ending::Exhausted;
        };
        // An assignment of a finite domain runs at most once (FZ-POLISH N-T1).
        let proposal = state.unrepeated(settings, proposal);
        let case = state.totals.cases;
        state.sequence(&proposal.values);
        let mut run = match run_proposal(runner, &mut state, &proposal, cancel) {
            Ok(run) => run,
            Err(abort) => {
                state.abort = Some(abort.reason);
                break Ending::Aborted;
            }
        };
        state.charge(run.work);
        state.totals.cases += 1;
        state.notes(case, None, &run);
        let mut class = run.class;
        if class == OutcomeClass::Hit {
            match confirm(runner, &mut state, case, &proposal.values, &run, cancel) {
                Confirmed::Agrees(detail) => {
                    state.record(&run, OutcomeClass::Hit);
                    let witness = finish_witness(
                        runner, &mut state, settings, case, proposal, *detail, cancel,
                    );
                    schedule.contribute(&mut state.totals);
                    return state.report(
                        settings,
                        budget,
                        CampaignOutcome::WitnessFound { witness },
                    );
                }
                Confirmed::Cancelled => {
                    // The candidate was not confirmed: a clock-dependent case, whose coverage
                    // the totals do not take, and a trace in the report (ARCHITECTURE 5.4).
                    state.unconfirmed(case, &proposal.values, "was cancelled");
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
                    run.unjudged = Some(UnjudgedReason::Unconfirmed);
                }
                Confirmed::Aborted(reason) => {
                    // The fresh backend failed as every run would: the campaign aborts, and the
                    // candidate stays unconfirmed (ARCHITECTURE 5.3).
                    state.unconfirmed(case, &proposal.values, "aborted");
                    let aborted = CaseRun {
                        unjudged: Some(UnjudgedReason::Unconfirmed),
                        ..run
                    };
                    state.record(&aborted, OutcomeClass::Unsupported);
                    state.abort = Some(reason);
                    break Ending::Aborted;
                }
            }
        }
        state.keep_incidental(case, &mut run, runner);
        state.record(&run, class);
        if is_cancelled(cancel) {
            break Ending::Cancelled;
        }
        let observation = observation(settings, case, class, run);
        state.score(case, observation.score.as_ref());
        let interesting = feedback.is_interesting(&observation);
        schedule.observe(&proposal, &observation, interesting);
        if let Some(assignments) = state.exhausts(settings.domain.as_ref(), &proposal) {
            break Ending::DomainExhausted { assignments };
        }
    };
    schedule.contribute(&mut state.totals);
    let no_witness = no_witness(
        ending,
        &state.totals_snapshot(),
        &state.cuts,
        budget,
        &settings.options,
        settings.rejection_cap,
    );
    let outcome = outcome(ending, no_witness, state.abort.take());
    state.report(settings, budget, outcome)
}

/// The outcome of a campaign that ended without a witness, for `ending`; `abort` is why an
/// aborted one aborted.
fn outcome(ending: Ending, no_witness: NoWitness, abort: Option<String>) -> CampaignOutcome {
    match ending {
        Ending::Budget | Ending::Exhausted | Ending::DomainExhausted { .. } => {
            CampaignOutcome::NoWitnessFound { no_witness }
        }
        Ending::RejectedOut => CampaignOutcome::RejectedOut { no_witness },
        Ending::Cancelled => CampaignOutcome::Cancelled { no_witness },
        Ending::Aborted => CampaignOutcome::Aborted {
            reason: abort.unwrap_or_default(),
            no_witness,
        },
    }
}

/// The observation of case `case` of `class` with `run`'s signals. Only `miss` cases are scored
/// (ARCHITECTURE 6.1, R-18): a bounded or unclean case's coverage stops early, and a rejected
/// case ran nothing.
fn observation(
    settings: &LoopSettings,
    case: u64,
    class: OutcomeClass,
    run: CaseRun,
) -> Observation {
    let signals = Signals {
        applied: &run.applied,
        matched: &run.matched,
        guards: &run.guards,
        progress: run.progress,
    };
    let miss_scorer = settings
        .scorer
        .as_ref()
        .filter(|_| class == OutcomeClass::Miss);
    let blocked = miss_scorer.and_then(|scorer| scorer.blocked(signals));
    let (score, reads) = miss_scorer.map_or((None, Vec::new()), |scorer| {
        let scored = scorer.score(signals);
        (Some(scored.score), scored.reads)
    });
    Observation {
        case,
        class,
        applied: run.applied,
        matched: run.matched,
        applied_counts: run.applied_counts,
        work: run.work,
        score,
        reads,
        blocked,
        comparisons: crate::proposers::runtime::pool(&run.comparisons, &settings.pool_rank),
    }
}

/// Run `proposal` as a case, or, when no complete assignment was drawn (a generator failed),
/// count it as a `rejected` case (`generation`) that is not run, with the generator's message
/// as a warning.
fn run_proposal(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    proposal: &Proposal,
    cancel: Option<&CancellationToken>,
) -> Result<CaseRun, Abort> {
    if let Some(failure) = &proposal.failure {
        state.warn(format!(
            "a generator failed to draw a value and the case was rejected: {failure}"
        ));
        return Ok(CaseRun::rejected(RejectionReason::Generation, 0));
    }
    runner.run_case(&proposal.values, cancel)
}

/// The report of a run that executes no case (an equivalent differential pair, a failed
/// rebuild).
pub(crate) fn report_without_cases(
    settings: &LoopSettings,
    budget: Budget,
    outcome: CampaignOutcome,
) -> FuzzReport {
    let mut state = State::new(budget);
    state.warnings.clone_from(&settings.warnings);
    state.report(settings, budget, outcome)
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
    /// It aborted as every run would (a failed solver prelude on the fresh backend); why.
    Aborted(String),
}

/// Confirm a candidate (ARCHITECTURE 7), charging its work.
///
/// The confirmation's own engine defects (its rule-graph self-check) and warnings are recorded
/// under `case`, whatever the verdict.
fn confirm(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    case: u64,
    values: &[Value],
    candidate: &CaseRun,
    cancel: Option<&CancellationToken>,
) -> Confirmed {
    // Where the target was reached: the state, the side, leaf and (for an observer) hit step,
    // and the kind of kill. Under the determinism contract all of them repeat; a confirmation
    // that differs in any is an engine defect, never the witness's source (ARCHITECTURE 7).
    let reaching = candidate
        .hit
        .as_ref()
        .map(|detail| (detail.reaching_state.clone(), detail.reaching, detail.kill));
    match runner.confirm(values, cancel) {
        Err(failure) => {
            state.charge(0);
            match failure {
                _ if is_cancelled(cancel) => Confirmed::Cancelled,
                ConfirmFailure::Abort(abort) => Confirmed::Aborted(abort.reason),
                ConfirmFailure::Failed(message) => Confirmed::Disagrees(format!(
                    "the case reached the target, but its confirmation failed: {message}"
                )),
            }
        }
        Ok(confirmation) => {
            state.charge(confirmation.work);
            let prefix = format!("confirmation of {}", render(values));
            state.notes(case, Some(&prefix), &confirmation);
            if is_cancelled(cancel) && confirmation.class != OutcomeClass::Hit {
                return Confirmed::Cancelled;
            }
            match confirmation.hit {
                Some(detail)
                    if confirmation.class == OutcomeClass::Hit
                        && reaching.as_ref()
                            == Some(&(
                                detail.reaching_state.clone(),
                                detail.reaching,
                                detail.kill,
                            )) =>
                {
                    Confirmed::Agrees(Box::new(detail))
                }
                Some(_) if confirmation.class == OutcomeClass::Hit => Confirmed::Disagrees(
                    "the case reached the target, but its confirmation reached it in another \
                     configuration, at another leaf or step, or by another kind of kill"
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
    if !settings.options.shrink {
        return Witness {
            label: settings.label,
            krun_command: first.krun_command.clone(),
            mutant_krun_command: first.mutant_krun_command.clone(),
            clean_leaf_facts: witness_facts(&settings.clean_leaf_facts, kind),
            first: judged_case(runner, state, &values, first, cancel),
            shrunk: None,
        };
    }
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
            let prefix = format!("shrink candidate {}", render(candidate));
            state.notes(case, Some(&prefix), &screened);
            // A shrink keeps the witness's kind of kill: a removed end never shrinks into an
            // added one, which is another behaviour (FZ-08 review S1).
            if screened.class != OutcomeClass::Hit
                || screened.hit.as_ref().map(|detail| detail.kill) != Some(kind)
            {
                return Verdict::Miss;
            }
            match confirm(runner, state, case, candidate, &screened, cancel) {
                Confirmed::Agrees(detail) => {
                    last = Some(*detail);
                    Verdict::Hit
                }
                Confirmed::Cancelled => Verdict::Stop,
                Confirmed::Aborted(reason) => {
                    state.warnings.push(format!("shrinking stopped: {reason}"));
                    Verdict::Stop
                }
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
    let (shrunk, krun_command, mutant_krun_command) = match last {
        Some(detail) if shrunk != values => {
            let commands = (
                detail.krun_command.clone(),
                detail.mutant_krun_command.clone(),
            );
            let judged = judged_case(runner, state, &shrunk, detail, cancel);
            (Some(judged), commands.0, commands.1)
        }
        _ => (
            None,
            first.krun_command.clone(),
            first.mutant_krun_command.clone(),
        ),
    };
    Witness {
        label: settings.label,
        first: judged_case(runner, state, &values, first, cancel),
        shrunk,
        clean_leaf_facts: witness_facts(&settings.clean_leaf_facts, kind),
        krun_command,
        mutant_krun_command,
    }
}

/// The witness case a confirmed hit's `detail` with `values` reports, with the comparable
/// judgement its case did not make ([`CaseRunner::comparability`]). That judgement's run is
/// part of no case, and it runs after shrinking: its work goes to the campaign's total alone,
/// so it moves no case's class, determinism or coverage, the case count or shrinking.
fn judged_case(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    values: &[Value],
    detail: HitDetail,
    cancel: Option<&CancellationToken>,
) -> WitnessCase {
    let mut case = witness_case(detail);
    if case.comparable.is_none()
        && let Some((comparable, work)) = runner.comparability(values, cancel)
    {
        state.charge_extra(work);
        case.comparable = Some(comparable);
    }
    case
}

/// The witness case a confirmed hit's detail reports.
fn witness_case(detail: HitDetail) -> WitnessCase {
    WitnessCase {
        holes: detail.holes,
        program: detail.program,
        config_vars: detail.config_vars,
        class: OutcomeClass::Hit,
        sides: detail.sides,
        reaching: detail.reaching,
        kill: detail.kill,
        steps: detail.steps,
        comparable: detail.comparable,
    }
}

/// The facts a witness rests on: the clean-leaf facts of its target, and for a differential
/// witness the conditions of ARCHITECTURE 4.3 for its kind of kill (with D15's requirement that
/// every end of the complete side be data). An end is a clean, decided `stuck` leaf, natural or
/// not (`final`); an undefined step is no end (FZ-DIFFEND).
fn witness_facts(base: &[String], kind: Option<KillKind>) -> Vec<String> {
    let extra: &[&str] = match kind {
        None => &[],
        Some(KillKind::AddedEnd) => &[
            "baseline-complete",
            "every-baseline-end-data",
            "mutant-end-final",
            "mutant-end-data",
            "mutant-end-not-in-baseline-ends",
        ],
        Some(KillKind::RemovedEnd) => &[
            "mutant-complete",
            "every-mutant-end-data",
            "baseline-end-final",
            "baseline-end-data",
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

/// How many cases of one class had a path cut by each kind of bound ([`Cut`]), for the
/// no-witness statement. A case cut by several kinds counts under each.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct CutCounts {
    /// Cases with a path stopped at the depth or breadth bound.
    pub(crate) depth: u64,
    /// Cases with a path stopped at the work bound.
    pub(crate) work: u64,
    /// Cases stopped at the clock.
    pub(crate) clock: u64,
    /// Cases with no path cut by any bound.
    pub(crate) none: u64,
}

impl CutCounts {
    fn add(&mut self, cut: Cut) {
        self.depth += u64::from(cut.depth);
        self.work += u64::from(cut.work);
        self.clock += u64::from(cut.clock);
        self.none += u64::from(!(cut.depth || cut.work || cut.clock));
    }
}

/// The [`CutCounts`] of the two classes whose remedy depends on what cut them.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Cuts {
    /// Of the `reached-unfinished` cases.
    pub(crate) unfinished: CutCounts,
    /// Of the `baseline-incomplete` cases.
    pub(crate) incomplete: CutCounts,
    /// The differential `work-bound` cases whose baseline reached all its ends (FZ-POLISH
    /// S-T5).
    pub(crate) diverging: Diverging,
}

/// The differential `work-bound` cases in which the work bound stopped the mutant while no
/// bound and no clock cut the baseline: the mutant needed more than the bound where the
/// baseline needed at most [`Self::baseline_work`]. Whether the mutant's run ends at all
/// cannot be decided, so the statement reports these facts and suggests no bound.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Diverging {
    /// How many such cases.
    pub(crate) cases: u64,
    /// The largest work the baseline spent in one of them.
    pub(crate) baseline_work: u64,
}

/// The loop's running totals.
struct State {
    budget: Budget,
    totals: Totals,
    /// The canonical JSON of each assignment of [`LoopSettings::domain`] that was tried.
    assignments: BTreeSet<String>,
    /// The seeded permutation of the domain's assignment indices, made on the first repeat,
    /// and how far [`State::unrepeated`] has walked it.
    order: Option<Vec<u64>>,
    next_untried: usize,
    /// The `miss` cases scored, and the best score with the earliest case that reached it
    /// ([`Totals::best_score`]).
    scored: u64,
    best: Option<(Score, u64)>,
    cuts: Cuts,
    load_records: BTreeSet<LoadRecord>,
    warnings: Vec<String>,
    defects: Vec<EngineDefect>,
    abort: Option<String>,
    /// The first `stuck` and the first `undefined` case (FZ-INCIDENTAL).
    incidental: Incidentals,
}

impl State {
    fn new(budget: Budget) -> Self {
        Self {
            budget,
            totals: Totals {
                case_sequence_digest: digest_hex(b""),
                ..Totals::default()
            },
            assignments: BTreeSet::new(),
            order: None,
            next_untried: 0,
            scored: 0,
            best: None,
            cuts: Cuts::default(),
            load_records: BTreeSet::new(),
            warnings: Vec::new(),
            defects: Vec::new(),
            abort: None,
            incidental: Incidentals::default(),
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

    /// Charge work a proposer spent outside cases ([`Schedule::take_extra_work`]), as it is.
    fn charge_extra(&mut self, work: u64) {
        self.totals.work = self.totals.work.saturating_add(work);
    }

    /// Chain one case's values into [`Totals::case_sequence_digest`].
    fn sequence(&mut self, values: &[Value]) {
        let mut bytes = self.totals.case_sequence_digest.clone().into_bytes();
        bytes.push(b'\n');
        bytes.extend(render(values).into_bytes());
        self.totals.case_sequence_digest = digest_hex(&bytes);
    }

    /// Add `warning` to the report unless it already holds the same text.
    fn warn(&mut self, warning: String) {
        if !self.warnings.contains(&warning) {
            self.warnings.push(warning);
        }
    }

    fn defect(&mut self, case: Option<u64>, description: String) {
        self.defects.push(EngineDefect { case, description });
    }

    /// Record `run`'s engine defects under `case`, each after `prefix` when one is given, and
    /// its warnings.
    fn notes(&mut self, case: u64, prefix: Option<&str>, run: &CaseRun) {
        for defect in &run.defects {
            let description = match prefix {
                Some(prefix) => format!("{prefix}: {defect}"),
                None => defect.clone(),
            };
            self.defect(Some(case), description);
        }
        for warning in &run.warnings {
            self.warn(warning.clone());
        }
    }

    /// Count case `case`, a candidate with `values` whose confirmation `ended` without a
    /// verdict, as unconfirmed, with a warning.
    fn unconfirmed(&mut self, case: u64, values: &[Value], ended: &str) {
        self.totals.unconfirmed += 1;
        self.warnings.push(format!(
            "case {case} reached the target with the values {}; its confirmation {ended}, so it \
             is not a witness",
            render(values)
        ));
    }

    /// Keep case `case`'s incidental finding ([`CaseRun::incidental`]) when it is the first of
    /// its class (`stuck` or `undefined`), and tell `runner`, which then describes no later case
    /// of that class. The runner gives a finding only when the run it comes from is inside the
    /// determinism contract, which for a differential case is the baseline's run alone, so the
    /// case's own [`CaseRun::outside_determinism`] (which counts the mutant's run too) is not
    /// read here. Nothing else changes: the class, the counts, the case sequence and the budget
    /// are what they would be without it.
    fn keep_incidental(&mut self, case: u64, run: &mut CaseRun, runner: &mut dyn CaseRunner) {
        let Some((class, mut found)) = run.incidental.take() else {
            return;
        };
        let slot = match class {
            OutcomeClass::Stuck => &mut self.incidental.stuck,
            OutcomeClass::Undefined => &mut self.incidental.undefined,
            _ => return,
        };
        if slot.is_some() {
            return;
        }
        found.case = case;
        *slot = Some(*found);
        runner.incidental_kept(class);
    }

    /// `proposal`, or, when it repeats an assignment of the campaign's finite domain that was
    /// already tried, the next untried assignment in a permutation of the domain seeded from
    /// the campaign seed, proposed by the same proposer without value trees (FZ-POLISH N-T1).
    /// Every case's outcome is a function of its assignment (ARCHITECTURE 5.4), so a repeat
    /// adds nothing; the repeat is not run and is no case, and the proposer observes the
    /// replacement it is credited with, as it would any case of its own.
    fn unrepeated(&mut self, settings: &LoopSettings, proposal: Proposal) -> Proposal {
        let Some(domain) = &settings.domain else {
            return proposal;
        };
        if proposal.failure.is_some()
            || !domain.contains(&proposal.values)
            || !self.assignments.contains(&render(&proposal.values))
        {
            return proposal;
        }
        let order = self
            .order
            .get_or_insert_with(|| domain.permutation(settings.identity.seed));
        while let Some(&index) = order.get(self.next_untried) {
            self.next_untried += 1;
            let values = domain.assignment(index);
            if !self.assignments.contains(&render(&values)) {
                return Proposal::plain(proposal.origin, values);
            }
        }
        proposal
    }

    /// Record that `proposal`'s assignment ran, when it is one of `domain`'s; the number of
    /// the domain's assignments once every one of them has run.
    fn exhausts(&mut self, domain: Option<&FiniteDomain>, proposal: &Proposal) -> Option<u64> {
        let domain = domain?;
        if proposal.failure.is_some() || !domain.contains(&proposal.values) {
            return None;
        }
        self.assignments.insert(render(&proposal.values));
        (u64::try_from(self.assignments.len()).unwrap_or(u64::MAX) >= domain.size())
            .then(|| domain.size())
    }

    /// Take case `case`'s score, when it was scored, into [`Totals::best_score`]: a better score
    /// replaces the best one, an equal one keeps the earlier case.
    fn score(&mut self, case: u64, score: Option<&Score>) {
        let Some(score) = score else {
            return;
        };
        self.scored += 1;
        if self.best.as_ref().is_none_or(|(best, _)| score < best) {
            self.best = Some((score.clone(), case));
        }
    }

    /// Count a case under `class`.
    fn record(&mut self, run: &CaseRun, class: OutcomeClass) {
        *self.totals.classes.entry(class).or_insert(0) += 1;
        match class {
            OutcomeClass::ReachedUnfinished => self.cuts.unfinished.add(run.cut),
            OutcomeClass::BaselineIncomplete => self.cuts.incomplete.add(run.cut),
            OutcomeClass::WorkBound if run.cut.work => {
                if let Some(work) = run.baseline_ended_within {
                    let diverging = &mut self.cuts.diverging;
                    diverging.cases += 1;
                    diverging.baseline_work = diverging.baseline_work.max(work);
                }
            }
            _ => {}
        }
        // `Totals::unsupported_reasons` and `baseline_incomplete_reasons` sum to their classes' counts;
        // every runner gives a reason.
        let reasons = match class {
            OutcomeClass::Unsupported => Some(&mut self.totals.unsupported_reasons),
            OutcomeClass::BaselineIncomplete => Some(&mut self.totals.baseline_incomplete_reasons),
            _ => None,
        };
        if let Some(reasons) = reasons {
            debug_assert!(run.unjudged.is_some(), "an unjudged case without a reason");
            let reason = run.unjudged.unwrap_or(UnjudgedReason::EngineDefect);
            *reasons.entry(reason).or_insert(0) += 1;
        }
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
        if let Some(count) = run.pattern_body_matches {
            let total = self.totals.pattern_body_matches.get_or_insert(0);
            *total = total.saturating_add(count);
        }
        let coverage = &mut self.totals.coverage;
        coverage.applied.extend(run.applied.iter().cloned());
        coverage.matched.extend(run.matched.iter().cloned());
    }

    fn totals_snapshot(&mut self) -> Totals {
        // No case yet: a rate of 0.
        self.totals.rejection_rate_permille = self
            .rejected()
            .saturating_mul(1000)
            .checked_div(self.totals.cases)
            .unwrap_or(0);
        self.totals.clone()
    }

    fn report(
        mut self,
        settings: &LoopSettings,
        budget: Budget,
        outcome: CampaignOutcome,
    ) -> FuzzReport {
        let mut totals = self.totals_snapshot();
        totals.best_score = settings.scorer.as_ref().map(|_| BestScore {
            scored_cases: self.scored,
            best: self.best.as_ref().map(|(score, case)| score.value(*case)),
        });
        let coverage = &mut totals.coverage;
        coverage.names = coverage
            .applied
            .iter()
            .chain(&coverage.matched)
            .filter_map(|id| {
                settings
                    .rule_names
                    .get(id)
                    .map(|name| (id.clone(), name.clone()))
            })
            .collect();
        if totals.pattern_body_matches == Some(0) {
            let judged = totals
                .cases
                .saturating_sub(self.rejected())
                .saturating_sub(totals.outside_determinism);
            self.warn(format!(
                "pattern body: no end of the {judged} executed {} matched the pattern's \
                 configuration, whatever its `requires` gave, so the pattern may name a cell, \
                 key or value no end holds (a misspelled key?); a negated property then holds \
                 vacuously, and a `miss` says nothing about it",
                if judged == 1 { "case" } else { "cases" }
            ));
        }
        if let Some(warning) = every_k_warning(settings.normal_end, &totals) {
            self.warn(warning);
        }
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
            normal_end: settings.normal_end,
            incidental: self.incidental,
            sort_overrides: settings.sort_overrides.clone(),
            warnings: self.warnings,
            definition_findings: settings.definition_findings.clone(),
            engine_defects: self.defects,
        }
    }
}

/// When the every-`<k>` default normal end applied to a definition and some case's class rests
/// on a natural end judgement (`miss`, `stuck`, `hit`, `reached-unfinished`), the warning that
/// says so and how to override it: the default reads only the `<k>` cells, so a semantics that
/// removes a thread on error gives `miss` where its program failed (FZ-UNSUPPORTED review S3).
pub(crate) fn every_k_warning(normal_end: Option<NormalEnds>, totals: &Totals) -> Option<String> {
    let ends = normal_end?;
    let every_k =
        ends.baseline == NormalEndKind::EveryK || ends.mutant == Some(NormalEndKind::EveryK);
    let decided = [
        OutcomeClass::Miss,
        OutcomeClass::Stuck,
        OutcomeClass::Hit,
        OutcomeClass::ReachedUnfinished,
    ]
    .iter()
    .any(|class| totals.classes.get(class).is_some_and(|count| *count > 0));
    (every_k && decided).then(|| {
        "every-k: no normal-end pattern was given and the configuration's <k> cell lies under a \
         multiplicity cell, so a stuck run counted as finished when every <k> cell held .K or \
         no <k> cell was left (the initial configuration having had one); a semantics that \
         removes a thread on error, or leaves a value in a finished thread's <k>, needs a \
         pattern of its finished configuration: campaign key `normal-end-pattern`, command \
         line `--normal-end`, library `CaseOptions::normal_end_pattern`"
            .to_owned()
    })
}

/// The clause of the no-witness statement that counts unjudged cases per reason
/// ([`UnjudgedReason`]), largest first, and gives the largest one's remedy when it has one.
fn reason_clause(text: &mut String, reasons: &std::collections::BTreeMap<UnjudgedReason, u64>) {
    let ranked = ranked_reasons(reasons);
    let Some((top, _)) = ranked.first() else {
        return;
    };
    let counts: Vec<String> = ranked
        .iter()
        .map(|(reason, count)| format!("{count} {}", reason.name()))
        .collect();
    write!(text, " By reason: {}.", counts.join(", ")).expect("writing to a String");
    if let Some(remedy) = top.remedy() {
        write!(text, " For {}: {remedy}.", top.name()).expect("writing to a String");
    }
}

/// `reasons` with their counts, largest count first, ties in [`UnjudgedReason`]'s order.
pub(crate) fn ranked_reasons(
    reasons: &std::collections::BTreeMap<UnjudgedReason, u64>,
) -> Vec<(UnjudgedReason, u64)> {
    let mut ranked: Vec<(UnjudgedReason, u64)> = reasons
        .iter()
        .filter(|(_, count)| **count > 0)
        .map(|(reason, count)| (*reason, *count))
        .collect();
    ranked.sort_by(|(left, left_count), (right, right_count)| {
        right_count.cmp(left_count).then(left.cmp(right))
    });
    ranked
}

/// Why a campaign ended without a witness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Ending {
    /// The budget was spent.
    Budget,
    /// Every proposer was exhausted before the budget.
    Exhausted,
    /// Every one of the `assignments` assignments of the holes' finite domains ran
    /// ([`FiniteDomain`]).
    DomainExhausted {
        /// How many assignments the domain has.
        assignments: u64,
    },
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
#[expect(
    clippy::too_many_lines,
    reason = "one statement, written clause by clause in the order it reads"
)]
pub(crate) fn no_witness(
    ending: Ending,
    totals: &Totals,
    cuts: &Cuts,
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
        Ending::DomainExhausted { assignments } => write!(
            text,
            " Domain exhausted: every one of the {assignments} assignments of the holes' finite \
             domains (each hole's choices, a Boolean, or a bounded integer range, as generated) \
             was tried once (run, or rejected before running), so the campaign ended before its \
             budget; more cases would only repeat them."
        )
        .expect("writing to a String"),
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
        // A case the backend refused ran, to depth 0; every other rejection is decided before
        // the run.
        let refused = totals
            .rejections
            .get(&RejectionReason::BackendRefused)
            .copied()
            .unwrap_or(0)
            .min(rejected);
        if rejected > refused {
            write!(
                text,
                " {} rejected and not run.",
                plural_were(rejected - refused)
            )
            .expect("writing to a String");
        }
        if refused > 0 {
            write!(
                text,
                " {} rejected by the backend, which refused the initial state.",
                plural_were(refused)
            )
            .expect("writing to a String");
        }
    }
    let unsupported = count(OutcomeClass::Unsupported);
    if unsupported > 0 {
        write!(
            text,
            " {} could not be judged (unsupported) and may hide a witness.",
            plural(unsupported, "case")
        )
        .expect("writing to a String");
        reason_clause(&mut text, &totals.unsupported_reasons);
    }
    let incomplete = count(OutcomeClass::BaselineIncomplete);
    if incomplete > 0 {
        write!(
            text,
            " {} had an incomplete baseline, so no kill could be judged.",
            plural(incomplete, "case")
        )
        .expect("writing to a String");
        reason_clause(&mut text, &totals.baseline_incomplete_reasons);
        bound_advice(&mut text, &cuts.incomplete, options, "a baseline path", "");
        if cuts.incomplete.none > 0 {
            write!(
                text,
                " In {} of them no bound cut the baseline: it stopped otherwise, or holds an end \
                 that cannot be compared (undecided, not data, or resting on an \
                 implementation-chosen value), which no bound changes.",
                cuts.incomplete.none
            )
            .expect("writing to a String");
        }
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
    if let Some(solve) = totals
        .solve
        .as_ref()
        .filter(|solve| solve.outside_determinism > 0)
    {
        write!(
            text,
            " {} of the solve proposer's symbolic runs {} outside the determinism contract (an \
             unknown solver answer, a stack stop or a stop by the clock), so a re-run may propose \
             other cases.",
            solve.outside_determinism,
            if solve.outside_determinism == 1 {
                "was"
            } else {
                "were"
            }
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
        PathMode::AllPaths
            if depth + work + timeouts + unsupported + incomplete + unfinished == 0 =>
        {
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
        // A differential case whose baseline ended: the mutant's run needed more than the bound
        // where the baseline's needed little, so the mutant may not end on this program at all,
        // and no larger bound is known to help (FZ-POLISH S-T5).
        let diverging = cuts.diverging.cases.min(work);
        if work > diverging {
            write!(
                text,
                " {} stopped at {bound}: raise max-work.",
                plural(work - diverging, "case")
            )
            .expect("writing to a String");
        }
        if diverging > 0 {
            write!(
                text,
                " {} stopped at {bound} on the mutant, where the baseline reached all its ends \
                 within {} work at most: the mutant may not terminate on this program (whether a \
                 run terminates cannot be decided, so no bound is suggested).",
                plural(diverging, "case"),
                cuts.diverging.baseline_work
            )
            .expect("writing to a String");
        }
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
            " {} reached the target without ending naturally.",
            plural(unfinished, "case")
        )
        .expect("writing to a String");
        bound_advice(
            &mut text,
            &cuts.unfinished,
            options,
            "a path",
            " so that they finish",
        );
        if cuts.unfinished.none > 0 {
            write!(
                text,
                " {} of them stopped abnormally (stuck before a natural end, or at an \
                 undefined step), which no bound changes.",
                cuts.unfinished.none
            )
            .expect("writing to a String");
        }
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

/// The bound advice for the cases of one class whose `what` was cut ([`CutCounts`]): one
/// sentence per kind of bound, naming the bound and what to raise, with `purpose` after it.
fn bound_advice(
    text: &mut String,
    counts: &CutCounts,
    options: &CaseOptions,
    what: &str,
    purpose: &str,
) {
    if counts.depth > 0 {
        let bound = options.max_depth.map_or_else(
            || "its depth or breadth bound".to_owned(),
            |d| format!("max-depth {d}"),
        );
        write!(
            text,
            " In {} of them {what} stopped at {bound}: raise max-depth{purpose}.",
            counts.depth
        )
        .expect("writing to a String");
    }
    if counts.work > 0 {
        let bound = options
            .effective_max_work()
            .map_or_else(|| "its work bound".to_owned(), |w| format!("max-work {w}"));
        write!(
            text,
            " In {} of them {what} stopped at {bound}: raise max-work{purpose}.",
            counts.work
        )
        .expect("writing to a String");
    }
    if counts.clock > 0 {
        let advice = if options.safety_limit_ms.is_some() {
            ": raise the per-case safety limit"
        } else {
            ""
        };
        write!(
            text,
            " In {} of them {what} timed out{advice}.",
            counts.clock
        )
        .expect("writing to a String");
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
