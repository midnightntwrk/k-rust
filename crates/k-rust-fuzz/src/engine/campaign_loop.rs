//! The loop over cases, the budget, confirmation, shrinking and the report (ARCHITECTURE 7,
//! 9.2, 9.3). Owner: FZ-06.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    sync::Arc,
};

use k_rust::backend::CancellationToken;

use super::{
    proposer::{CoverageFeedback, Feedback as _, Observation, Origin, Proposal, ValueShrinker},
    runner::{CaseCrash, CaseRun, CaseRunner, ConfirmFailure, Cut, HitDetail},
    schedule::Schedule,
    shrink::{Verdict, shrink},
};
use crate::{
    crash::{self, MAX_CAMPAIGN_CRASH_SHRINK_RUNS, MAX_CRASH_SHRINK_RUNS, MAX_CRASH_SIGNATURES},
    exec::{Abort, ComparableCondition, NormalEndKind, OutcomeClass, UnjudgedReason},
    filter::{
        FilterRefusal, MAX_CLIENT_REFUSALS, MAX_FAILED_REPAIRS, MAX_REPAIR_CANDIDATES,
        WitnessFilter, is_cause,
    },
    report::{
        AbortKind, BestScore, CampaignOutcome, ClientRefusal, Comparability, CrashDeterminism,
        CrashFinding, CrashFindings, CrashHole, CrashPhase, CrashSignature, CrashStage,
        DivergingTotals, DomainTotals, EngineDefect, FuzzReport, HitLabel, Incidentals, KillKind,
        LoadRecord, NoWitness, NormalEnds, PanicRecord, REPORT_SCHEMA, REPORT_VERSION, ReasonHook,
        ReasonHooks, RejectionReason, RepairedFrom, ReportIdentity, SortOverride, Totals, Witness,
        WitnessCase, describe_reason, digest_hex,
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
    /// Each hole's name, in hole order, which crash findings name their values by.
    pub(crate) hole_names: Vec<String>,
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
    /// Whether the target is differential, for the no-witness statement.
    pub(crate) differential: bool,
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

/// [`run_loop_filtered`] without a filter, for the engine's tests.
#[cfg(test)]
pub(crate) fn run_loop(
    runner: &mut dyn CaseRunner,
    schedule: &mut Schedule,
    settings: &LoopSettings,
    budget: Budget,
    cancel: Option<&CancellationToken>,
) -> FuzzReport {
    run_loop_filtered(runner, schedule, settings, budget, cancel, None)
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
///
/// With the client's witness filter `filter` ([`crate::filter`]), a hit's case is judged before
/// its confirmation and the confirmed case after it; a refused hit is `unsupported`
/// (`client-refused`) and, when shrinking is on, repaired ([`repair`]); every shrink candidate is
/// judged the same way inside the shrink screen. Without a filter no call of the loop changes.
#[expect(
    clippy::too_many_lines,
    reason = "the loop over cases, each case's crash, filter, confirmation and witness in order"
)]
pub(crate) fn run_loop_filtered(
    runner: &mut dyn CaseRunner,
    schedule: &mut Schedule,
    settings: &LoopSettings,
    budget: Budget,
    cancel: Option<&CancellationToken>,
    filter: Option<&mut dyn WitnessFilter>,
) -> FuzzReport {
    let mut state = State::new(budget);
    state.warnings.clone_from(&settings.warnings);
    let mut filtering = match filter.map(Filtering::new).transpose() {
        Ok(filtering) => filtering,
        Err(abort) => {
            state.aborted(abort, 0, settings, &[], false);
            let no_witness = no_witness(
                Ending::Aborted,
                &state.totals_snapshot(),
                &state.cuts,
                budget,
                &settings.options,
                settings.rejection_cap,
                settings.differential,
            );
            let outcome = outcome(Ending::Aborted, no_witness, state.abort.take());
            return state.report(settings, budget, outcome);
        }
    };
    state.filter_id = filtering.as_ref().map(|filtering| filtering.id.clone());
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
        // A proposer's run outside the contract (a solve run the clock or the stack stopped)
        // decided this proposal, so a re-run may differ from this case on (S-C).
        let proposers_outside = schedule.outside_determinism();
        if proposers_outside > state.proposers_outside {
            state.proposers_outside = proposers_outside;
            state
                .totals
                .first_outside_determinism
                .get_or_insert(state.totals.cases);
        }
        // An assignment of a finite domain runs at most once (FZ-POLISH N-T1).
        let mut proposal = state.unrepeated(settings, proposal);
        let case = state.totals.cases;
        state.sequence(&proposal.values);
        let mut run = match run_proposal(runner, &mut state, &proposal, cancel) {
            Ok(run) => run,
            Err(abort) => {
                state.aborted(abort, case, settings, &proposal.values, false);
                break Ending::Aborted;
            }
        };
        state.charge(run.work);
        state.totals.cases += 1;
        state.notes(case, None, &run);
        // A crashed case is a finding, examined before it is counted: its confirmation can put
        // it outside the determinism contract (FZ-CRASH).
        if let Err(halt) = examine(
            runner,
            &mut state,
            settings,
            case,
            &mut proposal,
            &mut run,
            cancel,
        ) {
            let class = run.class;
            state.record(&run, class);
            halt.end(&mut state, settings, case);
            break Ending::Aborted;
        }
        let mut class = run.class;
        // The client's witness filter judges the hit's case before its confirmation, so a refused
        // case costs no confirmation run (FZ-COMPARABLE-B).
        let mut screened_case = None;
        if class == OutcomeClass::Hit
            && let Some(filtering) = filtering.as_mut()
            && let Some(detail) = run.hit.clone()
        {
            let screened = witness_case(detail);
            match filtering.judge(&screened) {
                Err(abort) => {
                    let refused = CaseRun {
                        unjudged: Some(UnjudgedReason::ClientRefused),
                        ..run
                    };
                    state.record(&refused, OutcomeClass::Unsupported);
                    state.aborted(abort, case, settings, &proposal.values, true);
                    break Ending::Aborted;
                }
                Ok(Some(refusal)) => {
                    class = OutcomeClass::Unsupported;
                    run.unjudged = Some(UnjudgedReason::ClientRefused);
                    match refused_hit(
                        runner,
                        &mut state,
                        settings,
                        filtering,
                        &Hit {
                            case,
                            values: &proposal.values,
                            origin: proposal.origin,
                            screened: &screened,
                        },
                        refusal,
                        cancel,
                    ) {
                        Refused::Demoted => {}
                        Refused::Aborted => {
                            state.record(&run, class);
                            break Ending::Aborted;
                        }
                        Refused::Repaired(witness) => {
                            state.keep_incidental(case, &mut run, runner);
                            state.record(&run, class);
                            schedule.contribute(&mut state.totals);
                            return witness_report(state, settings, budget, case, *witness);
                        }
                    }
                }
                Ok(None) => screened_case = Some(screened),
            }
        }
        if class == OutcomeClass::Hit {
            let confirmed = match confirm_noting(
                runner,
                &mut state,
                settings,
                case,
                &proposal.values,
                &run,
                cancel,
            ) {
                Ok(confirmed) => confirmed,
                Err(halt) => {
                    state.unconfirmed(case, &proposal.values, "crashed");
                    let unconfirmed = CaseRun {
                        unjudged: Some(UnjudgedReason::Unconfirmed),
                        ..run
                    };
                    state.record(&unconfirmed, OutcomeClass::Unsupported);
                    halt.end(&mut state, settings, case);
                    break Ending::Aborted;
                }
            };
            match confirmed {
                Confirmed::Agrees(detail) => {
                    // The filter judges the confirmed case too; a refusal wins (review M1).
                    let refused = match (filtering.as_mut(), &screened_case) {
                        (Some(filtering), Some(screened)) => {
                            let confirmed_case = witness_case((*detail).clone());
                            match judge_confirmed(
                                filtering,
                                &mut state,
                                case,
                                screened,
                                &confirmed_case,
                            ) {
                                Ok(refused) => refused,
                                Err(abort) => {
                                    let refused = CaseRun {
                                        unjudged: Some(UnjudgedReason::ClientRefused),
                                        ..run
                                    };
                                    state.record(&refused, OutcomeClass::Unsupported);
                                    state.aborted(abort, case, settings, &proposal.values, true);
                                    break Ending::Aborted;
                                }
                            }
                        }
                        _ => None,
                    };
                    if let Some(refusal) = refused {
                        // Reached only when the confirmation's case differs from the screened
                        // one (an engine defect, recorded by `judge_confirmed`): the hit is
                        // demoted and not repaired, since its two witness cases disagree on what
                        // the filter read and a repair would start from neither reliably.
                        state.refused(settings, case, &proposal.values, &refusal);
                        class = OutcomeClass::Unsupported;
                        run.unjudged = Some(UnjudgedReason::ClientRefused);
                    } else {
                        state.record(&run, OutcomeClass::Hit);
                        let witness = finish_witness(
                            runner,
                            &mut state,
                            settings,
                            case,
                            proposal,
                            *detail,
                            filtering.as_mut(),
                            cancel,
                        );
                        schedule.contribute(&mut state.totals);
                        return witness_report(state, settings, budget, case, witness);
                    }
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
                Confirmed::Outside => {
                    // Another run may confirm it: a clock-dependent case, as a cancelled
                    // confirmation's is, which can change every later case.
                    state.unconfirmed(
                        case,
                        &proposal.values,
                        "ran outside the determinism contract",
                    );
                    class = OutcomeClass::Timeout;
                    run.outside_determinism = true;
                    run.unjudged = None;
                }
                Confirmed::Aborted(abort) => {
                    // The fresh backend failed as every run would: the campaign aborts, and the
                    // candidate stays unconfirmed (ARCHITECTURE 5.3).
                    state.unconfirmed(case, &proposal.values, "aborted");
                    let aborted = CaseRun {
                        unjudged: Some(UnjudgedReason::Unconfirmed),
                        ..run
                    };
                    state.record(&aborted, OutcomeClass::Unsupported);
                    state.aborted(abort, case, settings, &proposal.values, false);
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
    let mut no_witness = no_witness(
        ending,
        &state.totals_snapshot(),
        &state.cuts,
        budget,
        &settings.options,
        settings.rejection_cap,
        settings.differential,
    );
    state.refusal_clause(&mut no_witness);
    let outcome = outcome(ending, no_witness, state.abort.take());
    state.report(settings, budget, outcome)
}

/// The report of a campaign whose witness `witness` (of case `case`) was confirmed: found,
/// unless the client's code (its observer, or its witness filter) failed while the witness was
/// finished, which aborts the campaign with a warning that keeps the confirmed witness's values.
fn witness_report(
    mut state: State,
    settings: &LoopSettings,
    budget: Budget,
    case: u64,
    witness: Witness,
) -> FuzzReport {
    if let Some(abort) = &state.abort {
        // An observer's panic keeps the unfiltered campaign's wording; a failure of the witness
        // filter, which only a filtered campaign has, names the filter.
        let (what, who) = match (abort.filter, abort.kind) {
            (false, _) => (
                "observer panicked",
                "the observer cannot be trusted after its panic",
            ),
            (true, AbortKind::ClientDefect) => (
                "witness filter broke its contract",
                "the filter cannot be trusted after that",
            ),
            (true, _) => (
                "witness filter panicked",
                "the filter cannot be trusted after its panic",
            ),
        };
        let values = witness
            .first
            .holes
            .iter()
            .map(|hole| {
                format!(
                    "{} = {}",
                    hole.name,
                    serde_json::to_string(&hole.value).unwrap_or_default()
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        state.warn(format!(
            "case {case} was a confirmed witness ({values}) when the client's {what} while it \
             was shrunk; {who}, so the campaign aborted, and the witness, confirmed but not \
             shrunk further, is not reported as found"
        ));
        let no_witness = no_witness(
            Ending::Aborted,
            &state.totals_snapshot(),
            &state.cuts,
            budget,
            &settings.options,
            settings.rejection_cap,
            settings.differential,
        );
        let outcome = outcome(Ending::Aborted, no_witness, state.abort.take());
        return state.report(settings, budget, outcome);
    }
    state.report(settings, budget, CampaignOutcome::WitnessFound { witness })
}

/// The client's witness filter, and what the loop keeps about it (FZ-COMPARABLE-B).
pub(crate) struct Filtering<'f> {
    filter: &'f mut dyn WitnessFilter,
    /// The filter's identity ([`WitnessFilter::id`]), for the report.
    id: String,
    /// Per cause, the refused hits whose repair ran candidates and found no witness
    /// ([`MAX_FAILED_REPAIRS`]).
    failed_repairs: BTreeMap<String, u64>,
}

impl<'f> Filtering<'f> {
    /// The loop's handle on `filter`, with its identity.
    ///
    /// # Errors
    ///
    /// A client panic when [`WitnessFilter::id`] panics.
    fn new(filter: &'f mut dyn WitnessFilter) -> Result<Self, Abort> {
        let id = crash::catch(|| filter.id()).map_err(|record| filter_panic("id", record))?;
        Ok(Self {
            filter,
            id,
            failed_repairs: BTreeMap::new(),
        })
    }

    /// The filter's verdict on `case`: `None` when it accepts the case, else its refusal.
    ///
    /// # Errors
    ///
    /// A client panic when the filter panics, and a client defect when its refusal's cause is no
    /// cause token ([`is_cause`]).
    fn judge(&mut self, case: &WitnessCase) -> Result<Option<FilterRefusal>, Abort> {
        match crash::catch(|| self.filter.judge(case)) {
            Ok(Ok(())) => Ok(None),
            Ok(Err(refusal)) if is_cause(&refusal.cause) => Ok(Some(refusal)),
            Ok(Err(refusal)) => Err(filter_defect(format!(
                "the client's witness filter refused a case with the cause {:?}, which is no \
                     cause token (1 to 64 bytes of a-z, 0-9, `-` and `:`)",
                refusal.cause
            ))),
            Err(record) => Err(filter_panic("judge", record)),
        }
    }

    /// The filter's repair candidates for the refused `case` with `values`.
    ///
    /// # Errors
    ///
    /// A client panic when the filter panics.
    fn repair(
        &mut self,
        case: &WitnessCase,
        values: &[Value],
        refusal: &FilterRefusal,
    ) -> Result<Vec<Vec<Value>>, Abort> {
        crash::catch(|| self.filter.repair(case, values, refusal))
            .map_err(|record| filter_panic("repair", record))
    }
}

/// The abort for a panic of the client's witness filter in `call`.
pub(crate) fn filter_panic(call: &str, record: PanicRecord) -> Abort {
    Abort {
        kind: AbortKind::ClientPanic,
        reason: format!(
            "the client's witness filter panicked (phase filter, in `{call}`): {}",
            record.message
        ),
        panic: Some(record),
        filter: true,
    }
}

/// The abort for the client's witness filter breaking its contract (`client-defect`).
fn filter_defect(reason: String) -> Abort {
    Abort {
        filter: true,
        ..Abort::new(AbortKind::ClientDefect, reason)
    }
}

/// The filter's verdict on a confirmed hit whose case it accepted before the confirmation
/// (review M1): `None` when it accepts the confirmed case too, else its refusal, which wins. When
/// the confirmed case differs from the screened one, the difference is one the fuzz's
/// confirmation does not compare (it compares the reaching configuration, leaf and kind of kill),
/// recorded as an engine defect.
///
/// # Errors
///
/// A client defect when the two witness cases are equal (the filter's judgement is then no
/// function of the case), and the filter's own aborts ([`Filtering::judge`]).
fn judge_confirmed(
    filtering: &mut Filtering<'_>,
    state: &mut State,
    case: u64,
    screened: &WitnessCase,
    confirmed: &WitnessCase,
) -> Result<Option<FilterRefusal>, Abort> {
    let Some(refusal) = filtering.judge(confirmed)? else {
        return Ok(None);
    };
    if screened == confirmed {
        return Err(filter_defect(format!(
            "the client's witness filter accepted case {case}'s witness case and refused its \
                 confirmation's, an equal witness case ({}: {}): its judgement is not a function \
                 of the case",
            refusal.cause, refusal.detail
        )));
    }
    state.defect(
        Some(case),
        format!(
            "the confirmation's witness case differs from the case's in what the client's witness \
             filter reads (the confirmation compares the reaching configuration, leaf and kind of \
             kill only), and the filter accepted the case's and refused the confirmation's ({}): \
             the refusal wins",
            refusal.cause
        ),
    );
    Ok(Some(refusal))
}

/// A hit the filter refused: its case, its values, the proposer it came from and the witness case
/// the filter judged.
struct Hit<'a> {
    case: u64,
    values: &'a [Value],
    origin: Origin,
    screened: &'a WitnessCase,
}

/// What became of a hit the filter refused ([`refused_hit`]).
enum Refused {
    /// It stays a refused case (`unsupported`, `client-refused`), and the search goes on.
    Demoted,
    /// A repair candidate became the witness, shrunk.
    Repaired(Box<Witness>),
    /// The campaign aborts (`State::abort` says why).
    Aborted,
}

/// Count the hit the filter refused with `refusal`, and, when the campaign shrinks, repair it
/// ([`repair`]); a repaired witness is shrunk under the filter and names the refused case
/// (`repaired-from`, review M2). Repairing is part of finishing a witness: without shrinking the
/// caller asked for the found case itself as the witness, so a refused hit is only demoted.
fn refused_hit(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    settings: &LoopSettings,
    filtering: &mut Filtering<'_>,
    hit: &Hit<'_>,
    refusal: FilterRefusal,
    cancel: Option<&CancellationToken>,
) -> Refused {
    state.refused(settings, hit.case, hit.values, &refusal);
    if !settings.options.shrink {
        return Refused::Demoted;
    }
    match repair(runner, state, settings, filtering, hit, &refusal, cancel) {
        Repair::None => Refused::Demoted,
        Repair::Aborted => Refused::Aborted,
        Repair::Found(candidate, detail) => {
            state.repaired(&refusal.cause, hit.case);
            let proposal = Proposal::plain(hit.origin, candidate);
            let mut witness = finish_witness(
                runner,
                state,
                settings,
                hit.case,
                proposal,
                *detail,
                Some(filtering),
                cancel,
            );
            witness.repaired_from = Some(RepairedFrom {
                case: hit.case,
                holes: crash_holes(settings, hit.values),
                cause: refusal.cause,
            });
            Refused::Repaired(Box::new(witness))
        }
    }
}

/// What a repair gave ([`repair`]).
enum Repair {
    /// No candidate is a witness, or there was none.
    None,
    /// This candidate is a confirmed witness the filter accepts.
    Found(Vec<Value>, Box<HitDetail>),
    /// The campaign aborts (`State::abort` says why).
    Aborted,
}

/// Repair the refused `hit` (FZ-COMPARABLE-B, S3): the filter's candidates ([`WitnessFilter::
/// repair`]) that differ from the hit's values and from each other, at most
/// [`MAX_REPAIR_CANDIDATES`], each admissible one run as a full case on the campaign's runner and
/// charged as extra work (as a shrink candidate is). The first that hits with the same kind of
/// kill, is accepted, is confirmed and is accepted again is the witness. No candidate runs once a
/// cause's repairs failed [`MAX_FAILED_REPAIRS`] times (review M7): a refusal no input avoids
/// would cost its candidates on every hit.
fn repair(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    settings: &LoopSettings,
    filtering: &mut Filtering<'_>,
    hit: &Hit<'_>,
    refusal: &FilterRefusal,
    cancel: Option<&CancellationToken>,
) -> Repair {
    if filtering
        .failed_repairs
        .get(&refusal.cause)
        .is_some_and(|failed| *failed >= MAX_FAILED_REPAIRS)
    {
        state.totals.filter.repairs_skipped += 1;
        return Repair::None;
    }
    let candidates = match filtering.repair(hit.screened, hit.values, refusal) {
        Ok(candidates) => candidates,
        Err(abort) => {
            state.aborted(abort, hit.case, settings, hit.values, true);
            return Repair::Aborted;
        }
    };
    let mut distinct: Vec<Vec<Value>> = Vec::new();
    for candidate in candidates {
        if distinct.len() == MAX_REPAIR_CANDIDATES {
            break;
        }
        if candidate.len() == hit.values.len()
            && candidate != hit.values
            && !distinct.contains(&candidate)
        {
            distinct.push(candidate);
        }
    }
    // A repair counts, toward `repairs` and toward the cause's failures, only once a candidate
    // runs: proposing nothing, or only inadmissible candidates, costs no run.
    let mut ran = false;
    let kind = hit.screened.kill;
    for candidate in distinct {
        if is_cancelled(cancel) || !state.may_start_extra() || state.abort.is_some() {
            return Repair::None;
        }
        if candidate
            .iter()
            .enumerate()
            .any(|(hole, value)| !runner.admissible(hole, value))
        {
            continue;
        }
        if !ran {
            ran = true;
            state.totals.filter.repairs += 1;
        }
        let before = state.totals.work;
        let outcome = repair_candidate(
            runner, state, settings, filtering, hit.case, &candidate, kind, cancel,
        );
        state.totals.filter.repair_candidates += 1;
        state.totals.filter.repair_work = state
            .totals
            .filter
            .repair_work
            .saturating_add(state.totals.work.saturating_sub(before));
        match outcome {
            Candidate::Witness(detail) => return Repair::Found(candidate, detail),
            Candidate::Aborted => return Repair::Aborted,
            Candidate::Not => {}
        }
    }
    if ran {
        *filtering
            .failed_repairs
            .entry(refusal.cause.clone())
            .or_insert(0) += 1;
    }
    Repair::None
}

/// The verdict on one repair candidate ([`repair_candidate`]).
enum Candidate {
    /// Not a witness.
    Not,
    /// A confirmed witness the filter accepts.
    Witness(Box<HitDetail>),
    /// The campaign aborts (`State::abort` says why).
    Aborted,
}

/// Screen one repair candidate of case `case` as a shrink candidate is screened, under the
/// filter: run it, note its crash (phase `repair`), and require a hit with the kill kind
/// `kind`, accepted by the filter, confirmed, and accepted again.
#[expect(
    clippy::too_many_arguments,
    reason = "the loop's state, the filter, the candidate and its kill kind, and the token"
)]
fn repair_candidate(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    settings: &LoopSettings,
    filtering: &mut Filtering<'_>,
    case: u64,
    candidate: &[Value],
    kind: Option<KillKind>,
    cancel: Option<&CancellationToken>,
) -> Candidate {
    let mut screened = match run_caught(runner, candidate, cancel) {
        Ok(run) => run,
        Err(abort) => {
            state.aborted(abort, case, settings, candidate, false);
            return Candidate::Aborted;
        }
    };
    state.charge(screened.work);
    let prefix = format!("repair candidate {}", render(candidate));
    state.notes(case, Some(&prefix), &screened);
    if let Some(crash) = screened.crash.take() {
        let noted = note_crash(
            runner,
            state,
            settings,
            cancel,
            Found {
                case,
                values: candidate,
                crash: &crash,
                phase: CrashPhase::Repair,
                trees: None,
                poisoned: screened.poisoned,
            },
        );
        return match noted {
            Ok(_) => Candidate::Not,
            Err(halt) => {
                halt.end(state, settings, case);
                Candidate::Aborted
            }
        };
    }
    if screened.poisoned
        && let Err(halt) = recover(runner)
    {
        halt.end(state, settings, case);
        return Candidate::Aborted;
    }
    let Some(detail) = screened
        .hit
        .clone()
        .filter(|detail| screened.class == OutcomeClass::Hit && detail.kill == kind)
    else {
        return Candidate::Not;
    };
    let candidate_case = witness_case(detail);
    match filtering.judge(&candidate_case) {
        Err(abort) => {
            state.aborted(abort, case, settings, candidate, true);
            return Candidate::Aborted;
        }
        Ok(Some(_)) => return Candidate::Not,
        Ok(None) => {}
    }
    let confirmed =
        match confirm_noting(runner, state, settings, case, candidate, &screened, cancel) {
            Ok(confirmed) => confirmed,
            Err(halt) => {
                halt.end(state, settings, case);
                return Candidate::Aborted;
            }
        };
    match confirmed {
        Confirmed::Agrees(detail) => {
            let confirmed_case = witness_case((*detail).clone());
            match judge_confirmed(filtering, state, case, &candidate_case, &confirmed_case) {
                Ok(None) => Candidate::Witness(detail),
                Ok(Some(_)) => Candidate::Not,
                Err(abort) => {
                    state.aborted(abort, case, settings, candidate, true);
                    Candidate::Aborted
                }
            }
        }
        // A repair candidate is no case: a cancelled confirmation, or one whose run was outside
        // the contract, decides only whether the repair is kept.
        Confirmed::Cancelled | Confirmed::Outside => Candidate::Not,
        Confirmed::Aborted(abort) => {
            state.aborted(abort, case, settings, candidate, false);
            Candidate::Aborted
        }
        Confirmed::Disagrees(description) => {
            state.defect(
                Some(case),
                format!("repair candidate {}: {description}", render(candidate)),
            );
            Candidate::Not
        }
    }
}

/// The outcome of a campaign that ended without a witness, for `ending`; `abort` is why an
/// aborted one aborted.
fn outcome(ending: Ending, no_witness: NoWitness, abort: Option<AbortInfo>) -> CampaignOutcome {
    match ending {
        Ending::Budget | Ending::Exhausted | Ending::DomainExhausted { .. } => {
            CampaignOutcome::NoWitnessFound { no_witness }
        }
        Ending::RejectedOut => CampaignOutcome::RejectedOut { no_witness },
        Ending::Cancelled => CampaignOutcome::Cancelled { no_witness },
        Ending::Aborted => {
            let abort = abort.unwrap_or_else(|| AbortInfo {
                kind: AbortKind::RebuildFailed,
                reason: String::new(),
                case: None,
                holes: Vec::new(),
                panic: None,
                filter: false,
            });
            CampaignOutcome::Aborted {
                kind: abort.kind,
                reason: abort.reason,
                case: abort.case,
                holes: abort.holes,
                panic: abort.panic,
                no_witness,
            }
        }
    }
}

/// Why a campaign aborted, for its outcome.
struct AbortInfo {
    kind: AbortKind,
    reason: String,
    case: Option<u64>,
    holes: Vec<CrashHole>,
    panic: Option<PanicRecord>,
    /// The client's witness filter failed ([`Abort::filter`]).
    filter: bool,
}

/// The hole values `values` with the names of `settings`' holes.
fn crash_holes(settings: &LoopSettings, values: &[Value]) -> Vec<CrashHole> {
    values
        .iter()
        .enumerate()
        .map(|(index, value)| CrashHole {
            name: settings
                .hole_names
                .get(index)
                .cloned()
                .unwrap_or_else(|| format!("#{index}")),
            value: value.clone(),
        })
        .collect()
}

/// Why the examination of a crash stopped the loop (FZ-CRASH): the runner did not rebuild
/// after a panic, or a run aborted as every run would or because the client's observer
/// panicked, on `values` in case `case`.
enum Halt {
    /// The runner did not rebuild; why.
    Rebuild(String),
    /// A run aborted, on these values, in this case.
    Abort {
        abort: Abort,
        case: u64,
        values: Vec<Value>,
    },
}

impl Halt {
    /// Make `state` end the campaign for this halt.
    fn end(self, state: &mut State, settings: &LoopSettings, case: u64) {
        match self {
            Self::Rebuild(reason) => state.rebuild_failed(case, &reason),
            Self::Abort {
                abort,
                case,
                values,
            } => state.aborted(abort, case, settings, &values, true),
        }
    }
}

/// Rebuild the campaign's runner after a caught panic ([`CaseRunner::recover`]); a panic of
/// the rebuild itself is a failed rebuild.
fn recover(runner: &mut dyn CaseRunner) -> Result<(), Halt> {
    match crash::catch(|| runner.recover()) {
        Ok(rebuilt) => rebuilt.map_err(Halt::Rebuild),
        Err(record) => Err(Halt::Rebuild(format!(
            "the rebuild panicked: {}",
            record.message
        ))),
    }
}

/// Run one case on the campaign's runner, catching a panic of the engine around the runs (the
/// loop's catch site, FZ-CRASH): such a panic makes the case `unsupported` with the reason
/// `panic` and a crash of the engine, or, for `stacker`'s refusal to map a stack segment, with
/// the reason `stack-mapping-refused` outside the determinism contract and no crash. Either way
/// the runner must be rebuilt.
fn run_caught(
    runner: &mut dyn CaseRunner,
    values: &[Value],
    cancel: Option<&CancellationToken>,
) -> Result<CaseRun, Abort> {
    match crash::catch(|| runner.run_case(values, cancel)) {
        Ok(run) => run,
        Err(record) => Ok(engine_crash_run(record, is_cancelled(cancel))),
    }
}

/// The run of a case whose engine panicked with `record` ([`run_caught`]).
fn engine_crash_run(record: PanicRecord, clock: bool) -> CaseRun {
    let mut run = CaseRun::rejected(RejectionReason::Generation, 0);
    run.class = OutcomeClass::Unsupported;
    run.rejection = None;
    run.poisoned = true;
    if crash::is_stack_mapping_refusal(&record.message) {
        run.unjudged = Some(UnjudgedReason::StackMappingRefused);
        run.outside_determinism = true;
    } else {
        run.unjudged = Some(UnjudgedReason::Panic);
        run.crash = Some(Box::new(CaseCrash::engine(
            record.message,
            record.location,
            clock,
        )));
    }
    run
}

/// Examine case `case`'s run after it ran (FZ-CRASH): note its crash, taking the proposal's
/// value trees for shrinking it, and rebuild the runner when a panic was caught. The crash
/// moves the case outside the determinism contract when it is.
///
/// # Errors
///
/// A [`Halt`]: the runner did not rebuild, or a run that examined the crash aborted. The crash
/// is kept either way.
fn examine(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    settings: &LoopSettings,
    case: u64,
    proposal: &mut Proposal,
    run: &mut CaseRun,
    cancel: Option<&CancellationToken>,
) -> Result<(), Halt> {
    let Some(crash) = run.crash.take() else {
        return if run.poisoned {
            recover(runner)
        } else {
            Ok(())
        };
    };
    let trees = std::mem::replace(
        &mut proposal.trees,
        proposal.values.iter().map(|_| None).collect(),
    );
    let outside = note_crash(
        runner,
        state,
        settings,
        cancel,
        Found {
            case,
            values: &proposal.values,
            crash: &crash,
            phase: CrashPhase::Case,
            trees: Some(trees),
            poisoned: run.poisoned,
        },
    )?;
    run.outside_determinism |= outside;
    Ok(())
}

/// A crash the loop found: in case `case`, on `values` (a candidate's or a shrink candidate's
/// for those phases), in `phase`, with the value trees that shrink it for a case, and whether a
/// panic was caught while it ran, so that the runner must be rebuilt.
struct Found<'a> {
    case: u64,
    values: &'a [Value],
    crash: &'a CaseCrash,
    phase: CrashPhase,
    trees: Option<Vec<Option<Box<dyn ValueShrinker>>>>,
    poisoned: bool,
}

/// Note a crash (FZ-CRASH): count it under its signature, or keep it as the first case of a new
/// signature while fewer than [`MAX_CRASH_SIGNATURES`] are kept, and only then rebuild the
/// runner when a panic was caught, so that a rebuild that fails keeps the crash that made it
/// necessary. A new signature's crash is re-run once on a fresh backend unless the clock stopped
/// its run (`reproduced`, absent when no re-run could be made); a reproduced crash of a case is
/// shrunk under the same signature when the campaign shrinks, and the shrunk values re-run once
/// more (`shrunk-reproduced`). That work is charged to `crash-work` alone. Whether this crash is
/// outside the determinism contract: the clock stopped it, or its re-run did not repeat it.
///
/// # Errors
///
/// A [`Halt`]: the runner did not rebuild after a panic, or a run aborted.
fn note_crash(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    settings: &LoopSettings,
    cancel: Option<&CancellationToken>,
    found: Found<'_>,
) -> Result<bool, Halt> {
    let Found {
        case,
        values,
        crash,
        phase,
        trees,
        poisoned,
    } = found;
    let signature = crash.signature();
    let kept = keep_crash(state, settings, case, values, crash, phase);
    if poisoned {
        recover(runner)?;
    }
    let Some(index) = kept else {
        return Ok(crash.clock);
    };
    if crash.clock {
        return Ok(true);
    }
    let reproduced = confirm_crash(runner, state, case, values, &signature, phase, cancel)?;
    state.crashes[index].reproduced = reproduced;
    match reproduced {
        Some(true) => {}
        Some(false) => {
            state.crashes[index].determinism = CrashDeterminism::Outside;
            return Ok(true);
        }
        None => return Ok(false),
    }
    if phase == CrashPhase::Case
        && settings.options.shrink
        && let Some(trees) = trees
    {
        let shrunk = shrink_crash(
            runner, state, settings, case, values, trees, &signature, cancel,
        )?;
        if shrunk != values {
            let again = confirm_crash(runner, state, case, &shrunk, &signature, phase, cancel)?;
            let entry = &mut state.crashes[index];
            entry.shrunk_holes = Some(crash_holes(settings, &shrunk));
            entry.shrunk_reproduced = again;
        }
    }
    Ok(false)
}

/// Count `crash` under its signature, or keep it as the first case of a new signature while
/// fewer than [`MAX_CRASH_SIGNATURES`] are kept: the new finding's index, `None` otherwise.
/// Only a crash of phase `case` is counted. A finding first kept from another phase is taken
/// over by the first crash of a case with its signature, which then names that case's values
/// and is examined as a case's crash.
fn keep_crash(
    state: &mut State,
    settings: &LoopSettings,
    case: u64,
    values: &[Value],
    crash: &CaseCrash,
    phase: CrashPhase,
) -> Option<usize> {
    let signature = crash.signature();
    let counted = u64::from(phase == CrashPhase::Case);
    let krun_command = crash
        .krun_command
        .as_ref()
        .filter(|_| crash.stage == CrashStage::Execute)
        .map(|line| {
            let note = "expected to reproduce the crash";
            if line.contains("  # ") {
                format!("{line}; {note}")
            } else {
                format!("{line}  # {note}")
            }
        });
    let finding = CrashFinding {
        signature: signature.clone(),
        phase,
        message: crash::bounded_message(&crash.message),
        case,
        holes: crash_holes(settings, values),
        shrunk_holes: None,
        count: counted,
        reproduced: None,
        shrunk_reproduced: None,
        determinism: if crash.clock {
            CrashDeterminism::Outside
        } else {
            CrashDeterminism::Unknown
        },
        clock: crash.clock,
        debug_assertions: cfg!(debug_assertions),
        krun_command,
        program: crash.program.clone(),
        config_vars: crash.config_vars.clone(),
    };
    if let Some(index) = state
        .crashes
        .iter()
        .position(|entry| entry.signature == signature)
    {
        let entry = &mut state.crashes[index];
        if entry.phase != CrashPhase::Case && phase == CrashPhase::Case {
            *entry = finding;
            return Some(index);
        }
        entry.count += counted;
        return None;
    }
    if state.crashes.len() >= MAX_CRASH_SIGNATURES {
        state.crashes_omitted += counted;
        return None;
    }
    state.crashes.push(finding);
    Some(state.crashes.len() - 1)
}

/// Re-run `values` of case `case` once on a fresh backend, charged to `crash-work`: whether it
/// crashed with `signature`, or `None` when no re-run could be made (the fresh backend did not
/// build, the caller cancelled, the runner cannot repeat that phase). A crash of phase
/// `comparability` is re-run through the comparable judgement on fresh cases
/// ([`CaseRunner::confirm_comparability`]), every other through [`CaseRunner::confirm`].
///
/// # Errors
///
/// A [`Halt`]: the runner did not rebuild after a panic of the confirmation's engine, or the
/// confirmation aborted (a failed solver prelude, a panicking observer).
fn confirm_crash(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    case: u64,
    values: &[Value],
    signature: &CrashSignature,
    phase: CrashPhase,
    cancel: Option<&CancellationToken>,
) -> Result<Option<bool>, Halt> {
    let confirmed = crash::catch(|| {
        if phase == CrashPhase::Comparability {
            runner
                .confirm_comparability(values, cancel)
                .map(|judged| judged.map(|judged| (judged.work, judged.crash)))
        } else {
            Some(
                runner
                    .confirm(values, cancel)
                    .map(|mut run| (run.work, run.crash.take())),
            )
        }
    });
    match confirmed {
        Ok(None) => Ok(None),
        Ok(Some(Ok((work, crash)))) => {
            state.charge_crash(work);
            if is_cancelled(cancel) {
                return Ok(None);
            }
            Ok(Some(
                crash.is_some_and(|crash| crash.signature() == *signature),
            ))
        }
        Ok(Some(Err(ConfirmFailure::Failed(_)))) => {
            state.charge_crash(0);
            Ok(None)
        }
        Ok(Some(Err(ConfirmFailure::Abort(abort)))) => {
            state.charge_crash(0);
            Err(Halt::Abort {
                abort,
                case,
                values: values.to_vec(),
            })
        }
        Err(record) => {
            state.charge_crash(0);
            recover(runner)?;
            let crash = CaseCrash::engine(record.message, record.location, is_cancelled(cancel));
            Ok(Some(crash.signature() == *signature))
        }
    }
}

/// Shrink a crash of case `case` on `values` under its `signature` (FZ-CRASH): candidates are
/// screened on the campaign's runner as a hit's are, with their engine defects and warnings
/// recorded, and one that crashes with the same signature is kept; one that crashes otherwise
/// is noted as a crash of phase `shrink` with its own values. At most [`MAX_CRASH_SHRINK_RUNS`]
/// candidates per signature and [`MAX_CAMPAIGN_CRASH_SHRINK_RUNS`] per campaign, each crashing
/// one costing a rebuild.
///
/// # Errors
///
/// A [`Halt`]: the runner did not rebuild (the other crashes found so far are kept), or a
/// candidate's run aborted (a panicking observer, a failed solver prelude), on that
/// candidate's values.
#[expect(
    clippy::too_many_arguments,
    reason = "the loop's state, the crash and its values, and the token"
)]
fn shrink_crash(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    settings: &LoopSettings,
    case: u64,
    values: &[Value],
    trees: Vec<Option<Box<dyn ValueShrinker>>>,
    signature: &CrashSignature,
    cancel: Option<&CancellationToken>,
) -> Result<Vec<Value>, Halt> {
    let mut runs = 0_u64;
    let mut halt: Option<Halt> = None;
    let mut others: Vec<(Vec<Value>, CaseCrash)> = Vec::new();
    let shrunk = {
        let mut test = |candidate: &[Value]| -> Verdict {
            if halt.is_some()
                || is_cancelled(cancel)
                || runs >= MAX_CRASH_SHRINK_RUNS
                || state.crash_shrink_runs >= MAX_CAMPAIGN_CRASH_SHRINK_RUNS
            {
                return Verdict::Stop;
            }
            if candidate
                .iter()
                .enumerate()
                .any(|(hole, value)| !runner.admissible(hole, value))
            {
                return Verdict::Miss;
            }
            runs += 1;
            state.crash_shrink_runs += 1;
            let mut screened = match run_caught(runner, candidate, cancel) {
                Ok(screened) => screened,
                Err(abort) => {
                    halt = Some(Halt::Abort {
                        abort,
                        case,
                        values: candidate.to_vec(),
                    });
                    return Verdict::Stop;
                }
            };
            state.charge_crash(screened.work);
            let prefix = format!("crash shrink candidate {}", render(candidate));
            state.notes(case, Some(&prefix), &screened);
            let verdict = match screened.crash.take() {
                Some(crash) if crash.signature() == *signature => Verdict::Hit,
                Some(crash) => {
                    others.push((candidate.to_vec(), *crash));
                    Verdict::Miss
                }
                None => Verdict::Miss,
            };
            if screened.poisoned
                && let Err(failed) = recover(runner)
            {
                halt = Some(failed);
                return Verdict::Stop;
            }
            verdict
        };
        shrink(values, trees, &settings.constraints, &mut test)
    };
    if let Some(halt) = halt {
        // The crashes found so far are kept, unexamined: no run is made after the halt.
        for (candidate, crash) in &others {
            keep_crash(state, settings, case, candidate, crash, CrashPhase::Shrink);
        }
        return Err(halt);
    }
    for (candidate, crash) in others {
        note_crash(
            runner,
            state,
            settings,
            cancel,
            Found {
                case,
                values: &candidate,
                crash: &crash,
                phase: CrashPhase::Shrink,
                trees: None,
                poisoned: false,
            },
        )?;
    }
    Ok(shrunk)
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
    run_caught(runner, &proposal.values, cancel)
}

/// The report of a run that executes no case (an equivalent differential pair, a failed
/// rebuild).
pub(crate) fn report_without_cases(
    settings: &LoopSettings,
    budget: Budget,
    outcome: CampaignOutcome,
    filter: Option<String>,
) -> FuzzReport {
    let mut state = State::new(budget);
    state.warnings.clone_from(&settings.warnings);
    state.filter_id = filter;
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
    /// It did not hit, and its run was outside the determinism contract (a clock, a solver
    /// `unknown`, a stack stop or an allowance refusal, or a stack segment the host refused): no
    /// engine defect, and the case is outside the contract, since another run may confirm it
    /// (FZ-REPLAY-WHOLE fix round S-C).
    Outside,
    /// It aborted as every run would (a failed solver prelude on the fresh backend), or the
    /// client's observer panicked; why.
    Aborted(Abort),
}

/// [`confirm`], noting a crash of the confirmation as a crash of phase `confirmation` with the
/// candidate's values (FZ-CRASH): a panic of the confirmation's engine (the loop's catch site)
/// leaves the candidate unconfirmed, as a confirmation that failed does.
///
/// # Errors
///
/// A [`Halt`]: the runner did not rebuild after a panic (the crash is kept), or a run that
/// examined the crash aborted.
fn confirm_noting(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    settings: &LoopSettings,
    case: u64,
    values: &[Value],
    candidate: &CaseRun,
    cancel: Option<&CancellationToken>,
) -> Result<Confirmed, Halt> {
    let (confirmed, crash, poisoned) = confirm(runner, state, case, values, candidate, cancel);
    match crash {
        Some(crash) => {
            note_crash(
                runner,
                state,
                settings,
                cancel,
                Found {
                    case,
                    values,
                    crash: &crash,
                    phase: CrashPhase::Confirmation,
                    trees: None,
                    poisoned,
                },
            )?;
        }
        None if poisoned => recover(runner)?,
        None => {}
    }
    Ok(confirmed)
}

/// Confirm a candidate (ARCHITECTURE 7), charging its work, with the confirmation's crash and
/// whether the loop caught a panic of its engine (FZ-CRASH).
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
) -> (Confirmed, Option<Box<CaseCrash>>, bool) {
    // Where the target was reached: the state, the side, leaf and (for an observer) hit step,
    // and the kind of kill. Under the determinism contract all of them repeat; a confirmation
    // that differs in any is an engine defect, never the witness's source (ARCHITECTURE 7).
    let reaching = candidate.hit.as_ref().map(|detail| {
        (
            detail.reaching_state.clone(),
            detail.reaching.clone(),
            detail.kill,
        )
    });
    let confirmed = match crash::catch(|| runner.confirm(values, cancel)) {
        Ok(confirmed) => confirmed,
        Err(record) => {
            state.charge(0);
            let description = format!(
                "the case reached the target, but its confirmation panicked: {}",
                record.message
            );
            if crash::is_stack_mapping_refusal(&record.message) {
                return (Confirmed::Outside, None, true);
            }
            let crash = CaseCrash::engine(record.message, record.location, is_cancelled(cancel));
            return (
                Confirmed::Disagrees(description),
                Some(Box::new(crash)),
                true,
            );
        }
    };
    match confirmed {
        Err(failure) => {
            state.charge(0);
            let confirmed = match failure {
                _ if is_cancelled(cancel) => Confirmed::Cancelled,
                ConfirmFailure::Abort(abort) => Confirmed::Aborted(abort),
                ConfirmFailure::Failed(message) => Confirmed::Disagrees(format!(
                    "the case reached the target, but its confirmation failed: {message}"
                )),
            };
            (confirmed, None, false)
        }
        Ok(mut confirmation) => {
            state.charge(confirmation.work);
            let prefix = format!("confirmation of {}", render(values));
            state.notes(case, Some(&prefix), &confirmation);
            let crash = confirmation.crash.take();
            if is_cancelled(cancel) && confirmation.class != OutcomeClass::Hit {
                return (Confirmed::Cancelled, crash, false);
            }
            let confirmed = match confirmation.hit {
                Some(detail)
                    if confirmation.class == OutcomeClass::Hit
                        && reaching.as_ref()
                            == Some(&(
                                detail.reaching_state.clone(),
                                detail.reaching.clone(),
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
            };
            let confirmed = match confirmed {
                Confirmed::Disagrees(_) if confirmation.outside_determinism => Confirmed::Outside,
                confirmed => confirmed,
            };
            (confirmed, crash, false)
        }
    }
}

/// Shrink a confirmed witness and build the report's witness (ARCHITECTURE 7). With the client's
/// witness filter, every shrink candidate that hits is judged before its confirmation and again
/// after it, and kept only when both judgements accept it (FZ-COMPARABLE-B), so the shrunk
/// witness is one the client accepts.
#[expect(
    clippy::too_many_lines,
    reason = "one shrink test: screening, crash, filter, confirmation and the kept candidate"
)]
#[expect(
    clippy::too_many_arguments,
    reason = "the loop's state, the witness, the filter and the token"
)]
fn finish_witness(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    settings: &LoopSettings,
    case: u64,
    proposal: Proposal,
    first: HitDetail,
    mut filtering: Option<&mut Filtering<'_>>,
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
            first: judged_case(runner, state, settings, case, &values, first, cancel),
            shrunk: None,
            repaired_from: None,
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
            if !state.may_start_extra() || state.rebuild_failure.is_some() || state.abort.is_some()
            {
                return Verdict::Stop;
            }
            runs += 1;
            let mut screened = match run_caught(runner, candidate, cancel) {
                Ok(run) => run,
                Err(abort) => {
                    state.stop_shrinking(
                        case,
                        settings,
                        Halt::Abort {
                            abort,
                            case,
                            values: candidate.to_vec(),
                        },
                    );
                    return Verdict::Stop;
                }
            };
            state.charge(screened.work);
            let prefix = format!("shrink candidate {}", render(candidate));
            state.notes(case, Some(&prefix), &screened);
            // A candidate that crashed is dropped, and noted with its own values before any
            // rebuild (FZ-CRASH).
            if let Some(crash) = screened.crash.take() {
                let noted = note_crash(
                    runner,
                    state,
                    settings,
                    cancel,
                    Found {
                        case,
                        values: candidate,
                        crash: &crash,
                        phase: CrashPhase::Shrink,
                        trees: None,
                        poisoned: screened.poisoned,
                    },
                );
                if let Err(halt) = noted {
                    state.stop_shrinking(case, settings, halt);
                    return Verdict::Stop;
                }
                return Verdict::Miss;
            }
            if screened.poisoned
                && let Err(halt) = recover(runner)
            {
                state.stop_shrinking(case, settings, halt);
                return Verdict::Stop;
            }
            // A shrink keeps the witness's kind of kill: a removed end never shrinks into an
            // added one, which is another behaviour (FZ-08 review S1).
            if screened.class != OutcomeClass::Hit
                || screened.hit.as_ref().map(|detail| detail.kill) != Some(kind)
            {
                return Verdict::Miss;
            }
            // The filter judges the candidate before its confirmation (FZ-COMPARABLE-B).
            let mut candidate_case = None;
            if let Some(filtering) = filtering.as_deref_mut()
                && let Some(detail) = screened.hit.clone()
            {
                let judged = witness_case(detail);
                match filtering.judge(&judged) {
                    Err(abort) => {
                        state.stop_shrinking(
                            case,
                            settings,
                            Halt::Abort {
                                abort,
                                case,
                                values: candidate.to_vec(),
                            },
                        );
                        return Verdict::Stop;
                    }
                    Ok(Some(_)) => {
                        state.totals.filter.refused_shrink_candidates += 1;
                        return Verdict::Miss;
                    }
                    Ok(None) => candidate_case = Some(judged),
                }
            }
            let confirmed =
                match confirm_noting(runner, state, settings, case, candidate, &screened, cancel) {
                    Ok(confirmed) => confirmed,
                    Err(halt) => {
                        state.stop_shrinking(case, settings, halt);
                        return Verdict::Stop;
                    }
                };
            match confirmed {
                Confirmed::Agrees(detail) => {
                    if let (Some(filtering), Some(judged)) =
                        (filtering.as_deref_mut(), &candidate_case)
                    {
                        let confirmed_case = witness_case((*detail).clone());
                        match judge_confirmed(filtering, state, case, judged, &confirmed_case) {
                            Ok(None) => {}
                            Ok(Some(_)) => {
                                state.totals.filter.refused_shrink_candidates += 1;
                                return Verdict::Miss;
                            }
                            Err(abort) => {
                                state.stop_shrinking(
                                    case,
                                    settings,
                                    Halt::Abort {
                                        abort,
                                        case,
                                        values: candidate.to_vec(),
                                    },
                                );
                                return Verdict::Stop;
                            }
                        }
                    }
                    last = Some(*detail);
                    Verdict::Hit
                }
                Confirmed::Cancelled => Verdict::Stop,
                Confirmed::Aborted(abort) => {
                    state.stop_shrinking(
                        case,
                        settings,
                        Halt::Abort {
                            abort,
                            case,
                            values: candidate.to_vec(),
                        },
                    );
                    Verdict::Stop
                }
                Confirmed::Disagrees(description) => {
                    state.defect(
                        Some(case),
                        format!("shrink candidate {}: {description}", render(candidate)),
                    );
                    Verdict::Miss
                }
                // A shrink candidate is no case: its run outside the contract decides only how
                // far the witness shrinks.
                Confirmed::Outside => Verdict::Miss,
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
            let judged = judged_case(runner, state, settings, case, &shrunk, detail, cancel);
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
        first: judged_case(runner, state, settings, case, &values, first, cancel),
        shrunk,
        clean_leaf_facts: witness_facts(&settings.clean_leaf_facts, kind),
        krun_command,
        mutant_krun_command,
        repaired_from: None,
    }
}

/// The witness case a confirmed hit's `detail` with `values` reports, with the comparable
/// judgement its case did not make ([`CaseRunner::comparability`]). That judgement's run is
/// part of no case, and it runs after shrinking: its work goes to the campaign's total alone,
/// so it moves no case's class, determinism or coverage, the case count or shrinking.
///
/// A crash of that run is noted as a crash of phase `comparability` (FZ-CRASH), and the
/// judgement then names the condition `crash`; after a failed rebuild no run is made.
fn judged_case(
    runner: &mut dyn CaseRunner,
    state: &mut State,
    settings: &LoopSettings,
    number: u64,
    values: &[Value],
    detail: HitDetail,
    cancel: Option<&CancellationToken>,
) -> WitnessCase {
    let mut case = witness_case(detail);
    if case.comparable.is_some() || state.abort.is_some() {
        return case;
    }
    if state.rebuild_failure.is_some() {
        // No run is made on a runner that did not rebuild: a judgement it would have made says
        // that a crash stopped it, which no replay compares (`Comparability::reproducible`).
        if runner.comparability_pending() {
            case.comparable = Some(Comparability {
                holds: false,
                reasons: vec![ComparableCondition::Crash],
                hooks: std::collections::BTreeMap::new(),
            });
        }
        return case;
    }
    let judged = match crash::catch(|| runner.comparability(values, cancel)) {
        Ok(judged) => judged,
        Err(record) => {
            let crash = (!crash::is_stack_mapping_refusal(&record.message)).then(|| {
                Box::new(CaseCrash::engine(
                    record.message,
                    record.location,
                    is_cancelled(cancel),
                ))
            });
            let reason = if crash.is_some() {
                ComparableCondition::Crash
            } else {
                ComparableCondition::StackStops
            };
            Some(super::runner::JudgedComparability {
                comparable: Comparability {
                    holds: false,
                    reasons: vec![reason],
                    hooks: std::collections::BTreeMap::new(),
                },
                work: 0,
                crash,
                poisoned: true,
            })
        }
    };
    let Some(judged) = judged else {
        return case;
    };
    state.charge_extra(judged.work);
    case.comparable = Some(judged.comparable);
    let noted = match judged.crash {
        Some(crash) => note_crash(
            runner,
            state,
            settings,
            cancel,
            Found {
                case: number,
                values,
                crash: &crash,
                phase: CrashPhase::Comparability,
                trees: None,
                poisoned: judged.poisoned,
            },
        )
        .map(drop),
        None if judged.poisoned => recover(runner),
        None => Ok(()),
    };
    if let Err(halt) = noted {
        state.stop_shrinking(number, settings, halt);
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
    /// The proposers' runs outside the determinism contract seen so far
    /// ([`Schedule::outside_determinism`]).
    proposers_outside: u64,
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
    abort: Option<AbortInfo>,
    /// The first `stuck` and the first `undefined` case (FZ-INCIDENTAL).
    incidental: Incidentals,
    /// The first case of each crash signature, in the order they were found (FZ-CRASH).
    crashes: Vec<CrashFinding>,
    /// Crashed cases whose signature was not kept.
    crashes_omitted: u64,
    /// The crash shrink candidates screened so far.
    crash_shrink_runs: u64,
    /// Why the runner did not rebuild, once it did not while a witness was finished: no run
    /// is made on it after that.
    rebuild_failure: Option<String>,
    /// The first refused hit of each cause the client's witness filter gave (FZ-COMPARABLE-B).
    client_refusals: Vec<ClientRefusal>,
    /// The client's witness filter's identity, when the campaign runs with one.
    filter_id: Option<String>,
    /// Every hook the cases counted under each `unsupported` reason, then each
    /// `baseline-incomplete` reason, named (UNNAMED-HOOK): [`Totals::unsupported_hooks`] and
    /// [`Totals::baseline_incomplete_hooks`] list the first of each set.
    reason_hooks: [BTreeMap<UnjudgedReason, BTreeSet<ReasonHook>>; 2],
    /// How many of the cases counted under each `unsupported` reason, then each
    /// `baseline-incomplete` reason, named a hook ([`ReasonHooks::cases`]).
    reason_hook_cases: [BTreeMap<UnjudgedReason, u64>; 2],
}

impl State {
    fn new(budget: Budget) -> Self {
        Self {
            budget,
            totals: Totals {
                case_sequence_digest: digest_hex(b""),
                ..Totals::default()
            },
            proposers_outside: 0,
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
            crashes: Vec::new(),
            crashes_omitted: 0,
            crash_shrink_runs: 0,
            rebuild_failure: None,
            reason_hooks: [BTreeMap::new(), BTreeMap::new()],
            reason_hook_cases: [BTreeMap::new(), BTreeMap::new()],
            client_refusals: Vec::new(),
            filter_id: None,
        }
    }

    /// Count case `case`, a hit with `values` the client's witness filter refused with
    /// `refusal`, under its cause, keeping it as the cause's first case while fewer than
    /// [`MAX_CLIENT_REFUSALS`] causes are kept.
    fn refused(
        &mut self,
        settings: &LoopSettings,
        case: u64,
        values: &[Value],
        refusal: &FilterRefusal,
    ) {
        *self
            .totals
            .filter
            .refused
            .entry(refusal.cause.clone())
            .or_insert(0) += 1;
        if let Some(entry) = self
            .client_refusals
            .iter_mut()
            .find(|entry| entry.cause == refusal.cause)
        {
            entry.count += 1;
        } else if self.client_refusals.len() < MAX_CLIENT_REFUSALS {
            self.client_refusals.push(ClientRefusal {
                cause: refusal.cause.clone(),
                detail: refusal.detail.clone(),
                remedy: refusal.remedy.clone(),
                case,
                holes: crash_holes(settings, values),
                count: 1,
                repaired: false,
            });
        }
    }

    /// The refused hit of case `refused`, refused with `cause`, was repaired into the witness: its
    /// entry says so when it is the cause's first refused case (the case `repaired-from` names).
    fn repaired(&mut self, cause: &str, refused: u64) {
        if let Some(entry) = self
            .client_refusals
            .iter_mut()
            .find(|entry| entry.cause == cause && entry.case == refused)
        {
            entry.repaired = true;
        }
    }

    /// When the client's witness filter refused hits of a campaign that ends without a witness,
    /// say so in its statement and in a warning (review M5): every candidate hit was refused, so
    /// the ending is the client's judgement, not survival of the search.
    fn refusal_clause(&mut self, no_witness: &mut NoWitness) {
        let refused: u64 = self.totals.filter.refused.values().sum();
        if refused == 0 {
            return;
        }
        let mut ranked: Vec<(&String, &u64)> = self.totals.filter.refused.iter().collect();
        ranked.sort_by(|(left, left_count), (right, right_count)| {
            right_count.cmp(left_count).then(left.cmp(right))
        });
        let causes = ranked
            .iter()
            .map(|(cause, count)| format!("{count} {cause}"))
            .collect::<Vec<_>>()
            .join(", ");
        let hits = if refused == 1 {
            "1 candidate hit was".to_owned()
        } else {
            format!("{refused} candidate hits were")
        };
        let mut clause = format!(
            " {hits} refused by the client's witness filter, so none is a witness the client \
             accepts (by cause: {causes})."
        );
        if let Some((top, _)) = ranked.first()
            && let Some(remedy) = self
                .client_refusals
                .iter()
                .find(|entry| &entry.cause == *top)
                .and_then(|entry| entry.remedy.as_ref())
        {
            write!(clause, " For {top}: {remedy}.").expect("writing to a String");
        }
        no_witness.statement.push_str(&clause);
        // Every hit was refused only when no hit the filter accepted was lost to its
        // confirmation (a disagreement or a crash of it: `totals.unconfirmed`).
        let lost = self.totals.unconfirmed;
        let warning = if lost == 0 {
            format!(
                "client-refused: the client's witness filter refused every candidate hit of the \
                 campaign ({causes}; the report's client-refusals give each cause's first case): \
                 the campaign ended without a witness the client accepts, which is no sign that \
                 the mutation or property survives"
            )
        } else {
            format!(
                "client-refused: the client's witness filter refused candidate hits of the \
                 campaign ({causes}; the report's client-refusals give each cause's first case), \
                 and {lost} other candidate {} not confirmed (see the engine defects), so one of \
                 them may be a witness the client accepts",
                if lost == 1 { "was" } else { "were" }
            )
        };
        self.warn(warning);
    }

    /// Charge the work of a run that examined a crash to `crash-work` alone, at least 1.
    fn charge_crash(&mut self, work: u64) {
        self.totals.crash_work = self.totals.crash_work.saturating_add(work.max(1));
    }

    /// The campaign aborts for `abort`, in case `case` with `values`: a panicking observer, and
    /// with `name_input` any abort a crash's examination met, names the case and its values.
    fn aborted(
        &mut self,
        abort: Abort,
        case: u64,
        settings: &LoopSettings,
        values: &[Value],
        name_input: bool,
    ) {
        let client = name_input || abort.kind == AbortKind::ClientPanic;
        self.abort = Some(AbortInfo {
            kind: abort.kind,
            reason: abort.reason,
            case: client.then_some(case),
            holes: if client {
                crash_holes(settings, values)
            } else {
                Vec::new()
            },
            panic: abort.panic,
            filter: abort.filter,
        });
    }

    /// The campaign aborts because its runner did not rebuild after a crash at case `case`.
    fn rebuild_failed(&mut self, case: u64, reason: &str) {
        self.abort = Some(AbortInfo {
            kind: AbortKind::RebuildFailed,
            reason: format!(
                "the campaign's backends did not rebuild after a crash at case {case}: {reason}"
            ),
            case: None,
            holes: Vec::new(),
            panic: None,
            filter: false,
        });
    }

    /// While a confirmed witness of case `case` is finished, `halt` stopped a run on `values`:
    /// a runner that did not rebuild stops every later run, with a warning; a panicking observer
    /// aborts the campaign, since the observer cannot be trusted after its panic; any other
    /// abort (a failed solver prelude of a fresh backend) only stops shrinking, with a warning.
    fn stop_shrinking(&mut self, case: u64, settings: &LoopSettings, halt: Halt) {
        match halt {
            Halt::Rebuild(reason) => self.stop_on_failed_rebuild(case, &reason),
            Halt::Abort {
                abort,
                case: at,
                values: on,
            } if matches!(abort.kind, AbortKind::ClientPanic | AbortKind::ClientDefect) => {
                if self.abort.is_none() {
                    self.aborted(abort, at, settings, &on, true);
                }
            }
            Halt::Abort { abort, .. } => {
                self.warn(format!("shrinking stopped: {}", abort.reason));
            }
        }
    }

    /// While a confirmed witness is finished, its runner did not rebuild after a crash: no run
    /// is made on it after this, and a warning says what was not done.
    fn stop_on_failed_rebuild(&mut self, case: u64, reason: &str) {
        if self.rebuild_failure.is_none() {
            self.warn(format!(
                "the campaign's backends did not rebuild after a crash at case {case} ({reason}), \
                 so the witness was not shrunk further and no more runs were made"
            ));
            self.rebuild_failure = Some(reason.to_owned());
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
            OutcomeClass::Unsupported => Some((
                &mut self.totals.unsupported_reasons,
                &mut self.totals.unsupported_hooks,
                &mut self.reason_hooks[0],
                &mut self.reason_hook_cases[0],
            )),
            OutcomeClass::BaselineIncomplete => Some((
                &mut self.totals.baseline_incomplete_reasons,
                &mut self.totals.baseline_incomplete_hooks,
                &mut self.reason_hooks[1],
                &mut self.reason_hook_cases[1],
            )),
            _ => None,
        };
        if let Some((reasons, listed, every, naming)) = reasons {
            debug_assert!(run.unjudged.is_some(), "an unjudged case without a reason");
            let reason = run.unjudged.unwrap_or(UnjudgedReason::EngineDefect);
            *reasons.entry(reason).or_insert(0) += 1;
            // The hooks count under the reason they were read for only while it is the case's
            // reason: the loop may have replaced a candidate hit's.
            if let Some((named, hooks)) = &run.named_hooks
                && *named == reason
            {
                let every = every.entry(reason).or_default();
                every.extend(hooks.iter().cloned());
                let naming = naming.entry(reason).or_insert(0);
                *naming += 1;
                if let Some(mut hooks) = ReasonHooks::of(every) {
                    hooks.cases = *naming;
                    listed.insert(reason, hooks);
                }
            }
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
            // Every record follows its case's count (`run_loop_filtered`), so this case is the last
            // one counted.
            self.totals
                .first_outside_determinism
                .get_or_insert(self.totals.cases.saturating_sub(1));
            return;
        }
        if let Some(count) = run.pattern_body_matches {
            let total = self.totals.pattern_body_matches.get_or_insert(0);
            *total = total.saturating_add(count);
        }
        if run.pattern_body_matches.is_some() {
            let judged = self.totals.pattern_body_judged.get_or_insert(0);
            if run.pattern_body_judged > 0 {
                *judged = judged.saturating_add(1);
            }
        }
        let coverage = &mut self.totals.coverage;
        let before = coverage.applied.len() + coverage.matched.len();
        coverage.applied.extend(run.applied.iter().cloned());
        coverage.matched.extend(run.matched.iter().cloned());
        if coverage.applied.len() + coverage.matched.len() > before {
            // As above, this case is the last one counted.
            self.totals.coverage_last_grew = Some(self.totals.cases.saturating_sub(1));
        }
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
        totals.domain = settings.domain.as_ref().map(|domain| {
            let tried = u64::try_from(self.assignments.len()).unwrap_or(u64::MAX);
            DomainTotals {
                assignments: domain.size(),
                tried,
                exhausted: tried >= domain.size(),
            }
        });
        let diverging = self.cuts.diverging;
        totals.diverging = (diverging.cases > 0).then_some(DivergingTotals {
            cases: diverging.cases,
            baseline_work: diverging.baseline_work,
        });
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
        // Only a case with an end judged against the pattern's configuration can show that no
        // end holds it: a case whose every end is unclean (a chosen value, a contradicted claim,
        // an unsupported hook, ...) judged none, and its `unsupported` reason says why.
        let judged = totals.pattern_body_judged.unwrap_or(0);
        if totals.pattern_body_matches == Some(0) && judged > 0 {
            let executed = totals
                .cases
                .saturating_sub(self.rejected())
                .saturating_sub(totals.outside_determinism);
            let unjudged = executed.saturating_sub(judged);
            let others = if unjudged > 0 {
                format!(
                    " ({unjudged} other executed {} had no end clean enough to judge; their \
                     classes and reasons say why)",
                    if unjudged == 1 { "case" } else { "cases" }
                )
            } else {
                String::new()
            };
            self.warn(format!(
                "pattern body: no end of the {judged} executed {} whose ends were judged matched \
                 the pattern's configuration, whatever its `requires` gave{others}, so the \
                 pattern may name a cell, key or value no end holds (a misspelled key?); a \
                 negated property then holds vacuously, and a `miss` says nothing about it",
                if judged == 1 { "case" } else { "cases" }
            ));
        }
        if let Some(warning) = every_k_warning(settings.normal_end, &totals) {
            self.warn(warning);
        }
        if let Some(solve) = totals.solve.as_ref().filter(|solve| solve.panicked > 0) {
            self.warn(format!(
                "the solve proposer's query panicked {} {} (a k-rust defect; no concrete input)",
                solve.panicked,
                if solve.panicked == 1 { "time" } else { "times" }
            ));
        }
        FuzzReport {
            schema: REPORT_SCHEMA.into(),
            version: REPORT_VERSION,
            identity: ReportIdentity {
                budget,
                filter: self.filter_id,
                ..settings.identity.clone()
            },
            outcome,
            totals,
            load_records: self.load_records.into_iter().collect(),
            normal_end: settings.normal_end,
            incidental: self.incidental,
            crashes: CrashFindings(self.crashes),
            crashes_omitted: self.crashes_omitted,
            client_refusals: self.client_refusals,
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
/// ([`UnjudgedReason`]), largest first, each with the hooks its cases named (UNNAMED-HOOK), and
/// gives the largest one's remedy when it has one.
fn reason_clause(
    text: &mut String,
    reasons: &BTreeMap<UnjudgedReason, u64>,
    hooks: &BTreeMap<UnjudgedReason, ReasonHooks>,
) {
    let ranked = ranked_reasons(reasons);
    let Some((top, _)) = ranked.first() else {
        return;
    };
    let counts: Vec<String> = ranked
        .iter()
        .map(|(reason, count)| describe_reason(*reason, *count, hooks.get(reason)))
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
    differential: bool,
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
        Ending::DomainExhausted { assignments } => {
            write!(
                text,
                " Domain exhausted: every one of the {assignments} assignments of the holes' \
                 finite domains (each hole's choices, a Boolean, or a bounded integer range, as \
                 generated) was tried once (run, or rejected before running), so the campaign \
                 ended before its budget; more cases would only repeat them"
            )
            .expect("writing to a String");
            // A case outside the determinism contract, or a candidate whose confirmation
            // disagreed, may end otherwise when it runs again (final review N4).
            let unstable = [
                (
                    totals.outside_determinism,
                    "outside the determinism contract",
                ),
                (totals.unconfirmed, "that reached the target unconfirmed"),
            ]
            .into_iter()
            .filter(|(count, _)| *count > 0)
            .map(|(count, what)| format!("{} {what}", plural(count, "case")))
            .collect::<Vec<_>>();
            if unstable.is_empty() {
                text.push('.');
            } else {
                write!(
                    text,
                    ", except the {}, which may end otherwise on another run.",
                    unstable.join(" and the ")
                )
                .expect("writing to a String");
            }
        }
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
            // Only the baseline's refusal rejects a differential case: a mutant that refuses the
            // state is `unsupported` (`mutant-refused-state`), and one whose state has no
            // instance has the empty set of ends, which is compared (final review S1).
            let backend = if differential {
                "the baseline's backend"
            } else {
                "the backend"
            };
            write!(
                text,
                " {} rejected by {backend}, which refused the initial state (it is no state of \
                 that definition).",
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
        reason_clause(
            &mut text,
            &totals.unsupported_reasons,
            &totals.unsupported_hooks,
        );
    }
    let incomplete = count(OutcomeClass::BaselineIncomplete);
    if incomplete > 0 {
        write!(
            text,
            " {} had an incomplete baseline, so no kill could be judged.",
            plural(incomplete, "case")
        )
        .expect("writing to a String");
        reason_clause(
            &mut text,
            &totals.baseline_incomplete_reasons,
            &totals.baseline_incomplete_hooks,
        );
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
            " {} outside the determinism contract (a clock, a solver `unknown`, a stop for lack of \
             stack or an allowance refusal decided {}): such a case may end otherwise on another \
             run.",
            plural_were(totals.outside_determinism),
            if totals.outside_determinism == 1 {
                "it"
            } else {
                "them"
            },
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
    if let Some(case) = totals.first_outside_determinism {
        write!(
            text,
            " Every case depends on the cases before it, so a re-run with the same inputs \
             reproduces this report only up to case {case}, the first case outside the contract or \
             proposed after such a solve run, and may differ from it on."
        )
        .expect("writing to a String");
    }
    let depth = count(OutcomeClass::DepthBound);
    let work = count(OutcomeClass::WorkBound);
    let timeouts = count(OutcomeClass::Timeout);
    let unfinished = count(OutcomeClass::ReachedUnfinished);
    // What each side explored (final review N3): a differential baseline always runs every
    // path, and a rejected input none.
    match options.paths {
        PathMode::OnePath if differential => text.push_str(
            " The baseline was run on every path of each input and the mutant on k-rust's \
             first-applicable path only (one-path mode), or on every path where only a removed \
             end could still kill; the all-paths option runs the mutant on every path.",
        ),
        PathMode::OnePath => text.push_str(
            " Only k-rust's first-applicable path of each input was explored (one-path mode); \
             the all-paths option explores every path.",
        ),
        PathMode::AllPaths
            if depth + work + timeouts + unsupported + incomplete + unfinished == 0 =>
        {
            if rejected > 0 {
                text.push_str(
                    " Every path of each input that was not rejected was explored (all-paths \
                     mode).",
                );
            } else {
                text.push_str(" Every path of each input was explored (all-paths mode).");
            }
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
            " {} stopped at {bound}: raise max-depth{TERMINATES}.",
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
                " {} stopped at {bound}: raise max-work{TERMINATES}.",
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
    // Where coverage stopped growing (GUIDE-USABILITY 3): a sound hint that more cases of this
    // program are unlikely to help, which claims no unreachability.
    if let Some(last) = totals.coverage_last_grew
        && ending == Ending::Budget
        && last.saturating_add(1) < totals.cases
    {
        write!(
            text,
            " No case after case {last} (counted from 0) reached a rule that no earlier case \
             reached{}, so more cases of this program and these holes are unlikely to reach \
             others; that is no proof that none can, and a template that holds the target's \
             construct may.",
            if differential { " in the mutant" } else { "" }
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
            " In {} of them {what} stopped at {bound}: raise max-depth{purpose}{TERMINATES}.",
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
            " In {} of them {what} stopped at {bound}: raise max-work{purpose}{TERMINATES}.",
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

/// The condition of the advice to raise a depth or work bound (GUIDE-USABILITY 2): whether a
/// run ends cannot be decided, and a hole value can make the program itself loop (a loop whose
/// step a hole sets to 0), so a larger bound helps only a program that ends on those values.
const TERMINATES: &str = " if the program ends on those values (a hole value can make it loop, \
                          which no bound changes)";

/// "1 case was" or "N cases were".
fn plural_were(count: u64) -> String {
    if count == 1 {
        "1 case was".to_owned()
    } else {
        format!("{count} cases were")
    }
}
