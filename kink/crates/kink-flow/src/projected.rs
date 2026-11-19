//! Kills judged under each projection `run` lists (projections package, PJ-11; `[run]
//! projections`, [`crate::FlowManifest::run_projections`]).
//!
//! `run`'s search compares every mutant with the baseline by the run's own slots: the exit stop,
//! the record's cells (the union of the cells the declared projections compare, every observable
//! cell when one keeps them all) and every channel of `[observe]`. A projection observes a
//! function of what those slots compare: some of the record's cells, functions of those cells
//! evaluated in one fixed observer (`views`, `observer`), some of the channels. So a difference
//! under an `end` or `trace` projection is a difference under the run's slots, and an agreement
//! of the run's slots is an agreement under it; such a projection can turn a kill into a
//! survival, never the reverse. An `accepts` projection is the exception: under `[stop]` whether
//! an end is accepted depends on how a path reached it (`halt`), which no slot compares.
//!
//! How each listed projection is judged ([`Judge`]):
//!
//! - A projection whose observation is the run's own ([`Judge::Run`]: kind `end`, no `views` or
//!   `observer`, the record's cells, every `[observe]` channel) takes the row's status, killer
//!   and reason as they are: the runner's slot verdict is its verdict, one-sided kills included.
//!   The implicit `default` of a flow that declares no projection is judged by nothing in this
//!   module: such a flow's rows carry no `projections` member at all.
//! - Any other `end` or `trace` projection is judged flow-side per executed program
//!   ([`verdict`]), from the run's slot outcomes and, where the run's cells slot distinguished
//!   and the projection reads cells, from the two sides' ends: the baseline's as its record keeps
//!   them, the mutant's as the live call's evidence or the mutant ends store holds them
//!   ([`crate::mutant_ends`]), compared under the projection's cells and views by the front end
//!   ([`crate::compare::Vocabulary::compare_ends`]), or, in a K flow, natively by the
//!   projection's own cell projection ([`crate::admit::AdmittedSpec::projections`]).
//!   The mutant's ends are compared only where they are every end of its run ([`mutant_side`]),
//!   so a one-sided kill (a run its work budget cut, kink-campaign `OneSided`) is never re-judged
//!   through the projection's cells or views: a one-sided difference of the cells slot is
//!   `unknown` under it. A one-sided difference of the exit stop slot kills under every `end`
//!   projection, which reads that slot as the search does, with no view applied.
//! - An `accepts` projection ([`Judge::Accepts`]) is judged per executed program from the two
//!   sides' ends, whatever the slots say: a program kills under it where the baseline and the
//!   mutant differ in whether they accept it ([`accepts_verdict`]), each side's acceptance by
//!   phase 0's rule (`crate::compare`'s acceptance of a definition's ends: an end reached at the
//!   stop, or of a declared `finished` class, is accepted; one of a declared `refused` class, or
//!   a gap, is rejected). The class of each end is read by the baseline definition's own
//!   declared-end functions (the front end's renderer, `crate::evidence::EndRenderer::
//!   declared_ends`) for both sides, one fixed observer, so an edit of a declared end's function
//!   changes no class. Where the definition declares no `finished` end the projection observes
//!   nothing ([`Judge::Unobservable`], reason [`NO_FINISHED_END`]): every status under it is
//!   `unknown`.
//! - A snapshot projection and a `metric` projection are `compare`'s alone and are never listed
//!   ([`crate::FlowManifest::run_projections`]).
//!
//! The killer under a projection judged per program is its recorded killer while it kills under
//! it, else the first program of its domain in the search order that kills under it (decision U2,
//! per projection); where the run's search stopped before judging a program that decides it, `run`
//! runs the programs it needs (`crate::search`, the search under the projections).
//!
//! Nothing is cached: a verdict under a projection is recomputed from each side's stored raw
//! result on every run (projections package README, "Storage"), so no key names a projection.

use crate::compare::{Acceptance, NotCompared, ends_acceptance, ends_acceptance_of};
use crate::evidence::DeclaredEnd;
use crate::manifest::{FlowManifest, ProjectionKind, ProjectionSection};
use crate::mutant_ends::MutantEnds;
use crate::observed::ResultProjection;
use crate::outcomes::slot_name;
use crate::results::ResultClass;
use k_rust::kore::ast::Pattern;
use kink_campaign::OracleOutcome;
use serde_json::{Map, Value, json};
use std::collections::BTreeSet;

/// The reason of an `accepts` projection's `unknown` status where the definition declares no
/// `finished` end: no end of it can be told accepted from one it has no rule for, so the
/// projection observes nothing (as `compare` refuses an acceptance view there).
pub const NO_FINISHED_END: &str = "no-finished-end";

/// The reason of a `metric` projection under `run`, which never lists one: no side of a run
/// states a metric, which is an implementation's measurement.
pub const METRIC_NOT_OBSERVED: &str = "metric-not-observed";

/// The reason of an `undecided` status: some program of the projection's domain that its
/// decision needs was not judged under it, because a call of the search under the projections
/// failed (a corpus error, which stops the run, or the host's `infrastructure` failure of the
/// mutant or a lowering time limit; any other mutant-scope failure there contradicts the row's
/// own search and is a corpus error, `crate::search`), an event of the host, not a function of the run's inputs.
/// The only `undecided` there is, so a lock keeps the recorded entry over it (`crate::clock`).
pub const PROJECTION_SEARCH: &str = "projection-search";

/// The reason a `run --verify` names, in `lock.failed`, each recorded entry under a projection
/// of a row whose programs decide its status: `--verify` judges no projection, so it neither
/// confirms nor contradicts the entry (`crate::clock`), and `--locked` is `undecided` there.
pub const VERIFY_JUDGES_NO_PROJECTION: &str = "verify-judges-no-projection";

/// An executed entry's verdict under a projection whose domain does not hold its program, as
/// `compare` names a view outside its domain: the program is neither judged nor counted.
pub const OUTSIDE_DOMAIN_VERDICT: &str = "outside-domain";

/// The status of a projection judged flow-side whose programs do not decide it.
pub const UNDECIDED: &str = "undecided";

/// How `run` judges one listed projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Judge {
    /// Its observation is the run's own: the row's verdict is its verdict.
    Run,
    /// Judged flow-side, per executed program ([`verdict`]).
    Flow(FlowJudge),
    /// An `accepts` projection: judged per executed program from both sides' ends
    /// ([`accepts_verdict`]).
    Accepts,
    /// It observes nothing of the flow's runs: every status under it is `unknown` with this
    /// reason, no program is judged or run for it.
    Unobservable(&'static str),
}

/// What a projection judged flow-side reads of a run's slots.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlowJudge {
    /// The exit stop (slot 0): every `end` projection reads it, a `trace` projection does not.
    pub stop: bool,
    /// The record's cells (slot 1), re-judged under the projection's cells and views.
    pub cells: bool,
    /// The channels it reads of the observation slot (slot 2).
    pub channels: Channels,
}

/// The channels of `[observe]` a projection reads.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Channels {
    None,
    /// Every channel: the observation slot's verdict is its verdict.
    All,
    /// Some channels, by name: a difference the slot locates on one of them kills, one it locates
    /// elsewhere decides nothing.
    Some(Vec<String>),
}

impl Judge {
    /// How `run` judges `projection` of `manifest`.
    #[must_use]
    pub fn of(projection: &ProjectionSection, manifest: &FlowManifest) -> Self {
        let every = manifest
            .observe
            .as_ref()
            .map(|observe| observe.channel_names().collect::<BTreeSet<_>>())
            .unwrap_or_default();
        let named = projection
            .channels
            .iter()
            .flatten()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let channels = if named.is_empty() {
            Channels::None
        } else if named == every {
            Channels::All
        } else {
            Channels::Some(projection.channels.clone().unwrap_or_default())
        };
        match projection.kind {
            ProjectionKind::Accepts => Self::Accepts,
            // Never listed (`FlowManifest::run_projections`, the `[run] projections` refusal):
            // a metric is an implementation's, and no side of `run` states one.
            ProjectionKind::Metric => Self::Unobservable(METRIC_NOT_OBSERVED),
            ProjectionKind::Trace => Self::Flow(FlowJudge {
                stop: false,
                cells: false,
                channels,
            }),
            ProjectionKind::End => {
                // The record's cells: every observable cell for a projection without `compare`
                // when nothing narrows the record; else as many cells as the record keeps, which,
                // since the record is the union of the projections' cells and a projection names
                // no cell twice, are the record's cells. A front end that reads a cell under two
                // spellings keeps that: krs refuses one projection naming a cell by its path and
                // its K name (`result-cell-repeated`) and keeps each bound cell once in the
                // record, before the manifest reaches `run` (krs-cli `kink::cells::bind`).
                let record = match (&projection.compare, &manifest.record_cells) {
                    (None, None) => true,
                    (Some(compare), Some(kept)) => compare.len() == kept.len(),
                    _ => false,
                };
                let every_channel = named == every;
                if record && every_channel && !projection.has_front_end_keys() {
                    Self::Run
                } else {
                    Self::Flow(FlowJudge {
                        stop: true,
                        cells: true,
                        channels,
                    })
                }
            }
        }
    }
}

/// The verdict of one executed program under one projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Verdict {
    /// A slot the projection reads proves a difference of its observed values.
    Killed,
    /// Every slot the projection reads agrees.
    Agree,
    /// Some slot it reads is undecided under it: why.
    Unknown(String),
}

impl Verdict {
    /// The verdict as an executed entry's `projections` names it.
    #[must_use]
    pub const fn name(&self) -> &'static str {
        match self {
            Self::Killed => "killed",
            Self::Agree => "agree",
            Self::Unknown(_) => "unknown",
        }
    }

    /// The verdict of a test's slot `outcomes` under the run's own observation: killed when some
    /// slot distinguishes (kink-campaign kills through one), agree when every slot agrees.
    #[must_use]
    pub fn of_run(outcomes: &[OracleOutcome]) -> Self {
        if outcomes.contains(&OracleOutcome::Distinguish) {
            Self::Killed
        } else if let Some(other) = outcomes.iter().find(|o| **o != OracleOutcome::Agree) {
            Self::Unknown(format!("a slot of the run is `{}`", slot_name(*other)))
        } else {
            Self::Agree
        }
    }
}

/// The slot names of the reasons, by slot index.
const SLOTS: [&str; 3] = ["exit-stop", "cells", "observations"];

/// The verdict under `judge` of a test whose slot outcomes are `outcomes` (the end slots, then
/// the observation slot under `[observe]`), whose observation slot, where it distinguished,
/// located the first difference on `channel`; `cells` re-judges the cells slot under the
/// projection from the two sides' ends, asked only where that slot distinguished and nothing else
/// the projection reads kills, and is `None` where the mutant's ends are not at hand (a program
/// tier 1 decided with no ends record): the program is then not judged under the projection.
pub fn verdict(
    judge: &FlowJudge,
    outcomes: &[OracleOutcome],
    channel: Option<&str>,
    cells: impl FnOnce() -> Option<Verdict>,
) -> Option<Verdict> {
    let slot = |index: usize| outcomes.get(index).copied();
    let unknown = |index: usize, outcome: Option<OracleOutcome>| {
        Verdict::Unknown(match outcome {
            Some(outcome) => format!("the {} slot is `{}`", SLOTS[index], slot_name(outcome)),
            None => format!("the run has no {} slot", SLOTS[index]),
        })
    };
    let plain = |index: usize| match slot(index) {
        Some(OracleOutcome::Agree) => Verdict::Agree,
        Some(OracleOutcome::Distinguish) => Verdict::Killed,
        other => unknown(index, other),
    };
    let mut read = Vec::new();
    if judge.stop {
        read.push(plain(0));
    }
    match &judge.channels {
        Channels::None => {}
        Channels::All => read.push(plain(2)),
        Channels::Some(names) => read.push(match slot(2) {
            Some(OracleOutcome::Agree) => Verdict::Agree,
            Some(OracleOutcome::Distinguish) => match channel {
                Some(at) if names.iter().any(|name| name == at) => Verdict::Killed,
                Some(at) => Verdict::Unknown(format!(
                    "the observations slot differs first on channel `{at}`, which the projection \
                     does not read; whether its channels differ is not recorded"
                )),
                None => Verdict::Unknown(
                    "the observations slot differs at no recorded channel".to_owned(),
                ),
            },
            other => unknown(2, other),
        }),
    }
    if judge.cells && !read.contains(&Verdict::Killed) {
        read.push(match slot(1) {
            Some(OracleOutcome::Agree) => Verdict::Agree,
            Some(OracleOutcome::Distinguish) => cells()?,
            other => unknown(1, other),
        });
    }
    Some(fold(read))
}

/// Killed when one is, else the first unknown, else agree.
fn fold(verdicts: Vec<Verdict>) -> Verdict {
    if verdicts.contains(&Verdict::Killed) {
        return Verdict::Killed;
    }
    verdicts
        .into_iter()
        .find(|verdict| matches!(verdict, Verdict::Unknown(_)))
        .unwrap_or(Verdict::Agree)
}

/// The mutant's ends of `ends` as the baseline's record keeps a program's ends (`result`, the
/// run's second slot: each left-out cell `\top`, the counter erased), when they are every end of
/// the mutant's run and data under the baseline's definition; else why they cannot be compared.
///
/// # Errors
///
/// Why the record's ends are no complete side under the baseline's definition.
pub fn mutant_side(
    ends: &MutantEnds,
    result: &ResultProjection,
) -> Result<BTreeSet<Pattern>, String> {
    whole(ends)?;
    Ok(ends
        .patterns()?
        .iter()
        .map(|end| project(result, end))
        .collect())
}

/// Whether `ends` are every end of the mutant's run, data under the baseline's definition and
/// the reverse ([`mutant_side`]); else why not.
fn whole(ends: &MutantEnds) -> Result<(), String> {
    if let Some(not) = ends.across.mutant {
        return Err(format!(
            "the mutant's ends are not data under the baseline's definition (`{}`)",
            not.as_str()
        ));
    }
    if let Some(not) = ends.across.baseline {
        return Err(format!(
            "the baseline's ends are not data under the mutant's definition (`{}`)",
            not.as_str()
        ));
    }
    if !ends.complete {
        return Err(
            "the mutant's run is not complete (a bound cut a path, a leaf is undecided or an end \
             has a variable): its ends are not every end it has"
                .to_owned(),
        );
    }
    Ok(())
}

/// `end` as `projection`'s slot reads it: its cells left out as `\top`, the counter erased.
#[must_use]
pub fn project(projection: &ResultProjection, end: &Pattern) -> Pattern {
    match projection.cells() {
        Some(cells) => cells.project(end).into_owned(),
        None => k_rust::backend::counter_erased(end).into_owned(),
    }
}

/// The comparison of a K flow's ends under a projection's own second slot (`projection`): both
/// sides projected by it, equal or not as sets. The baseline's ends are its record's, already
/// projected by the record's slot, whose left-out cells the projection leaves out too (its cells
/// are some of the record's), so projecting them again gives what projecting the run's ends
/// would.
#[must_use]
pub fn native_cells(
    projection: &ResultProjection,
    baseline: &BTreeSet<Pattern>,
    mutant: &BTreeSet<Pattern>,
) -> Verdict {
    let side = |ends: &BTreeSet<Pattern>| {
        ends.iter()
            .map(|end| project(projection, end))
            .collect::<BTreeSet<_>>()
    };
    if side(baseline) == side(mutant) {
        Verdict::Agree
    } else {
        Verdict::Killed
    }
}

/// The baseline's acceptance of a program, from its program row (`row`, the results' row: its
/// `class`, its `ends` summaries with `halt` under `[stop]` and `declared` where the definition
/// declares ends, and `undefined_steps` where a path of the run takes one), as `compare` reads
/// the definition's side (`crate::compare::row_acceptance`): only a `comparable` row has ends,
/// and a run that takes an undefined step beside ends it accepts at is not known to accept the
/// program, as on the mutant's side ([`mutant_acceptance`]).
#[must_use]
pub fn baseline_acceptance(row: &Value) -> Acceptance {
    side_of(row).unwrap_or_else(|| crate::compare::row_acceptance(row))
}

/// [`baseline_acceptance`] read from the listed ends alone, with no regard to an undefined step
/// the row states: the grammar reparse's reading (`crate::reparse`), which this rule leaves as it
/// was (FX1: whether it should take the undefined step too is a question to the orchestrator,
/// since it reaches flows without `[[projection]]`).
#[must_use]
pub fn listed_acceptance(row: &Value) -> Acceptance {
    side_of(row)
        .unwrap_or_else(|| ends_acceptance(row["ends"].as_array().map_or(&[][..], Vec::as_slice)))
}

/// The acceptance of a program row that is not `comparable` (it has no end); `None` for one that
/// is.
fn side_of(row: &Value) -> Option<Acceptance> {
    let class = row["class"].as_str().unwrap_or("error");
    if class == ResultClass::ComparablePrefix.as_str() {
        return Some(Acceptance::NotCompared(NotCompared::Undecided(
            "the baseline's run of the program is cut by its bounds before it ends \
             (`comparable-prefix`): whether it accepts the program is not known yet"
                .to_owned(),
        )));
    }
    (class != ResultClass::Comparable.as_str()).then(|| {
        Acceptance::NotCompared(NotCompared::Unreadable(format!(
            "the baseline's run of the program is `{class}`: it has no end"
        )))
    })
}

/// The mutant's acceptance of a program from its ends record (`ends`), by the rule the
/// baseline's side follows ([`baseline_acceptance`], `crate::compare`'s acceptance of a
/// definition's ends), read in the same observer: each end projected as the record's second
/// slot keeps the baseline's (`result`); under `[stop]` (`stop`) an end reached at the stop by
/// some path (the projection of one of the run's stop ends) is accepted, and every other end
/// has the class `declared` gives it, the baseline definition's own functions of its ends (the
/// front end's renderer, `None` where it reads none). An undefined step is no end in kink's
/// record: a run with no listed end has no acceptance, and one that takes an undefined step
/// beside ends it accepts at is not known to accept (an undefined step may reject); one that
/// rejects at every listed end rejects whatever its undefined steps are.
///
/// # Errors
///
/// Why the record is no side: its ends are not every end of the run, or not data under the
/// other definition ([`mutant_side`]), an end does not parse, the run lists no end, or the
/// front end gives no class.
pub fn mutant_acceptance(
    ends: &MutantEnds,
    result: &ResultProjection,
    stop: bool,
    declared: impl FnOnce(&[Pattern]) -> Option<Vec<DeclaredEnd>>,
) -> Result<Acceptance, String> {
    whole(ends)?;
    let projected = ends
        .patterns()?
        .iter()
        .map(|end| project(result, end))
        .collect::<Vec<_>>();
    if projected.is_empty() {
        return Err(
            "the mutant's run lists no end (every path takes an undefined step, which is no end \
             in kink's record): whether it accepts the program is not known"
                .to_owned(),
        );
    }
    let stopped = ends
        .stop_ends
        .iter()
        .filter_map(|&index| projected.get(index))
        .collect::<BTreeSet<_>>();
    let distinct = projected.iter().collect::<BTreeSet<_>>();
    let halt = |end: &Pattern| stop.then(|| stopped.contains(end));
    let mut summaries = distinct
        .iter()
        .map(|end| match halt(end) {
            Some(at_stop) => json!({"halt": if at_stop { "stop" } else { "own" }}),
            None => json!({}),
        })
        .collect::<Vec<_>>();
    let own = distinct
        .iter()
        .enumerate()
        .filter(|(_, end)| halt(end) != Some(true))
        .collect::<Vec<_>>();
    if !own.is_empty() {
        let asked = own
            .iter()
            .map(|(_, end)| (**end).clone())
            .collect::<Vec<_>>();
        let classes = declared(&asked)
            .filter(|classes| classes.len() == asked.len())
            .ok_or_else(|| {
                "the front end reads no declared end of the mutant's ends: whether it accepts \
                 the program is not known"
                    .to_owned()
            })?;
        for ((index, _), class) in own.iter().zip(&classes) {
            class.annotate(&mut summaries[*index]);
        }
    }
    let acceptance = ends_acceptance_of(
        &summaries,
        "the mutant's run",
        "whether it accepts the program is a question of inclusion, which no verdict states",
    )
    .expect("a run with ends has summaries");
    if ends.undefined_steps && acceptance == Acceptance::Accepted {
        return Ok(Acceptance::NotCompared(NotCompared::Undecided(
            "the mutant's run takes an undefined step beside ends it accepts the program at: an \
             undefined step is no end in kink's record, and whether it rejects is not stated, so \
             whether the run accepts the program is not known"
                .to_owned(),
        )));
    }
    Ok(acceptance)
}

/// The verdict under an `accepts` projection of a program whose baseline's acceptance is
/// `baseline` and whose mutant's is `mutant`: killed where both are decided and differ, agree
/// where both are decided and equal, `unknown` with the reason otherwise.
#[must_use]
pub fn accepts_verdict(baseline: &Acceptance, mutant: Result<Acceptance, String>) -> Verdict {
    let decided = |acceptance: &Acceptance| match acceptance {
        Acceptance::Accepted => Ok(true),
        Acceptance::Rejected => Ok(false),
        Acceptance::NotCompared(reason) => Err(reason.detail()),
    };
    match (
        decided(baseline),
        mutant.and_then(|mutant| decided(&mutant)),
    ) {
        (Err(reason), _) | (_, Err(reason)) => Verdict::Unknown(reason),
        (Ok(baseline), Ok(mutant)) if baseline == mutant => Verdict::Agree,
        (Ok(_), Ok(_)) => Verdict::Killed,
    }
}

/// One listed projection's status for one mutation (the run row's `projections` entry).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectionStatus {
    pub name: String,
    /// A status of the run document's (`killed`, `survived`, `unknown`, or the row's own where
    /// no program decides it), or [`UNDECIDED`].
    pub status: String,
    /// The killing program under the projection.
    pub killer: Option<String>,
    pub reason: Option<String>,
}

impl ProjectionStatus {
    /// The row's own status, killer and reason.
    #[must_use]
    pub fn of_row(name: &str, row: &Value) -> Self {
        let text = |key: &str| row[key].as_str().map(str::to_owned);
        Self {
            name: name.to_owned(),
            status: text("status").unwrap_or_else(|| "error".to_owned()),
            killer: text("killer"),
            reason: text("reason"),
        }
    }

    /// The entry as the row's `projections` holds it: `{name, status, killer, reason}`.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "name": self.name,
            "status": self.status,
            "killer": self.killer,
            "reason": self.reason,
        })
    }
}

/// `row` with its `projections` (where it has them) restated from its own status, killer and
/// reason, each entry as a row whose status no program decides has under every projection: for
/// a row whose status is rewritten after its projections were judged (`crate::search`: a
/// corpus error met after the row's search, which makes the row `error`).
pub fn restate(row: &mut Value) {
    let Some(names) = row["projections"].as_array().map(|entries| {
        entries
            .iter()
            .filter_map(|entry| entry["name"].as_str().map(str::to_owned))
            .collect::<Vec<_>>()
    }) else {
        return;
    };
    let entries = names
        .iter()
        .map(|name| ProjectionStatus::of_row(name, row).value())
        .collect::<Vec<_>>();
    row["projections"] = json!(entries);
}

/// An executed entry's `projections`: each projection's verdict of its program, by name
/// ([`Verdict::name`], or [`OUTSIDE_DOMAIN_VERDICT`]).
#[must_use]
pub fn entry_value(verdicts: &[(&str, &str)]) -> Value {
    Value::Object(
        verdicts
            .iter()
            .map(|(name, verdict)| ((*name).to_owned(), json!(verdict)))
            .collect::<Map<_, _>>(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use OracleOutcome::{Agree, Distinguish, Timeout, Unknown};

    fn end(channels: Channels) -> FlowJudge {
        FlowJudge {
            stop: true,
            cells: true,
            channels,
        }
    }

    /// The cells re-judgement is asked only where the cells slot distinguished and nothing else
    /// the projection reads kills; an agreement of every slot is an agreement under every
    /// projection.
    #[test]
    fn a_projection_reads_its_slots_and_rejudges_only_a_cells_difference() {
        let never = || -> Option<Verdict> { panic!("asked") };
        let judge = end(Channels::None);
        assert_eq!(
            verdict(&judge, &[Agree, Agree], None, never),
            Some(Verdict::Agree)
        );
        assert_eq!(
            verdict(&judge, &[Distinguish, Distinguish], None, never),
            Some(Verdict::Killed)
        );
        assert_eq!(
            verdict(&judge, &[Agree, Distinguish], None, || Some(Verdict::Agree)),
            Some(Verdict::Agree)
        );
        assert_eq!(
            verdict(&judge, &[Agree, Distinguish], None, || Some(
                Verdict::Killed
            )),
            Some(Verdict::Killed)
        );
        assert!(matches!(
            verdict(&judge, &[Agree, Timeout], None, never),
            Some(Verdict::Unknown(_))
        ));
        // A kill by the exit stop is a kill whatever the cells slot is.
        assert_eq!(
            verdict(&judge, &[Distinguish, Unknown], None, never),
            Some(Verdict::Killed)
        );
        // A projection reading no channel ignores the observation slot.
        assert_eq!(
            verdict(&judge, &[Agree, Agree, Distinguish], Some("log"), never),
            Some(Verdict::Agree)
        );
    }

    /// A channel subset is killed by a difference the slot locates on one of its channels; one
    /// located elsewhere, or nowhere, decides nothing; a trace projection reads no end slot.
    #[test]
    fn a_channel_subset_is_killed_only_where_the_difference_is_located() {
        let never = || -> Option<Verdict> { panic!("asked") };
        let trace = FlowJudge {
            stop: false,
            cells: false,
            channels: Channels::Some(vec!["log".into()]),
        };
        assert_eq!(
            verdict(
                &trace,
                &[Distinguish, Distinguish, Distinguish],
                Some("log"),
                never
            ),
            Some(Verdict::Killed)
        );
        assert!(matches!(
            verdict(
                &trace,
                &[Distinguish, Distinguish, Distinguish],
                Some("bus"),
                never
            ),
            Some(Verdict::Unknown(_))
        ));
        assert!(matches!(
            verdict(&trace, &[Agree, Agree, Distinguish], None, never),
            Some(Verdict::Unknown(_))
        ));
        assert_eq!(
            verdict(&trace, &[Distinguish, Distinguish, Agree], None, never),
            Some(Verdict::Agree)
        );
        let all = FlowJudge {
            channels: Channels::All,
            ..trace
        };
        assert_eq!(
            verdict(&all, &[Agree, Agree, Distinguish], None, never),
            Some(Verdict::Killed)
        );
    }

    /// Which projection takes the row's verdict, which is judged flow-side, which is not judged.
    #[test]
    fn a_projection_is_judged_by_the_run_only_where_it_observes_what_the_run_does() {
        let judges = |projections: &str| {
            let manifest = FlowManifest::decode(
                &format!(
                    "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\n\n\
                     [[observe.point]]\nname = \"emits\"\nafter = [\"CALC.emit\"]\nstutter = \"count\"\n\
                     cells = [\"out\"]\n\n[[observe.point]]\nname = \"notes\"\n\
                     after = [\"CALC.note\"]\nstutter = \"count\"\ncells = [\"out\"]\n\n{projections}"
                ),
                std::path::Path::new("corpus"),
            )
            .unwrap();
            manifest
                .run_projections()
                .iter()
                .map(|projection| Judge::of(projection, &manifest))
                .collect::<Vec<_>>()
        };
        let both = || Channels::Some(vec!["emits".into()]);
        let flow = |stop, cells, channels| {
            Judge::Flow(FlowJudge {
                stop,
                cells,
                channels,
            })
        };
        // The record's cells and every channel: the run's observation.
        assert_eq!(
            judges(
                "[[projection]]\nname = \"a\"\ncompare = [\"out\", \"k\"]\nchannels = [\"notes\", \"emits\"]\n"
            ),
            [Judge::Run]
        );
        // Fewer channels, fewer cells, views, a trace, an acceptance.
        assert_eq!(
            judges(
                "[[projection]]\nname = \"a\"\ncompare = [\"out\", \"k\"]\nchannels = [\"emits\"]\n\n\
                 [[projection]]\nname = \"b\"\ncompare = [\"out\"]\nchannels = [\"emits\", \"notes\"]\n\n\
                 [[projection]]\nname = \"c\"\ncompare = [\"out\", \"k\"]\nchannels = [\"emits\", \"notes\"]\n\
                 views = { out = \"V\" }\n\n\
                 [[projection]]\nname = \"t\"\nkind = \"trace\"\nchannels = [\"emits\"]\n"
            ),
            [
                flow(true, true, both()),
                flow(true, true, Channels::All),
                flow(true, true, Channels::All),
                flow(false, false, both()),
            ]
        );
        // Without `compare` while another projection keeps every cell: the record's cells.
        assert_eq!(
            judges(
                "[[projection]]\nname = \"w\"\nchannels = [\"emits\", \"notes\"]\n\n\
                 [[projection]]\nname = \"a\"\nkind = \"accepts\"\n\n\
                 [[projection]]\nname = \"o\"\ncompare = [\"out\"]\nchannels = [\"emits\", \"notes\"]\n"
            ),
            [Judge::Run, Judge::Accepts, flow(true, true, Channels::All),]
        );
    }

    /// A one-sided kill (a poll-bound mutant run: its ends record is not complete, its one-sided
    /// ends are the clean ground leaves the runner's rule read) is never re-judged through the
    /// projection's cells or views (PJ-11): the record is no side, so a one-sided difference of
    /// the cells slot is `unknown` under a projection judged flow-side. The exit stop slot is read
    /// as the search reads it, with no view applied, so its one-sided difference kills under every
    /// `end` projection, and a projection taking the search's verdict kills on either slot.
    #[test]
    fn a_one_sided_kill_is_taken_through_the_exit_stop_and_never_through_a_view() {
        use crate::mutant_ends::{Across, MutantEnds};
        use crate::outcomes::RunPolls;
        let leaf = r#"\dv{SortInt{}}("8")"#.to_owned();
        let cut = MutantEnds {
            program_id: "start".into(),
            ends: vec![leaf.clone()],
            stop_ends: Vec::new(),
            one_sided_ends: vec![leaf],
            undefined_steps: false,
            complete: false,
            across: Across::default(),
            polls: RunPolls {
                count: 11_000,
                bound: 11_000,
                cut: true,
            },
        };
        let whole = ResultProjection {
            state: kink_campaign::StateProjection::WholeTerm,
            compared: None,
            not_compared: Vec::new(),
            unobservable: Vec::new(),
        };
        let refused = mutant_side(&cut, &whole).unwrap_err();
        assert!(refused.contains("not complete"), "{refused}");
        // The same ends as every end of a complete run are a side: completeness alone decides.
        let complete = MutantEnds {
            complete: true,
            one_sided_ends: Vec::new(),
            ..cut.clone()
        };
        assert_eq!(mutant_side(&complete, &whole).map(|side| side.len()), Ok(1));
        // A projection with views is judged flow-side: exit stop, cells, no channel.
        let views = end(Channels::None);
        let cells = || Some(Verdict::Unknown(mutant_side(&cut, &whole).unwrap_err()));
        // The common shape: the exit stop slot is `unknown` (the run is cut), the cells slot
        // distinguished one-sidedly.
        assert!(matches!(
            verdict(&views, &[Unknown, Distinguish], None, cells),
            Some(Verdict::Unknown(_))
        ));
        assert!(matches!(
            verdict(&views, &[Agree, Distinguish], None, cells),
            Some(Verdict::Unknown(reason)) if reason.contains("not complete")
        ));
        // A one-sided difference of the exit stop slot: killed, the cells never re-judged.
        let never = || -> Option<Verdict> { panic!("asked") };
        assert_eq!(
            verdict(&views, &[Distinguish, Distinguish], None, never),
            Some(Verdict::Killed)
        );
        // A trace projection reads neither end slot.
        let trace = FlowJudge {
            stop: false,
            cells: false,
            channels: Channels::None,
        };
        assert_eq!(
            verdict(&trace, &[Distinguish, Distinguish], None, never),
            Some(Verdict::Agree)
        );
        // The search's own observation (`Judge::Run`, also folded per program under a `domain`).
        assert_eq!(Verdict::of_run(&[Unknown, Distinguish]), Verdict::Killed);
        assert_eq!(
            Verdict::of_run(&[Distinguish, Distinguish]),
            Verdict::Killed
        );
    }

    /// The cells re-judgement without the mutant's ends leaves the program unjudged.
    #[test]
    fn a_cells_difference_without_the_mutants_ends_is_not_judged() {
        let judge = end(Channels::None);
        assert_eq!(verdict(&judge, &[Agree, Distinguish], None, || None), None);
        assert_eq!(
            verdict(&judge, &[Distinguish, Distinguish], None, || None),
            Some(Verdict::Killed)
        );
    }

    /// A mutant's acceptance by phase 0's rule, its ends classed by the baseline definition's
    /// functions (`declared`), against the baseline's from its program row: a kill where the two
    /// differ in whether they accept, `unknown` where either is not decided.
    #[test]
    fn an_acceptance_is_read_from_both_sides_ends_by_one_rule() {
        use crate::mutant_ends::{Across, MutantEnds};
        use crate::outcomes::RunPolls;
        let leaf = |n: u32| format!(r#"\dv{{SortInt{{}}}}("{n}")"#);
        let ends = |count: u32| MutantEnds {
            program_id: "p".into(),
            ends: (0..count).map(leaf).collect(),
            stop_ends: Vec::new(),
            one_sided_ends: Vec::new(),
            undefined_steps: false,
            complete: true,
            across: Across::default(),
            polls: RunPolls {
                count: 10,
                bound: 100,
                cut: false,
            },
        };
        let whole = ResultProjection {
            state: kink_campaign::StateProjection::WholeTerm,
            compared: None,
            not_compared: Vec::new(),
            unobservable: Vec::new(),
        };
        let finished = || DeclaredEnd::Finished {
            item: "crate::halted".into(),
        };
        let refused = || DeclaredEnd::Refused {
            item: "crate::trapped".into(),
            reason: None,
            text: "1".into(),
        };
        let classes = |classes: Vec<DeclaredEnd>| move |_: &[Pattern]| Some(classes);
        let of = |record: &MutantEnds, stop: bool, declared: Vec<DeclaredEnd>| {
            mutant_acceptance(record, &whole, stop, classes(declared))
        };
        assert_eq!(
            of(&ends(2), false, vec![finished(), finished()]),
            Ok(Acceptance::Accepted)
        );
        assert_eq!(
            of(&ends(2), false, vec![refused(), DeclaredEnd::None]),
            Ok(Acceptance::Rejected)
        );
        assert!(matches!(
            of(&ends(2), false, vec![finished(), refused()]),
            Ok(Acceptance::NotCompared(NotCompared::SeveralEnds(reason)))
                if reason.starts_with("the mutant's run accepts")
        ));
        assert!(matches!(
            of(&ends(1), false, vec![DeclaredEnd::Undecided("open".into())]),
            Ok(Acceptance::NotCompared(NotCompared::Undecided(_)))
        ));
        // Under `[stop]` an end some path reached at the stop is accepted and asks no class;
        // the others have their declared class.
        let stopped = MutantEnds {
            stop_ends: vec![0],
            ..ends(2)
        };
        let asked = |expected: usize, class: DeclaredEnd| {
            move |asked: &[Pattern]| {
                assert_eq!(asked.len(), expected);
                Some(vec![class])
            }
        };
        assert!(matches!(
            mutant_acceptance(&stopped, &whole, true, asked(1, refused())),
            Ok(Acceptance::NotCompared(NotCompared::SeveralEnds(_)))
        ));
        assert_eq!(
            mutant_acceptance(&stopped, &whole, true, asked(1, finished())),
            Ok(Acceptance::Accepted)
        );
        let every = MutantEnds {
            stop_ends: vec![0, 1],
            ..ends(2)
        };
        assert_eq!(
            mutant_acceptance(&every, &whole, true, |_: &[Pattern]| -> Option<Vec<_>> {
                panic!("asked")
            }),
            Ok(Acceptance::Accepted)
        );
        // An undefined step beside listed ends: rejected stays rejected, accepted is not known.
        let undefined = MutantEnds {
            undefined_steps: true,
            ..ends(1)
        };
        assert_eq!(
            of(&undefined, false, vec![refused()]),
            Ok(Acceptance::Rejected)
        );
        assert!(matches!(
            of(&undefined, false, vec![finished()]),
            Ok(Acceptance::NotCompared(NotCompared::Undecided(_)))
        ));
        // No side: no listed end, an incomplete run, no class from the front end.
        let none = MutantEnds {
            undefined_steps: true,
            ..ends(0)
        };
        assert!(
            of(&none, false, Vec::new())
                .unwrap_err()
                .contains("lists no end")
        );
        let cut = MutantEnds {
            complete: false,
            ..ends(1)
        };
        assert!(
            of(&cut, false, vec![refused()])
                .unwrap_err()
                .contains("not complete")
        );
        assert!(
            mutant_acceptance(&ends(1), &whole, false, |_: &[Pattern]| None)
                .unwrap_err()
                .contains("no declared end")
        );
        // The baseline's side from its program row.
        let row = |class: &str, ends: Value| json!({"class": class, "ends": ends});
        let accepted = baseline_acceptance(&row("comparable", json!([{"declared": "finished"}])));
        assert_eq!(accepted, Acceptance::Accepted);
        let rejected = baseline_acceptance(&row(
            "comparable",
            json!([{"halt": "own", "declared": "none"}]),
        ));
        assert_eq!(rejected, Acceptance::Rejected);
        assert_eq!(
            baseline_acceptance(&row("comparable", json!([{"halt": "stop"}]))),
            Acceptance::Accepted
        );
        assert!(matches!(
            baseline_acceptance(&row("comparable-prefix", json!([]))),
            Acceptance::NotCompared(NotCompared::Undecided(_))
        ));
        assert!(matches!(
            baseline_acceptance(&row("timeout", Value::Null)),
            Acceptance::NotCompared(NotCompared::Unreadable(_))
        ));
        // The verdict.
        assert_eq!(
            accepts_verdict(&accepted, Ok(Acceptance::Rejected)),
            Verdict::Killed
        );
        assert_eq!(
            accepts_verdict(&rejected, Ok(Acceptance::Accepted)),
            Verdict::Killed
        );
        assert_eq!(
            accepts_verdict(&rejected, Ok(Acceptance::Rejected)),
            Verdict::Agree
        );
        assert!(matches!(
            accepts_verdict(&accepted, Err("cut".into())),
            Verdict::Unknown(reason) if reason == "cut"
        ));
        assert!(matches!(
            accepts_verdict(
                &Acceptance::NotCompared(NotCompared::SeveralEnds("both".into())),
                Ok(Acceptance::Accepted)
            ),
            Verdict::Unknown(reason) if reason == "both"
        ));
    }

    /// FX1 (review run-projection 1): a baseline whose run of a program ends `finished` on one
    /// path and takes an undefined step on another, against a mutant whose finished path ends
    /// at a refused end (its undefined step kept), is not a kill under `accepts`: read as a
    /// rejection, the baseline's undefined step makes it accept on one path and reject on
    /// another, which decides nothing, so the baseline's acceptance is not known, as the mutant
    /// side reads the same shape. The program row states the undefined step
    /// (`undefined_steps`); the grammar reparse's reading of the listed ends is unchanged.
    #[test]
    fn a_baseline_undefined_step_beside_accepted_ends_kills_nothing_under_accepts() {
        use crate::mutant_ends::{Across, MutantEnds};
        use crate::outcomes::RunPolls;
        let baseline = json!({
            "class": "comparable",
            "ends": [{"declared": "finished"}],
            "undefined_steps": true,
        });
        let side = baseline_acceptance(&baseline);
        assert!(
            matches!(&side, Acceptance::NotCompared(NotCompared::Undecided(detail))
                if detail.contains("undefined step")),
            "{side:?}"
        );
        let mutant = MutantEnds {
            program_id: "p".into(),
            ends: vec![r#"\dv{SortInt{}}("1")"#.to_owned()],
            stop_ends: Vec::new(),
            one_sided_ends: Vec::new(),
            undefined_steps: true,
            complete: true,
            across: Across::default(),
            polls: RunPolls {
                count: 10,
                bound: 100,
                cut: false,
            },
        };
        let whole = ResultProjection {
            state: kink_campaign::StateProjection::WholeTerm,
            compared: None,
            not_compared: Vec::new(),
            unobservable: Vec::new(),
        };
        let refused = mutant_acceptance(&mutant, &whole, false, |_: &[Pattern]| {
            Some(vec![DeclaredEnd::Refused {
                item: "crate::trapped".into(),
                reason: None,
                text: "1".into(),
            }])
        });
        assert_eq!(refused, Ok(Acceptance::Rejected));
        assert!(matches!(
            accepts_verdict(&side, refused),
            Verdict::Unknown(reason) if reason.contains("undefined step")
        ));
        // A baseline that rejects at every listed end rejects whatever its undefined step is.
        let rejecting = json!({
            "class": "comparable",
            "ends": [{"declared": "refused"}],
            "undefined_steps": true,
        });
        assert_eq!(baseline_acceptance(&rejecting), Acceptance::Rejected);
        // Without the undefined step the baseline accepts, and the same mutant kills.
        let finished = json!({"class": "comparable", "ends": [{"declared": "finished"}]});
        assert_eq!(baseline_acceptance(&finished), Acceptance::Accepted);
        assert_eq!(
            accepts_verdict(&baseline_acceptance(&finished), Ok(Acceptance::Rejected)),
            Verdict::Killed
        );
        // The grammar reparse reads the listed ends alone (unchanged).
        assert_eq!(listed_acceptance(&baseline), Acceptance::Accepted);
    }
}
