//! Kills judged under each projection `run` lists (projections package, PJ-11; `[run]
//! projections`, [`crate::FlowManifest::run_projections`]).
//!
//! `run`'s search compares every mutant with the baseline by the run's own slots: the exit stop,
//! the record's cells (the union of the cells the declared projections compare, every observable
//! cell when one keeps them all) and every channel of `[observe]`. A projection observes a
//! function of what those slots compare: some of the record's cells, functions of those cells
//! evaluated in one fixed observer (`views`, `observer`), some of the channels. So a difference
//! under a projection is a difference under the run's slots, and an agreement of the run's slots
//! is an agreement under every projection; a projection can turn a kill into a survival, never
//! the reverse.
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
//! - An `accepts` projection is not judged by `run` ([`Judge::NotJudged`]): its status is
//!   `undecided`, reason [`KIND_NOT_JUDGED`].
//!
//! The killer under a projection judged per program is its recorded killer while it kills under
//! it, else the first program of its domain in the search order that kills under it (decision U2,
//! per projection); where the run's search stopped before judging a program that decides it, `run`
//! runs the programs it needs (`crate::search`, the search under the projections).
//!
//! Nothing is cached: a verdict under a projection is recomputed from each side's stored raw
//! result on every run (projections package README, "Storage"), so no key names a projection.

use crate::manifest::{FlowManifest, ProjectionKind, ProjectionSection};
use crate::mutant_ends::MutantEnds;
use crate::observed::ResultProjection;
use crate::outcomes::slot_name;
use k_rust::kore::ast::Pattern;
use kink_campaign::OracleOutcome;
use serde_json::{Map, Value, json};
use std::collections::BTreeSet;

/// The reason of an `accepts` projection's status: `run` judges no acceptance.
pub const KIND_NOT_JUDGED: &str = "kind-not-judged";

/// The reason of an `undecided` status: some program of the projection's domain that its
/// decision needs was not judged under it, because no call of the search under the projections
/// could judge it (a call that met a corpus error, or a mutant-scope failure that ran no test;
/// `crate::search`).
pub const PROJECTION_SEARCH: &str = "projection-search";

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
    /// Not judged by `run`: the status is `undecided` with this reason.
    NotJudged(&'static str),
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
            ProjectionKind::Accepts => Self::NotJudged(KIND_NOT_JUDGED),
            ProjectionKind::Trace => Self::Flow(FlowJudge {
                stop: false,
                cells: false,
                channels,
            }),
            ProjectionKind::End => {
                // The record's cells: every observable cell for a projection without `compare`
                // when nothing narrows the record; else as many cells as the record keeps, which,
                // since the record is the union of the projections' cells and a projection names
                // no cell twice, are the record's cells.
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
    Ok(ends
        .patterns()?
        .iter()
        .map(|end| project(result, end))
        .collect())
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
            [
                Judge::Run,
                Judge::NotJudged(KIND_NOT_JUDGED),
                flow(true, true, Channels::All),
            ]
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
}
