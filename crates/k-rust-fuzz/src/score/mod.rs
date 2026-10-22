//! Scores per target kind (ARCHITECTURE 6.2, 6.4). Owner: FZ-12.
//!
//! A score ranks the `miss` cases of a campaign by how near each came to the target, smaller
//! being better; the climb proposer (`crate::proposers::climb`) climbs it. Only `miss` cases are
//! scored (R-18): a bounded or unclean case's coverage stops early, so its signals understate
//! how far it went, and the engine's loop gives every other case no score.
//!
//! # The rule score
//!
//! For a rule target the score is the pair (rule-graph distance, guard distance), compared
//! lexicographically ([`Score`]):
//!
//! - a case whose run entered the target's `requires` (the target is in coverage `matched`)
//!   has rule-graph distance 0, and its guard distance is the least distance of the target's
//!   condition over the instances the run entered it with ([`distance`]): how far the
//!   nearest instance is from passing it;
//! - a case that did not, but entered the `requires` of a direct predecessor of the target in
//!   the rule graph (a rule a step of which may enable the target) whose condition failed, has
//!   rule-graph distance 1, and its guard distance is the least distance of those failed
//!   instances: the predecessor's guard is what kept the run from the target (in the terms of
//!   search-based testing, the approach level and the branch distance of the critical branch).
//!   The predecessors read are those whose right-hand side keys the head of `<k>`
//!   (`RuleGraph::keyed_enablers`), when there are any;
//! - any other case has the least rule-graph distance from a rule it applied or entered to the
//!   target (none when the target is unreachable from all of them), and no guard distance.
//!
//! ARCHITECTURE 6.4 defines the guard component only for a case at the target; the second case
//! fills it where the target's condition was not reached, which only orders cases 6.4 leaves
//! tied (FZ-12 report). A missing guard distance sorts after every distance: an instance whose
//! condition gives no distance (symbolic, undefined or undecided atoms, a `chosen` record) is
//! no signal, never a distance of 0.
//!
//! The rule graph over-approximates enablement: a rule whose right-hand side ends with a bare
//! continuation (`=> .K ...`) keys nothing at the head of `<k>`, so it is a direct predecessor
//! of every rule (FZ-G8 review), whatever its step puts in the continuation. Its guard says
//! nothing about the target in particular, and following it leads elsewhere: on the stall
//! benchmark, a side cell's guard pulled the climb towards the side cell, which ends the walk,
//! and trapped it there (FZ-12 report). A predecessor that puts a rigid head in `<k>` that the
//! target's left-hand side key covers is preferred, so the score reads those when there
//! are any, and every predecessor only when none keys `<k>`. That is a scheduling choice, not
//! evidence: a keyed edge rests on what the step writes, an open one on nothing the graph can
//! see, but the real enabler can be an open predecessor whose continuation holds the target's
//! redex, and then a case blocked there scores no guard distance while an unrelated keyed
//! predecessor exists. The score stays a heuristic for the proposer, never evidence.
//!
//! # The observer score
//!
//! For an observer target the score is the observer's distance to acceptance: `u32::MAX` minus
//! the greatest progress ([`crate::target::ObserverVerdict::Progress`]) the observer answered on
//! any path of the run, normalized as an atom's distance, at level 0; a case whose observer
//! answered no progress has no guard distance.
//!
//! Pattern and differential targets are not scored yet: the signals they need are not reported
//! (FZ-12 report, "Open: other target kinds"), and the climb proposer refuses them.

pub(crate) mod distance;
pub(crate) mod records;

use std::collections::{BTreeMap, BTreeSet};

pub(crate) use distance::{Distance, Operand};

use crate::graph::RuleGraph;

/// The rule-graph component of a [`Score`]: a number of edges, or no path to the target.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum Level {
    /// The target is this many rule-graph edges away (0: the target's condition was entered).
    At(u64),
    /// No rule the case applied or entered reaches the target in the rule graph.
    Unreached,
}

/// The guard component of a [`Score`].
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum Guard {
    /// The least guard distance of the condition the level names.
    Defined(Distance),
    /// No instance gave a distance: no signal, worse than every distance.
    Unknown,
}

/// A score: compared lexicographically, the level first, smaller being better
/// (ARCHITECTURE 6.4).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct Score {
    /// The rule-graph distance.
    pub(crate) level: Level,
    /// The guard distance at that level.
    pub(crate) guard: Guard,
}

/// One recorded entry into a rule's `requires`, as a score reads it ([`records::guards`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct GuardEntry {
    /// The condition's guard distance under the entry's instance; `None` when it gives none.
    pub(crate) distance: Option<Distance>,
    /// The attempt refuted the condition (its verdict), so the entry is a failed guard.
    pub(crate) refuted: bool,
    /// The ground `Int` and `String` values the instance binds to the condition's variables:
    /// where a hole's value reaches the guard unchanged, it is among them (input-to-state
    /// correspondence; ARCHITECTURE 10.2, Redqueen).
    pub(crate) reads: Vec<Operand>,
}

/// Per rule id, the entries into its `requires` a run recorded, in the run's order.
pub(crate) type Guards = BTreeMap<String, Vec<GuardEntry>>;

/// A score with the values its guard read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Scored {
    /// The score.
    pub(crate) score: Score,
    /// The values bound to the variables of the condition whose distance is the score's guard
    /// component (an entry of least distance); empty without a guard distance. A climb prefers
    /// moving the holes whose values are among them.
    pub(crate) reads: Vec<Operand>,
}

/// What a case's run reports that a score reads: its coverage and the guard distance of each
/// condition entry of the rules whose conditions were collected.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Signals<'a> {
    /// Rule ids in coverage `applied`.
    pub(crate) applied: &'a [String],
    /// Rule ids in coverage `matched`.
    pub(crate) matched: &'a [String],
    /// Per rule id, the recorded entries into its `requires` ([`records::guards`]).
    pub(crate) guards: &'a Guards,
    /// For an observer target, the greatest progress the observer reported on the run.
    pub(crate) progress: Option<u32>,
}

/// The scorer of a campaign's target (ARCHITECTURE 6.4).
#[derive(Clone, Debug)]
pub(crate) enum Scorer {
    /// A rule target (module documentation, "The rule score").
    Rule(RuleScorer),
    /// An observer target: the observer's distance to acceptance, `u32::MAX` minus the greatest
    /// progress ([`crate::target::ObserverVerdict::Progress`]) the observer answered on the
    /// run, normalized as an atom's distance; no distance when it answered none.
    Observer,
}

impl Scorer {
    /// The rules whose condition entries the score reads; none for an observer target.
    pub(crate) fn condition_rules(&self) -> Vec<String> {
        match self {
            Self::Rule(rule) => rule.condition_rules(),
            Self::Observer => Vec::new(),
        }
    }

    /// The score of a `miss` case with `signals`.
    pub(crate) fn score(&self, signals: Signals<'_>) -> Scored {
        match self {
            Self::Rule(rule) => rule.score(signals),
            Self::Observer => Scored {
                score: Score {
                    level: Level::At(0),
                    guard: signals.progress.map_or(Guard::Unknown, |progress| {
                        Guard::Defined(Distance::normalized((u32::MAX - progress).into()))
                    }),
                },
                reads: Vec::new(),
            },
        }
    }
}

/// The scorer of a rule target (module documentation, "The rule score"), built once per
/// campaign from the baseline's rule graph.
#[derive(Clone, Debug)]
pub(crate) struct RuleScorer {
    target: String,
    /// The rule-graph distance from every rule that reaches the target.
    distances: BTreeMap<String, u64>,
    /// The target's direct predecessors whose guard the score reads, without the target: those
    /// that key the head of `<k>` (`RuleGraph::keyed_enablers`), or every direct predecessor
    /// when none does.
    predecessors: BTreeSet<String>,
}

impl RuleScorer {
    /// The scorer of the rule target `target` (a catalog id) over `graph`.
    pub(crate) fn new(graph: &RuleGraph, target: &str) -> Self {
        let distances = graph
            .distances_to(target)
            .into_iter()
            .map(|(id, distance)| (id, u64::try_from(distance).unwrap_or(u64::MAX)))
            .collect();
        let keyed = graph.keyed_enablers(target);
        let mut predecessors = if keyed.is_empty() {
            graph.enablers(target)
        } else {
            keyed
        };
        predecessors.remove(target);
        Self {
            target: target.to_owned(),
            distances,
            predecessors,
        }
    }

    /// The rules whose condition entries the score reads: the target and its direct
    /// predecessors, sorted. A campaign asks the backend to record exactly these.
    pub(crate) fn condition_rules(&self) -> Vec<String> {
        let mut rules: BTreeSet<String> = self.predecessors.clone();
        rules.insert(self.target.clone());
        rules.into_iter().collect()
    }

    /// The score of a `miss` case with `signals`, and the values its guard read.
    pub(crate) fn score(&self, signals: Signals<'_>) -> Scored {
        let scored = |level, found: Option<(&Distance, &GuardEntry)>| match found {
            Some((distance, entry)) => Scored {
                score: Score {
                    level,
                    guard: Guard::Defined(distance.clone()),
                },
                reads: entry.reads.clone(),
            },
            None => Scored {
                score: Score {
                    level,
                    guard: Guard::Unknown,
                },
                reads: Vec::new(),
            },
        };
        if signals.matched.contains(&self.target) {
            let entries = signals
                .guards
                .get(&self.target)
                .map_or(&[][..], Vec::as_slice);
            // A held entry is at distance 0 only where the target also applied; held while the
            // rule was blocked (no successor) is no measure of how near the case came.
            let applied = signals.applied.contains(&self.target);
            return scored(
                Level::At(0),
                least(entries.iter().filter(|entry| applied || entry.refuted)),
            );
        }
        let blocked = self
            .predecessors
            .iter()
            .filter_map(|rule| signals.guards.get(rule))
            .flatten()
            .filter(|entry| entry.refuted);
        if let Some(found) = least(blocked) {
            return scored(Level::At(1), Some(found));
        }
        let level = signals
            .applied
            .iter()
            .chain(signals.matched)
            .filter_map(|rule| self.distances.get(rule))
            .min()
            .map_or(Level::Unreached, |distance| Level::At(*distance));
        scored(level, None)
    }

    /// A scorer over explicit distances and predecessors, for unit tests without a graph.
    #[cfg(test)]
    pub(crate) fn from_parts(
        target: &str,
        distances: &[(&str, u64)],
        predecessors: &[&str],
    ) -> Self {
        Self {
            target: target.to_owned(),
            distances: distances
                .iter()
                .map(|(id, distance)| ((*id).to_owned(), *distance))
                .collect(),
            predecessors: predecessors.iter().map(|id| (*id).to_owned()).collect(),
        }
    }
}

/// The entry of least distance among `entries` (the first of equal ones), with its distance.
fn least<'a>(
    entries: impl Iterator<Item = &'a GuardEntry>,
) -> Option<(&'a Distance, &'a GuardEntry)> {
    let mut best: Option<(&Distance, &GuardEntry)> = None;
    for entry in entries {
        if let Some(distance) = &entry.distance
            && best.is_none_or(|(least, _)| distance < least)
        {
            best = Some((distance, entry));
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ids(names: &[&str]) -> Vec<String> {
        names.iter().map(|name| (*name).to_owned()).collect()
    }

    fn d(raw: u32) -> Distance {
        Distance::normalized(raw.into())
    }

    fn scorer() -> RuleScorer {
        RuleScorer::from_parts(
            "t",
            &[("t", 0), ("p", 1), ("q", 1), ("a", 2), ("far", 3)],
            &["p", "q"],
        )
    }

    fn score(
        applied: &[&str],
        matched: &[&str],
        guards: &[(&str, Vec<Option<Distance>>)],
    ) -> Score {
        let guards: Guards = guards
            .iter()
            .map(|(rule, records)| {
                let entries = records
                    .iter()
                    .map(|distance| GuardEntry {
                        distance: distance.clone(),
                        refuted: distance.as_ref().is_none_or(|distance| !distance.is_zero()),
                        reads: Vec::new(),
                    })
                    .collect();
                ((*rule).to_owned(), entries)
            })
            .collect();
        scorer()
            .score(Signals {
                applied: &ids(applied),
                matched: &ids(matched),
                guards: &guards,
                progress: None,
            })
            .score
    }

    #[test]
    fn an_observer_case_is_nearer_the_more_progress_it_made() {
        let score = |progress| {
            Scorer::Observer
                .score(Signals {
                    applied: &[],
                    matched: &[],
                    guards: &Guards::new(),
                    progress,
                })
                .score
        };
        assert!(score(Some(3)) < score(Some(2)));
        assert!(score(Some(0)) < score(None));
        assert_eq!(score(None).guard, Guard::Unknown);
        assert!(Scorer::Observer.condition_rules().is_empty());
    }

    #[test]
    fn the_condition_rules_are_the_target_and_its_predecessors() {
        assert_eq!(scorer().condition_rules(), ids(&["p", "q", "t"]));
    }

    #[test]
    fn a_case_at_the_target_is_ranked_by_its_nearest_instance() {
        let near = score(&["a"], &["t"], &[("t", vec![Some(d(9)), Some(d(2)), None])]);
        assert_eq!(
            near,
            Score {
                level: Level::At(0),
                guard: Guard::Defined(Distance::normalized(2u32.into()))
            }
        );
        let far = score(&["a"], &["t"], &[("t", vec![Some(d(5))])]);
        assert!(near < far);
        // At the target, an instance without a distance is no signal: worse than any distance,
        // still better than not reaching the target's condition.
        let unknown = score(&["a"], &["t"], &[("t", vec![None])]);
        assert_eq!(unknown.guard, Guard::Unknown);
        assert!(far < unknown);
        let blocked = score(&["a"], &["p"], &[("p", vec![Some(d(1))])]);
        assert!(unknown < blocked);
    }

    #[test]
    fn a_case_blocked_at_a_predecessor_is_ranked_by_the_failed_guard() {
        let near = score(
            &["a"],
            &["p", "q"],
            &[("p", vec![Some(d(3))]), ("q", vec![Some(d(7))])],
        );
        assert_eq!(near.level, Level::At(1));
        assert_eq!(
            near.guard,
            Guard::Defined(Distance::normalized(3u32.into()))
        );
        // A predecessor whose condition held is no blocking guard.
        let passed = score(&["a", "p"], &["p"], &[("p", vec![Some(Distance::zero())])]);
        assert_eq!(
            passed,
            Score {
                level: Level::At(1),
                guard: Guard::Unknown
            }
        );
        assert!(near < passed);
    }

    #[test]
    fn a_held_entry_counts_only_where_the_target_applied() {
        let held = || vec![("t", vec![Some(Distance::zero())])];
        // Held but blocked (the target matched, did not apply): no measure.
        assert_eq!(score(&["a"], &["t"], &held()).guard, Guard::Unknown);
        // Held and applied (a miss for another reason, such as an unclean leaf): distance 0.
        assert_eq!(
            score(&["a", "t"], &["t"], &held()).guard,
            Guard::Defined(Distance::zero())
        );
    }

    #[test]
    fn other_cases_have_only_the_rule_graph_distance() {
        assert_eq!(
            score(&["far", "a"], &[], &[]),
            Score {
                level: Level::At(2),
                guard: Guard::Unknown
            }
        );
        assert_eq!(
            score(&["elsewhere"], &[], &[]),
            Score {
                level: Level::Unreached,
                guard: Guard::Unknown
            }
        );
        assert!(score(&["a"], &[], &[]) < score(&["far"], &[], &[]));
        assert!(score(&["far"], &[], &[]) < score(&["elsewhere"], &[], &[]));
    }

    #[test]
    fn the_reads_are_those_of_the_entry_of_least_distance() {
        let entry = |raw: u32, read: i64| GuardEntry {
            distance: Some(d(raw)),
            refuted: true,
            reads: vec![Operand::Int(read.into())],
        };
        let guards: Guards = [(
            "t".to_owned(),
            vec![
                entry(9, 1),
                entry(2, 2),
                entry(2, 3),
                GuardEntry {
                    distance: None,
                    refuted: true,
                    reads: vec![Operand::Int(4.into())],
                },
            ],
        )]
        .into_iter()
        .collect();
        let scored = scorer().score(Signals {
            applied: &[],
            matched: &ids(&["t"]),
            guards: &guards,
            progress: None,
        });
        assert_eq!(scored.reads, vec![Operand::Int(2.into())]);
        // Without a guard distance, nothing was read.
        let scored = scorer().score(Signals {
            applied: &ids(&["a"]),
            matched: &[],
            guards: &Guards::new(),
            progress: None,
        });
        assert!(scored.reads.is_empty());
    }

    /// The GUARD fixture, executed with condition records: `notBool pb(0)` is undefined, so the
    /// case at `X = 0` has no guard distance, never 0, and ranks below the defined miss at
    /// `X = 1` (`pb(1)` true, so the guard fails by one atom).
    #[test]
    fn an_undefined_target_guard_scores_below_a_defined_miss() {
        use k_rust::backend::{ConditionCollection, ExecuteRequest};
        let compiled = crate::support::GUARD.compiled();
        let score_of = |file: &str| {
            let mut request = ExecuteRequest::new(compiled.initial(file));
            request.collect_coverage = true;
            request.collect_conditions = Some(ConditionCollection::new(["GUARD.goal"]));
            let result = compiled
                .source_backend()
                .execute(request)
                .expect("the program executes");
            let coverage = result.coverage.expect("coverage was asked for");
            let conditions = coverage.conditions.expect("conditions were asked for");
            assert_eq!(conditions.len(), 1, "{conditions:?}");
            let target = conditions[0].rule.clone();
            let guards = records::guards(&conditions);
            RuleScorer::from_parts(&target, &[(target.as_str(), 0)], &[])
                .score(Signals {
                    applied: &coverage.applied,
                    matched: &coverage.matched,
                    guards: &guards,
                    progress: None,
                })
                .score
        };
        let undefined = score_of("guard/zero.pgm");
        let defined = score_of("guard/one.pgm");
        assert_eq!(
            undefined,
            Score {
                level: Level::At(0),
                guard: Guard::Unknown
            }
        );
        assert_eq!(
            defined,
            Score {
                level: Level::At(0),
                guard: Guard::Defined(d(1))
            }
        );
        assert!(defined < undefined);
    }
}
