//! Targets: what a case must do to be a hit, their resolution against a definition, and the
//! judgement of a case result (ARCHITECTURE 4). Owner: FZ-05; the differential judge is FZ-08's
//! (`differential`); the observer target is FZ-10's (`observer`); patterns `at: any-state` are
//! FZ-ANYSTATE's (`any_state`).
//!
//! Every target is an existential goal. A universal property is stated as the target "a clean
//! natural end violates P", with [`Target::negated_property`] set, and its hit is reported as a
//! property failure (ARCHITECTURE 4).

mod any_state;
mod comparable;
pub(crate) mod differential;
#[cfg(test)]
mod fixture_tests;
mod observer;
mod rule;
#[cfg(test)]
mod tests;

use std::{collections::BTreeMap, fmt};

use k_rust::backend::{CompiledRuleKind, CompiledRuleOutput, HaltReasonOutput};
use serde::{Deserialize, Serialize};

pub(crate) use observer::JudgedRun;
pub use observer::{
    ConfigurationView, Observer, ObserverHandle, ObserverTarget, ObserverVerdict, contains_symbol,
};
pub(crate) use rule::relative_catalog;
#[cfg(test)]
pub(crate) use rule::resolve_rule;

use crate::{
    assemble::ProgramAssembly,
    error::{CampaignError, TargetProblem},
    exec::{
        self, CaseResult, CompiledPattern, Executor, LeafMatcher, OutcomeClass, StateMatchNeed,
        TargetNeeds, UncleanReason, UnjudgedReason,
    },
    report::{EngineDefect, ExecutionModality, ResultModality},
    source_names::SourceNames,
    spec::{CompiledDefinition, PathMode},
};

/// A campaign's target (ARCHITECTURE 4.1).
#[expect(
    clippy::struct_excessive_bools,
    reason = "each is an independent option of the serialized target, a campaign key"
)]
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct Target {
    /// What is to be reached.
    pub kind: TargetKind,
    /// A case that reaches the target continues to its natural end, and a hit also requires a
    /// clean natural end; a reaching case that does not end naturally is `reached-unfinished`
    /// (ARCHITECTURE 4.1, R-23).
    pub run_to_completion: bool,
    /// The target states the violation of a universal property: its hit is reported as a
    /// property failure (ARCHITECTURE 4).
    pub negated_property: bool,
    /// For a rule or pattern target with `run-to-completion`: a hit also requires the reaching
    /// natural end to be data (`k_rust_backend::data_term`), the fact the differential judge's
    /// condition 4 rests on, so that the witness's end can be compared with another
    /// definition's (ARCHITECTURE 4.3). A reaching natural end that is not data is
    /// `unsupported`. `true` by default (absent from a serialized target when `true`): the
    /// witness of a run-to-completion target is meant to become a test whose end is compared.
    /// Ignored without `run-to-completion`, for a negated property (whose counterexample is
    /// decided by its match) and by the differential and observer targets.
    #[serde(
        default = "data_end_default",
        skip_serializing_if = "is_data_end_default"
    )]
    pub data_end: bool,
    /// For a rule or pattern target (`comparable-end`): a hit also requires that the witness
    /// program's run of every path is one kink can compare (P7-ADDENDUM section 4, conditions
    /// P1 to P5; [`crate::exec::comparable::end_conditions`]): complete, every leaf an end or an
    /// undefined step, decided, every such leaf's term data (k-rust's `is_data`), with no
    /// diagnostic of any kind on any leaf, and no stack stop, chosen value, contradicted claim,
    /// allowance refusal or unsupported hook in the run or the definition's load. That run is the
    /// hit case's own when it ran every path with no terminal rule; otherwise one more run of
    /// every path (with [`crate::spec::DEFAULT_MAX_WORK`] when the campaign sets no work bound),
    /// part of the case, which counts its work and determinism. A hit that fails is
    /// `unsupported`, with the reason `end-not-comparable:CONDITION`
    /// ([`crate::exec::UnjudgedReason::EndNotComparable`]), or `timeout` when a clock stopped that
    /// run. Without the option, the witness of a rule or pattern target still carries the
    /// judgement ([`crate::report::WitnessCase::comparable`]), made outside every case when it
    /// needs the extra run, so that the option's absence leaves the campaign's cases as they
    /// were. `false` by default (absent from a serialized target when `false`); ignored by the
    /// differential and observer targets.
    #[serde(default, skip_serializing_if = "is_false")]
    pub comparable: bool,
    /// For a pattern target (`query-confirmable`): a hit also requires that no leaf of the run
    /// carries a diagnostic of any kind, that the run's lists hold no fact (a chosen value or
    /// contradicted claim on no leaf, an allowance refusal, an unsupported hook, a stop for lack
    /// of stack), that the definition's load counted no stop for lack of stack (its other records
    /// do not refuse the hit), and that the matched state holds no term-level `\and`
    /// (P7-ADDENDUM section 4, conditions Q2', Q4', Q5';
    /// [`crate::exec::comparable::query_conditions`]). The run is read whole because kink's
    /// search absorbs the facts of converging paths into a matching state. This is necessary
    /// for kink's query to confirm the hit, not sufficient: kink's search stops at its first
    /// match (Q6'), which the fuzz cannot decide. A hit that fails is `unsupported`, with the
    /// reason `query-not-confirmable:CONDITION`
    /// ([`crate::exec::UnjudgedReason::QueryNotConfirmable`]). `false` by default (absent from
    /// a serialized target when `false`); ignored by every other target kind.
    #[serde(default, skip_serializing_if = "is_false")]
    pub query_confirmable: bool,
}

/// [`Target::data_end`]'s default.
const fn data_end_default() -> bool {
    true
}

#[expect(
    clippy::trivially_copy_pass_by_ref,
    reason = "serde's `skip_serializing_if` passes a reference"
)]
const fn is_data_end_default(data_end: &bool) -> bool {
    *data_end
}

#[expect(
    clippy::trivially_copy_pass_by_ref,
    reason = "serde's `skip_serializing_if` passes a reference"
)]
const fn is_false(value: &bool) -> bool {
    !*value
}

impl Target {
    /// Whether a hit needs a data end: a rule or pattern target with `run-to-completion` and
    /// [`Self::data_end`], that states no property's violation. A property counterexample is
    /// decided by its match, whatever the end's function applications denote, and is not a test
    /// compared by its end, so it needs none (FZ-DATAEND review S1).
    #[must_use]
    pub(crate) fn requires_data_end(&self) -> bool {
        self.run_to_completion
            && self.data_end
            && !self.negated_property
            && matches!(self.kind, TargetKind::Rule(_) | TargetKind::Pattern(_))
    }
}

/// The kinds of target (ARCHITECTURE 4.1).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum TargetKind {
    /// A rewrite rule fires, is covered, or has its condition reached (ARCHITECTURE 4.2).
    Rule(RuleTarget),
    /// A configuration matches a compiled pattern (ARCHITECTURE 4.1).
    Pattern(PatternTarget),
    /// The mutant reaches a clean end the baseline cannot reach on the same input
    /// (ARCHITECTURE 4.3).
    Differential(DifferentialTarget),
    /// A client observer accepts (ARCHITECTURE 4.1, 9.2), fed after the run (`observer`).
    Observer(ObserverTarget),
}

/// A rule target (ARCHITECTURE 4.2).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct RuleTarget {
    /// The rule, resolved through `Backend::rule_catalog`.
    pub rule: RuleRef,
    /// What counts as reaching it.
    pub mode: RuleMode,
}

/// A reference to a rule of the catalog (ARCHITECTURE 4.2).
///
/// A reference resolves to the id of one catalog entry. Entries matching it with different ids
/// make it ambiguous; an entry whose id other entries share, whose id is `UNKNOWN`, that is not
/// executable, or that is an equation is refused, because coverage and traces record ids, and
/// such an id may be recorded for another sentence or for use the run never made.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(
    tag = "by",
    content = "value",
    rename_all = "kebab-case",
    deny_unknown_fields
)]
pub enum RuleRef {
    /// The rule's label as the catalog writes it (`IMP.overflow`), or, when no entry has that
    /// label, the label without its module (`overflow`).
    Label(String),
    /// The rule's unique id (`UNIQUE_ID`).
    UniqueId(String),
    /// The rule's source position: a catalog origin with this `source` whose `location` holds
    /// `line`, from the line the rule starts on to the line it ends on. A rule is a span of its
    /// source, and rules do not nest, so any line of a rule names that rule alone.
    Source {
        /// The source file, which must name exactly one file of the catalog: the catalog's
        /// path or its `Source(path)` text (a whole path names its file alone); else a suffix
        /// of a path that starts after a `/` (`rules.k` for `Source(tests/rules/rules.k)`);
        /// else an absolute path that ends with `/` and a relative catalog path. A source that
        /// names several files is refused, whatever the line. Equal written axioms share one
        /// catalog entry, so a reference to one of their positions names all.
        source: String,
        /// A one-based line of the rule: the line it starts on, or any later line it spans.
        line: u32,
    },
}

/// The names of a catalog entry besides its unique id: its kind, its label and where it is
/// written (ARCHITECTURE 4.2). Coverage and traces record ids; these names let an author read
/// which rule an id is. Several entries that share one id (equal written axioms) give one name
/// with all their locations, and the first entry's kind and label.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct RuleName {
    /// A rewrite rule, or the kind of equation.
    pub kind: CompiledRuleKind,
    /// The label as the catalog writes it (`IMP.assign`), if the rule has one.
    pub label: Option<String>,
    /// The source locations the entry was written at, in catalog order; empty for a sentence
    /// with no source location.
    pub locations: Vec<RuleLocation>,
}

impl RuleName {
    /// The rule `id` of this name on one line: where it is written (each file by its
    /// [`RuleLocation::reference`], so `FILE:LINE` as printed is a reference to the rule), its
    /// label in brackets, its kind when it is an equation, and its unique id, as in
    /// `imp.k:56 [IMP.mul] unique id 5872…`.
    #[must_use]
    pub fn describe<'a>(&'a self, id: &'a str) -> impl fmt::Display + 'a {
        Described { id, name: self }
    }
}

/// [`RuleName::describe`].
struct Described<'a> {
    id: &'a str,
    name: &'a RuleName,
}

impl fmt::Display for Described<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.name.locations.is_empty() {
            f.write_str("(no source location)")?;
        }
        for (index, location) in self.name.locations.iter().enumerate() {
            if index > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{}:{}", location.reference, location.line)?;
            if location.end_line > location.line {
                write!(f, "-{}", location.end_line)?;
            }
        }
        if let Some(label) = &self.name.label {
            write!(f, " [{label}]")?;
        }
        match self.name.kind {
            CompiledRuleKind::Rewrite => {}
            CompiledRuleKind::FunctionEquation => f.write_str(" (function equation)")?,
            CompiledRuleKind::Simplification => f.write_str(" (simplification)")?,
            CompiledRuleKind::Definedness => f.write_str(" (definedness axiom)")?,
        }
        write!(f, " unique id {}", self.id)
    }
}

/// Where a catalog entry is written: a source file and the lines it spans.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Ord, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct RuleLocation {
    /// The source file, named by its path relative to the directory of the main module's file
    /// (`imp.k`, `lib/expr.k`, `../lib/x.k`; a `krust-builtin://` URI as it is), not by the path
    /// the catalog records, which says where the definition was compiled (FZ-REPLAY-WHOLE S1).
    pub source: String,
    /// The shortest reference that names this file alone among the catalog's files: its
    /// shortest suffix after a `/`, or the whole relative path ([`RuleRef::Source`]).
    pub reference: String,
    /// The one-based line the entry starts on.
    pub line: u32,
    /// The one-based line it ends on.
    pub end_line: u32,
}

/// The names of every id of `catalog` ([`RuleName`]).
pub(crate) fn rule_names(catalog: &[CompiledRuleOutput]) -> BTreeMap<String, RuleName> {
    let files = rule::catalog_files(catalog);
    let references: BTreeMap<&str, String> = files
        .iter()
        .map(|file| (*file, rule::shortest_reference(&files, file)))
        .collect();
    let mut names: BTreeMap<String, RuleName> = BTreeMap::new();
    for entry in catalog {
        let locations = rule::locations(entry, &references);
        names
            .entry(entry.id.clone())
            .and_modify(|name| name.locations.extend(locations.iter().cloned()))
            .or_insert_with(|| RuleName {
                kind: entry.kind,
                label: entry.label.clone(),
                locations,
            });
    }
    names
}

/// What counts as reaching a rule (ARCHITECTURE 4.2, R-5).
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum RuleMode {
    /// A clean leaf's trace contains a `Rewrite` entry with the rule's id, or the run halted
    /// `terminal` on the rule as the only stop rule.
    Fired,
    /// The rule is in coverage `applied` (kink's `fired_by`); weaker than `fired`.
    Covered,
    /// The rule is in coverage `matched` (kink's `reached_by`).
    ConditionReached,
}

/// A pattern target (ARCHITECTURE 4.1).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct PatternTarget {
    /// The pattern in krun's `--pattern` surface syntax; it may carry `requires`.
    pub pattern: String,
    /// Where the pattern is matched.
    pub at: PatternAt,
}

/// Where a pattern target is matched (ARCHITECTURE 4.1).
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum PatternAt {
    /// The end of the run: a clean leaf (ARCHITECTURE 4.1, 5.2) that matches with empty
    /// constraints; `run-to-completion` additionally requires a natural end.
    Final,
    /// Any normalized configuration the run reaches, the initial one included: one that is
    /// decided, ceil-free and matches with empty constraints, reached on a path whose prefix up
    /// to it is clean (ARCHITECTURE 5.2's leaf facts, read on the prefix). Under
    /// `run-to-completion` every leaf must also be a clean natural end (and a data end with
    /// `data-end`), since a reached state is attributed to no leaf. The witness records the
    /// configuration and its depth. k-rust matches every reached state inside the run
    /// (`matchStates`, FZ-STATESET-MATCH; `any_state` module documentation).
    AnyState,
}

/// The differential target's options (ARCHITECTURE 4.3); the two definitions are
/// [`crate::Definitions::baseline`] and [`crate::Definitions::mutant`]. The mutant runs on the
/// campaign's path mode; the baseline always runs all paths.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct DifferentialTarget {}

/// Where a hit reached the target (ARCHITECTURE 5.3, D16).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum HitSite {
    /// This clean leaf reaches the target: its path fired the rule or its state matches.
    Leaf(usize),
    /// The run reaches the target, and no one leaf can be named: a coverage-mode hit over
    /// several leaves, every one of which is clean, so the witness is the case and every leaf's
    /// configuration, without a single final configuration; or an all-paths `fired` hit read
    /// from the run's committed transitions with every leaf clean (FZ-STATESET-MATCH).
    Run,
    /// A state the run reached at `depth` (committed steps from the initial configuration)
    /// matches the pattern `at: any-state` on a clean prefix (`ExecutionResult::state_matches`,
    /// its first clean reach). It is attributed to no leaf; the witness carries the configuration
    /// ([`JudgedRun::state_match`]).
    StateMatch {
        /// The depth of the reaching state.
        depth: u64,
    },
}

/// The judgement of one case against a resolved target.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Judgement {
    /// The case's class.
    pub(crate) class: OutcomeClass,
    /// For a hit, where the target was reached.
    pub(crate) hit_site: Option<HitSite>,
    /// The target rule is in coverage `matched` but not `applied`: its condition was entered
    /// and it built no successor (a blocked rule, ARCHITECTURE 6.2).
    pub(crate) blocked: bool,
    /// Why the case is `unsupported` ([`crate::exec::reasons`]); `Some` exactly then.
    pub(crate) reason: Option<UnjudgedReason>,
    /// The class the case's leaves gave when [`UnjudgedReason::FiredOffTrace`] replaced it by
    /// `unsupported`, and `None` otherwise. That reason says only that the target cannot be
    /// judged; the leaves are the run's own, so a clean abnormal stop among them is still a
    /// `stuck` finding of the program, and the incidental finding is decided from this class
    /// ([`crate::report::Incidentals`]).
    pub(crate) demoted_from: Option<OutcomeClass>,
}

/// A target resolved against one definition: rules mapped to catalog ids, patterns compiled for
/// that definition's executor (ARCHITECTURE 4.2, 9.2).
pub(crate) struct ResolvedTarget {
    target: Target,
    resolved: Resolved,
    matchers: Vec<LeafMatcher>,
}

/// What a target resolved to.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Resolved {
    /// A rewrite rule, by its catalog id, and the mode that counts as reaching it.
    Rule {
        /// The rule's unique id.
        id: String,
        /// What counts as reaching it.
        mode: RuleMode,
    },
    /// A pattern at a clean natural end, judged by the target's only matcher.
    PatternFinal,
    /// A pattern at any configuration of a path, judged by the target's only matcher from
    /// observed execution ([`ResolvedTarget::run_and_judge`], `any_state`).
    PatternAnyState,
    /// The differential target, judged by [`differential::judge_pair`].
    Differential,
    /// An observer target, judged from observed execution
    /// ([`ResolvedTarget::run_and_judge`]).
    Observer {
        /// The observation filter: the rules whose steps are observed, or every event.
        rules: Option<Vec<String>>,
    },
}

/// For each leaf of `result`, whether it is an end leaf that matches the target's only matcher
/// (ARCHITECTURE 4.1, `at: final`; 5.3, D16).
///
/// Only a leaf whose halt is an end (`stuck`, `trivial` or `terminal`) holds a final state; a
/// leaf cut by a bound, a timeout or a cancellation does not, so its match says nothing about
/// the end the run never reached, and the leaf classes by its halt. On end leaves,
/// [`crate::exec::LeafReport::matches`] is judged whenever the state can be decided, clean or
/// not, so that a matching leaf that is not clean classes as `unsupported`, never as `miss`.
/// Whether a hit may rest on the leaf (clean, and a natural end under `run-to-completion`) is
/// [`crate::exec::classify`]'s question.
///
/// # Errors
///
/// [`EngineDefect`] when a leaf carries no judgement of the matcher, which [`Executor::run`]
/// owes every leaf of a case run with this target's matchers.
fn pattern_reached(result: &CaseResult) -> Result<Vec<bool>, EngineDefect> {
    result
        .leaves
        .iter()
        .enumerate()
        .map(|(index, leaf)| match leaf.matches.first() {
            Some(matched) => Ok(*matched
                && matches!(
                    leaf.halt,
                    HaltReasonOutput::Stuck
                        | HaltReasonOutput::Trivial
                        | HaltReasonOutput::Terminal
                )),
            None => Err(EngineDefect {
                case: None,
                description: format!(
                    "leaf {index} carries no judgement of the pattern target's matcher"
                ),
            }),
        })
        .collect()
}

/// Whether a case of a `kind` target on `paths` runs as a state set (FZ-STATESET, D35;
/// ARCHITECTURE 5.1): an all-paths rule or pattern target.
///
/// Both read what a state set keeps of every path: a final pattern a configuration at an end,
/// which merging keeps (a state set reports the path set's final configurations, merged leaves
/// carrying the merged diagnostics or the run's lists their facts), and a rule target its
/// run's coverage (the union over every explored path, absorbed arrivals included) or a
/// retained leaf's own trace and terminal halt. A rule fired only on an absorbed arrival's path
/// is judged by [`UnjudgedReason::FiredOffTrace`]. `fired` keeps its terminal rule: under a
/// state set a terminal or stuck leaf then carries every run fact, which only taints more
/// (D36). A pattern `at: any-state` reads the reached states, which k-rust matches inside the
/// run (`matchStates`, FZ-STATESET-MATCH): a state merged into an equal one of its depth has its
/// verdict, so every reached configuration is judged without exploring converging paths twice.
/// One path stays a path set (strategy `any` has nothing to merge); observers fold their state
/// over a path, which the merge key omits. The differential target's sides ask for state sets
/// themselves (`differential::plan`).
pub(crate) fn case_state_set(kind: &TargetKind, paths: PathMode) -> bool {
    paths == PathMode::AllPaths && matches!(kind, TargetKind::Rule(_) | TargetKind::Pattern(_))
}

/// The result modality of each kind of run a campaign of `target` on `paths` makes
/// ([`ExecutionModality`], the report's `identity.execution-modality`).
pub(crate) fn execution_modality(target: &Target, paths: PathMode) -> ExecutionModality {
    let modality = |state_set: bool| {
        if state_set {
            ResultModality::StateSet
        } else {
            ResultModality::PathSet
        }
    };
    match &target.kind {
        TargetKind::Differential(_) => ExecutionModality {
            cases: ResultModality::StateSet,
            every_path: None,
            any_state: None,
        },
        TargetKind::Observer(_) => ExecutionModality {
            cases: ResultModality::PathSet,
            every_path: None,
            any_state: None,
        },
        TargetKind::Rule(_) | TargetKind::Pattern(_) => ExecutionModality {
            cases: modality(case_state_set(&target.kind, paths)),
            every_path: Some(ResultModality::StateSet),
            // The run that matches the reached states is the case's own.
            any_state: matches!(
                &target.kind,
                TargetKind::Pattern(PatternTarget {
                    at: PatternAt::AnyState,
                    ..
                })
            )
            .then(|| modality(case_state_set(&target.kind, paths))),
        },
    }
}

/// Whether a `fired` case's `class` means, among other things, that no path which fired the
/// rule reached a clean end of the kind the target asks for: `miss` (every leaf a clean natural
/// end, none on such a path), `stuck` (no clean leaf on such a path, and one clean abnormal
/// stop) and `reached-unfinished` (only paths that did not end cleanly and naturally fired it,
/// under `run-to-completion`). On a state set that is unjudgeable once some explored path fired
/// the rule off every retained trace, which the committed transitions show (coverage
/// `committed`, FZ-STATESET-MATCH; without them coverage `applied`, which also holds rolled-back
/// candidates, stands for it): an arrival absorbed into a recorded state of its depth may have
/// fired it on its own path, and its continuation is the recorded state's subtree, whose clean
/// end then lies on a path that fired the rule while the end's leaf keeps another arrival's
/// trace (a leaf absorbed by the final merge is such an end itself). Such a case is
/// `unsupported` with [`UnjudgedReason::FiredOffTrace`], unless the leaves decide it either way
/// ([`every_leaf_qualifies`]: a hit of the whole run; [`no_path_ends_naturally`] under
/// `run-to-completion`: `reached-unfinished`). A rule in `applied` and not in `committed` was
/// fired on no explored path, so the class stands.
///
/// The other non-hit classes make no such claim and stand: `depth-bound`, `work-bound` and
/// `timeout` already say that the run is incomplete, and `undefined` names an undefined step a
/// leaf really took. An absorbed hit can therefore surface as one of them (V7).
fn denies_a_clean_reaching_end(class: OutcomeClass) -> bool {
    matches!(
        class,
        OutcomeClass::Miss | OutcomeClass::Stuck | OutcomeClass::ReachedUnfinished
    )
}

/// Whether every leaf of `result` could carry a hit attributed to no leaf, and nothing a path
/// went through is missing from the leaves (FZ-STATESET-MATCH): at least one leaf, every leaf
/// clean (and, under `run_to_completion`, a natural end, and a data end with `data_end`), and no
/// run fact off the leaves.
///
/// On a state set every explored path ends at a leaf of the result, as its configuration and
/// halt: a merged arrival's continuation is the recorded state's subtree, whose leaves are in
/// the result, and the final merge keeps one leaf per configuration of a compatible halt. A path
/// may carry diagnostics its leaf does not show only as path facts (the exploration merge
/// ignores them; any other diagnostic of an absorbed arrival is among the recorded state's),
/// and those are on the run's lists: with every leaf clean, a run fact is on no leaf, so
/// requiring none off the leaves requires none at all. So a path ends at a leaf that may carry a
/// hit, with nothing its own path carried that the leaf does not.
fn every_leaf_qualifies(result: &CaseResult, run_to_completion: bool, data_end: bool) -> bool {
    !result.leaves.is_empty()
        && !result.run_facts_off_leaves
        && result.leaves.iter().all(|leaf| {
            leaf.is_clean()
                && (!run_to_completion
                    || (leaf.natural_end && (!data_end || leaf.data_end == Some(true))))
        })
}

/// The class of an all-paths `fired` case on a state set whose leaves gave `class` (not a hit)
/// from their retained traces and terminal halts, when the run's committed transitions change
/// it ([`ResolvedTarget::judge_run`]): `None` keeps `class`.
///
/// Some explored path fired the rule when it is committed (a run without the committed
/// transitions reads coverage `applied` in their place, conservatively, since that also holds
/// rolled-back candidates). A committed rule is a hit of the whole run when every leaf could
/// carry it ([`every_leaf_qualifies`]), demoted as every hit is outside the determinism
/// contract ([`hit_unless_demoted`]); under `run-to-completion`, a case whose leaves give
/// `stuck`, `undefined` or `reached-unfinished` is `reached-unfinished` when no path ends
/// naturally ([`reached_unfinished_everywhere`]); otherwise a case that fired somewhere and whose class denies a
/// clean reaching end ([`denies_a_clean_reaching_end`]) is `unsupported` with
/// [`UnjudgedReason::FiredOffTrace`].
fn fired_off_retained_traces(
    id: &str,
    result: &CaseResult,
    class: OutcomeClass,
    run_to_completion: bool,
    data_end: bool,
) -> Option<(OutcomeClass, Option<UnjudgedReason>)> {
    let committed = rule::committed(id, result.coverage.as_ref());
    let fired_somewhere = committed.unwrap_or_else(|| rule::applied(id, result.coverage.as_ref()));
    let committed = committed == Some(true);
    if committed && every_leaf_qualifies(result, run_to_completion, data_end) {
        // Every path's end is a leaf of the result, as its configuration and halt, and no leaf
        // carries a fact or a taint a path to it may have carried that it does not show
        // (`every_leaf_qualifies`): a path that fired the rule ends at a leaf that may carry the
        // hit. Which one is not known, so the hit is the run's (D13), and it is demoted as every
        // hit is outside the determinism contract.
        return Some(hit_unless_demoted(result));
    }
    if committed && run_to_completion && reached_unfinished_everywhere(result, class) {
        // Some path fired the rule and no path ends naturally: the target was reached and the
        // run did not end naturally, whichever path reached it.
        return Some((OutcomeClass::ReachedUnfinished, None));
    }
    (fired_somewhere && denies_a_clean_reaching_end(class)).then_some((
        OutcomeClass::Unsupported,
        Some(UnjudgedReason::FiredOffTrace),
    ))
}

/// `hit`, or the class a hit takes in a run outside the determinism contract
/// ([`exec::demoted_hit`], with the first of its reasons): the one demotion every hit goes
/// through, whether the leaves' classification or the run's committed transitions or state
/// matches decided it.
pub(super) fn hit_unless_demoted(result: &CaseResult) -> (OutcomeClass, Option<UnjudgedReason>) {
    match exec::demoted_hit(&result.determinism_breaks()) {
        Some((class, reasons)) => (class, reasons.into_iter().min()),
        None => (OutcomeClass::Hit, None),
    }
}

/// Whether `reached-unfinished` holds of the whole run, whichever path reached the target
/// (FZ-STATESET-MATCH): the leaves' own class (`leaves_class`, from their traces or with no leaf
/// reaching) is one that claims nothing unsupported and no cut (`stuck`, `undefined`, or
/// `reached-unfinished`), and no path ends naturally ([`no_path_ends_naturally`]). A leaf that
/// is unsupported (a fact, an undecided natural end) or cut keeps the class its leaves give.
pub(super) fn reached_unfinished_everywhere(
    result: &CaseResult,
    leaves_class: OutcomeClass,
) -> bool {
    matches!(
        leaves_class,
        OutcomeClass::Stuck | OutcomeClass::Undefined | OutcomeClass::ReachedUnfinished
    ) && no_path_ends_naturally(result)
}

/// Whether no path of `result` ends naturally (FZ-STATESET-MATCH): every leaf is an undefined
/// step (`trivial`) unclean for nothing but its halt, never a natural end, or a clean `stuck`
/// leaf whose natural end is decided false, and no run fact lies off the leaves. No leaf is cut,
/// so every explored path ends at a leaf of the result as its configuration and halt ([`every_leaf_qualifies`]); a `stuck` leaf merges only
/// with leaves of its configuration whose halt it stands for, and whether a clean stuck leaf is
/// a natural end is a property of its configuration. So no path, absorbed or not, reached a
/// natural end, and `reached-unfinished` (some path reached the target, none ended naturally)
/// holds of the run, whichever path reached it.
fn no_path_ends_naturally(result: &CaseResult) -> bool {
    !result.leaves.is_empty()
        && !result.run_facts_off_leaves
        && result.leaves.iter().all(|leaf| match leaf.halt {
            // An undefined step that rests on nothing open: in every model the path ends there.
            HaltReasonOutput::Trivial => !leaf.unclean_beyond_halt(),
            // A decided abnormal stop: its natural end is refuted, not undecided.
            HaltReasonOutput::Stuck => {
                leaf.is_clean() && !leaf.natural_end && !leaf.natural_end_undecided()
            }
            HaltReasonOutput::Cancelled
            | HaltReasonOutput::Vacuous
            | HaltReasonOutput::Branch
            | HaltReasonOutput::CutPoint
            | HaltReasonOutput::Terminal
            | HaltReasonOutput::DepthBound
            | HaltReasonOutput::BreadthBound
            | HaltReasonOutput::WorkBound
            | HaltReasonOutput::Indeterminate
            | HaltReasonOutput::UnsupportedHook
            | HaltReasonOutput::SimplificationError
            | HaltReasonOutput::Timeout => false,
        })
}

impl ResolvedTarget {
    /// Resolve `target` for `executor`'s definition. Rules go through
    /// `Backend::rule_catalog(None)`; an entry with `shared_identity`, with
    /// `executable: false` or with id `UNKNOWN` is refused, and so is an equation in M1. A
    /// pattern compiles to a [`LeafMatcher`]; at `final` its configuration without its
    /// `requires` also compiles to an informational matcher, at `any-state` nothing else does.
    /// An observer target without its observer is refused (`observer::resolve`). A differential
    /// target resolves here to its baseline's part; the pair is judged by
    /// [`differential::judge_pair`].
    ///
    /// # Errors
    ///
    /// [`CampaignError::Target`].
    pub(crate) fn resolve(
        target: &Target,
        executor: &mut Executor,
        definition: &CompiledDefinition,
        assembly: &ProgramAssembly,
    ) -> Result<Self, CampaignError> {
        Self::resolve_with(target, executor, definition, assembly, None)
    }

    /// [`Self::resolve`], with the target's patterns already compiled for this definition
    /// (`compiled`, as [`Self::compiled_patterns`] of an earlier resolution of the same target
    /// gave them), so that only their preparation on `executor`'s backend runs. A compiled
    /// pattern is a function of the definition, the program grammar and the pattern text alone,
    /// so preparing it is the same as compiling it again (FZ-06's confirmation request).
    ///
    /// # Errors
    ///
    /// As [`Self::resolve`].
    pub(crate) fn resolve_with(
        target: &Target,
        executor: &mut Executor,
        definition: &CompiledDefinition,
        assembly: &ProgramAssembly,
        compiled: Option<&[CompiledPattern]>,
    ) -> Result<Self, CampaignError> {
        let mut matchers = Vec::new();
        let resolved = match &target.kind {
            TargetKind::Rule(rule_target) => {
                let catalog = executor.backend_mut().rule_catalog(None).map_err(|error| {
                    CampaignError::Definition {
                        message: format!("the rule catalog is not available: {error}"),
                    }
                })?;
                let (catalog, recorded) = rule::relative_catalog(
                    catalog,
                    &SourceNames::of(&definition.frontend_definition),
                );
                let id = rule::resolve_rule_recorded(&catalog, &rule_target.rule, &recorded)
                    .map_err(CampaignError::Target)?;
                Resolved::Rule {
                    id,
                    mode: rule_target.mode,
                }
            }
            TargetKind::Pattern(pattern) => {
                let pattern_problem =
                    |message| CampaignError::Target(TargetProblem::Pattern(message));
                let matcher = match compiled.and_then(<[CompiledPattern]>::first) {
                    Some(compiled) => LeafMatcher::prepare(executor, compiled),
                    None => LeafMatcher::compile(executor, definition, assembly, &pattern.pattern),
                }
                .map_err(pattern_problem)?;
                match pattern.at {
                    PatternAt::Final => {
                        // The configuration without the `requires`, which only informs: the
                        // report counts the clean ends it matched, so that a pattern no end comes
                        // near (a misspelled key) is told apart from one whose condition fails
                        // (S2).
                        let body = matcher
                            .compiled()
                            .body_only()
                            .map(|body| LeafMatcher::prepare(executor, &body))
                            .transpose()
                            .map_err(pattern_problem)?;
                        matchers.push(matcher);
                        matchers.extend(body.map(LeafMatcher::informational));
                        Resolved::PatternFinal
                    }
                    PatternAt::AnyState => {
                        matchers.push(matcher);
                        Resolved::PatternAnyState
                    }
                }
            }
            TargetKind::Differential(_) => Resolved::Differential,
            TargetKind::Observer(target) => observer::resolve(target, executor)?,
        };
        Ok(Self {
            target: target.clone(),
            resolved,
            matchers,
        })
    }

    /// What every execute request on `paths` must carry for this target: traces for `fired`,
    /// and its rule as the only terminal rule without `run-to-completion`, in both path modes
    /// (ARCHITECTURE 5.1, D16, D18); a state set for an all-paths rule or pattern target
    /// ([`case_state_set`], FZ-STATESET), with the committed transitions for `fired` on it; and
    /// for a pattern `at: any-state` the state matching of its pattern, with proof agreement
    /// unless the pattern evaluates nothing (FZ-STATESET-MATCH).
    ///
    /// The differential target's needs per side come from [`differential::plan`].
    pub(crate) fn needs(&self, paths: PathMode) -> TargetNeeds {
        let state_set = case_state_set(&self.target.kind, paths);
        let needs = match &self.resolved {
            Resolved::Rule { id, mode } => TargetNeeds {
                // A `fired` hit or miss on a state set reads the committed transitions too
                // (`judge_run`).
                collect_committed: state_set && *mode == RuleMode::Fired,
                ..rule::rule_needs(id, *mode, self.target.run_to_completion)
            },
            Resolved::PatternAnyState => {
                // The resolution keeps the target's one matcher, and no informational one.
                let matcher = &self.matchers[0];
                TargetNeeds {
                    match_states: Some(StateMatchNeed {
                        pattern: matcher.kore().clone(),
                        proof_agreement: !matcher.mode_independent(),
                    }),
                    ..TargetNeeds::default()
                }
            }
            Resolved::PatternFinal | Resolved::Differential | Resolved::Observer { .. } => {
                TargetNeeds::default()
            }
        };
        TargetNeeds {
            data_end: self.target.requires_data_end(),
            state_set,
            ..needs
        }
    }

    /// The catalog id of a rule target's rule; `None` for every other kind.
    pub(crate) fn rule_id(&self) -> Option<&str> {
        match &self.resolved {
            Resolved::Rule { id, .. } => Some(id),
            Resolved::PatternFinal
            | Resolved::PatternAnyState
            | Resolved::Differential
            | Resolved::Observer { .. } => None,
        }
    }

    /// The target's patterns compiled for its definition, for [`Self::resolve_with`] on
    /// another backend of the same definition: the target's own pattern, from which the
    /// informational matcher of its configuration is derived again.
    pub(crate) fn compiled_patterns(&self) -> Vec<CompiledPattern> {
        self.matchers
            .iter()
            .take(1)
            .map(|matcher| matcher.compiled().clone())
            .collect()
    }

    /// For a pattern target at `final`, how many end leaves of `result` (`stuck`, `trivial` or
    /// `terminal`) matched the pattern's configuration without its `requires` (the target's
    /// own matcher when the pattern has no `requires`), whatever the `requires` gave there:
    /// true, false or undecided. A leaf counts when it is clean apart from the target
    /// matcher's own undecided verdict ([`UncleanReason::UndecidedMatch`]); a leaf unclean for
    /// any other reason (an undecided or not ceil-free state, an implementation-chosen value, a
    /// contradicted claim, ...) is left out even when its configuration matched, as every
    /// verdict of this campaign leaves it out, so a semantics whose every end is unclean gets a
    /// count of 0. `None` for every other target kind, and at `any-state`, whose configurations
    /// are not counted (FZ-POLISH S2).
    pub(crate) fn pattern_body_matches(&self, result: &CaseResult) -> Option<u64> {
        if self.resolved != Resolved::PatternFinal {
            return None;
        }
        let index = self.matchers.len().saturating_sub(1);
        let count = result
            .leaves
            .iter()
            .filter(|leaf| body_judged(leaf) && leaf.matches.get(index) == Some(&true))
            .count();
        Some(u64::try_from(count).unwrap_or(u64::MAX))
    }

    /// For a pattern target at `final`, how many end leaves of `result` were judged against the
    /// pattern's configuration ([`Self::pattern_body_matches`] counts those that matched): end
    /// leaves clean apart from the target matcher's own undecided verdict. A case with none says
    /// nothing about whether the pattern names a configuration some end holds, so the warning
    /// that no end matched counts only cases with some. 0 for every other target kind.
    pub(crate) fn pattern_body_judged(&self, result: &CaseResult) -> u64 {
        if self.resolved != Resolved::PatternFinal {
            return 0;
        }
        let count = result
            .leaves
            .iter()
            .filter(|leaf| body_judged(leaf))
            .count();
        u64::try_from(count).unwrap_or(u64::MAX)
    }

    /// The leaf matchers [`Executor::run`] must judge for this target, in the order
    /// [`crate::exec::LeafReport::matches`] reports them. None for a pattern at `any-state`,
    /// whose matcher judges configurations, not leaves ([`Executor::run_any_state`]).
    pub(crate) fn matchers(&self) -> Vec<&LeafMatcher> {
        if self.resolved == Resolved::PatternAnyState {
            return Vec::new();
        }
        self.matchers.iter().collect()
    }

    /// [`Self::judge_run`] of a run of one path, for tests.
    #[cfg(test)]
    pub(crate) fn judge(&self, result: &CaseResult) -> Result<Judgement, EngineDefect> {
        self.judge_run(result, false, false)
    }

    /// Judge one case, whose run explored every path when `all_paths` and reported a state set
    /// when `state_set`: decide which leaves reach the target (from traces, terminal halts,
    /// coverage or pattern matches, per mode), then class the case with
    /// [`crate::exec::classify`].
    ///
    /// A hit of a coverage mode on a run of every path names no leaf ([`HitSite::Run`]), even
    /// when one leaf is left: a sibling path whose successor vanished left its applications in
    /// coverage, so the remaining leaf need not be on the path that reached the rule (phase-1
    /// review N7). On one path the run is its leaf's path.
    ///
    /// A `fired` case on a state set that a retained trace or terminal halt does not make a hit
    /// reads the run's committed transitions (FZ-STATESET-MATCH): a rule some explored path
    /// fired, absorbed arrivals included. When the rule is committed and every leaf could carry
    /// a hit with nothing off the leaves ([`every_leaf_qualifies`]), the case is a hit of the
    /// whole run ([`HitSite::Run`]); when it is committed, `run-to-completion` holds and no path
    /// ends naturally ([`no_path_ends_naturally`]), a `stuck` or `reached-unfinished` case is
    /// `reached-unfinished`; otherwise a case that would be `miss`, `stuck` or
    /// `reached-unfinished` is `unsupported` with [`UnjudgedReason::FiredOffTrace`] (FZ-STATESET
    /// B1, [`denies_a_clean_reaching_end`]), and the class it replaces is kept in
    /// [`Judgement::demoted_from`] for the incidental finding. A rule that is applied but not
    /// committed built only rolled-back candidates, and the class stands. A run without the
    /// committed transitions reads coverage `applied` in their place, conservatively. On a path
    /// set every path keeps its leaf, so a rule on no trace was fired on no path, and the class
    /// stands.
    ///
    /// # Errors
    ///
    /// [`EngineDefect`] from classification; for a leaf without the pattern matcher's
    /// judgement; for a differential target, whose cases [`differential::judge_pair`] judges;
    /// for an observer target and a pattern at `any-state`, whose cases [`Self::run_and_judge`]
    /// judges; and for a `hit`
    /// class with no clean reaching leaf.
    pub(crate) fn judge_run(
        &self,
        result: &CaseResult,
        all_paths: bool,
        state_set: bool,
    ) -> Result<Judgement, EngineDefect> {
        let run_to_completion = self.target.run_to_completion;
        let data_end = self.target.requires_data_end();
        let (reached, blocked) = match &self.resolved {
            Resolved::Rule { id, mode } => (
                rule::rule_reached_ends(id, *mode, run_to_completion, data_end, result),
                rule::blocked(id, result.coverage.as_ref()),
            ),
            Resolved::PatternFinal => (pattern_reached(result)?, false),
            Resolved::Differential => {
                return Err(EngineDefect {
                    case: None,
                    description: "a differential case was judged as a single run".to_owned(),
                });
            }
            Resolved::Observer { .. } => {
                return Err(EngineDefect {
                    case: None,
                    description: "an observer case was judged without its observed run".to_owned(),
                });
            }
            Resolved::PatternAnyState => {
                return Err(EngineDefect {
                    case: None,
                    description: "an any-state case was judged without its observed run".to_owned(),
                });
            }
        };
        let coverage_mode = matches!(
            &self.resolved,
            Resolved::Rule {
                mode: RuleMode::Covered | RuleMode::ConditionReached,
                ..
            }
        );
        let (mut class, mut reason) =
            exec::classify_ends_explained(result, &reached, run_to_completion, data_end)?;
        if class == OutcomeClass::Hit && coverage_mode && result.run_facts_off_leaves {
            // A candidate that vanished from every leaf (its successor was no state, and a
            // sibling took its instances) left its applications in coverage and its facts on no
            // leaf, so the coverage fact may rest on that unclean work (ARCHITECTURE 5.3, D18).
            class = OutcomeClass::Unsupported;
            reason = Some(UnjudgedReason::RunFactOffLeaves);
        }
        let mut demoted_from = None;
        let mut run_hit = false;
        if let Resolved::Rule {
            id,
            mode: RuleMode::Fired,
        } = &self.resolved
            && state_set
            && class != OutcomeClass::Hit
            && let Some((judged, why)) =
                fired_off_retained_traces(id, result, class, run_to_completion, data_end)
        {
            run_hit = judged == OutcomeClass::Hit;
            demoted_from = (why == Some(UnjudgedReason::FiredOffTrace)).then_some(class);
            (class, reason) = (judged, why);
        }
        let hit_site = if run_hit {
            Some(HitSite::Run)
        } else if class == OutcomeClass::Hit {
            let leaf = result
                .leaves
                .iter()
                .zip(&reached)
                .position(|(leaf, reached)| {
                    *reached
                        && leaf.is_clean()
                        && (!run_to_completion || leaf.natural_end)
                        && (!data_end || leaf.data_end == Some(true))
                });
            let Some(leaf) = leaf else {
                return Err(EngineDefect {
                    case: None,
                    description: "a case classed `hit` has no clean leaf that reaches the target"
                        .to_owned(),
                });
            };
            // Run coverage over several leaves, or over all paths, names no leaf (D13): the
            // hit is the run's.
            let run_level = coverage_mode && (all_paths || result.leaves.len() > 1);
            Some(if run_level {
                HitSite::Run
            } else {
                HitSite::Leaf(leaf)
            })
        } else {
            None
        };
        let judgement = Judgement {
            class,
            hit_site,
            blocked,
            reason,
            demoted_from,
        };
        let term_conjunction = match hit_site {
            Some(HitSite::Leaf(index)) => result.leaves[index].term_conjunction,
            Some(HitSite::Run | HitSite::StateMatch { .. }) | None => false,
        };
        Ok(self.confirmable(judgement, result, term_conjunction))
    }
}

/// Whether `leaf`'s configuration is judged against a final pattern's
/// ([`ResolvedTarget::pattern_body_matches`], [`ResolvedTarget::pattern_body_judged`]): a leaf
/// clean apart from the target matcher's own undecided verdict and an undecided natural end.
/// Only a `stuck` leaf, or a `terminal` one at the target's own stop rule, can be: every other
/// halt, `trivial` (an undefined step) included, carries [`UncleanReason::Halt`]. The halt test
/// is kept so that the filter does not rest on that.
fn body_judged(leaf: &crate::exec::LeafReport) -> bool {
    matches!(
        leaf.halt,
        HaltReasonOutput::Stuck | HaltReasonOutput::Trivial | HaltReasonOutput::Terminal
    ) && leaf.unclean.iter().all(|reason| {
        matches!(
            reason,
            UncleanReason::NaturalEndUndecided | UncleanReason::UndecidedMatch
        )
    })
}
