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
#[cfg(test)]
pub(crate) use rule::resolve_rule;

use crate::{
    assemble::ProgramAssembly,
    error::{CampaignError, TargetProblem},
    exec::{
        self, CaseResult, CompiledPattern, Executor, LeafMatcher, OutcomeClass, TargetNeeds,
        UncleanReason, UnjudgedReason,
    },
    report::EngineDefect,
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
    /// of stack, also in the definition's load), and that the matched state holds no term-level
    /// `\and` (P7-ADDENDUM section 4, conditions Q2', Q4', Q5';
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
    /// The source file as the catalog records it (the path inside its `Source(path)` text).
    pub source: String,
    /// The shortest reference that names this file alone among the catalog's files: its
    /// shortest suffix after a `/`, or the whole path ([`RuleRef::Source`]).
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
    /// Any normalized configuration on an explored path, the initial one included: one that is
    /// decided, ceil-free and matches with empty constraints, on the path of a leaf that ends
    /// cleanly (naturally under `run-to-completion`). The witness records the step of the first
    /// such configuration on the hit leaf's path. The case runs through observed execution,
    /// which costs more than `final` (`any_state` module documentation).
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
    /// configuration, without a single final configuration.
    Run,
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
                let id = rule::resolve_rule(&catalog, &rule_target.rule)
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
    /// (ARCHITECTURE 5.1, D16, D18). The needs do not depend on the path mode since D18; the
    /// parameter keeps the request shape's inputs in one place.
    ///
    /// The differential target's needs per side come from [`differential::plan`].
    pub(crate) fn needs(&self, _paths: PathMode) -> TargetNeeds {
        let needs = match &self.resolved {
            Resolved::Rule { id, mode } => {
                rule::rule_needs(id, *mode, self.target.run_to_completion)
            }
            Resolved::PatternFinal
            | Resolved::PatternAnyState
            | Resolved::Differential
            | Resolved::Observer { .. } => TargetNeeds::default(),
        };
        TargetNeeds {
            data_end: self.target.requires_data_end(),
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
            .filter(|leaf| {
                matches!(
                    leaf.halt,
                    HaltReasonOutput::Stuck
                        | HaltReasonOutput::Trivial
                        | HaltReasonOutput::Terminal
                ) && leaf.unclean.iter().all(|reason| {
                    matches!(
                        reason,
                        UncleanReason::NaturalEndUndecided | UncleanReason::UndecidedMatch
                    )
                }) && leaf.matches.get(index) == Some(&true)
            })
            .count();
        Some(u64::try_from(count).unwrap_or(u64::MAX))
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
        self.judge_run(result, false)
    }

    /// Judge one case, whose run explored every path when `all_paths`: decide which leaves
    /// reach the target (from traces, terminal halts, coverage or pattern matches, per mode),
    /// then class the case with [`crate::exec::classify`].
    ///
    /// A hit of a coverage mode on a run of every path names no leaf ([`HitSite::Run`]), even
    /// when one leaf is left: a sibling path whose successor vanished left its applications in
    /// coverage, so the remaining leaf need not be on the path that reached the rule (phase-1
    /// review N7). On one path the run is its leaf's path.
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
        let hit_site = if class == OutcomeClass::Hit {
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
        };
        let term_conjunction = match hit_site {
            Some(HitSite::Leaf(index)) => result.leaves[index].term_conjunction,
            Some(HitSite::Run) | None => false,
        };
        Ok(self.confirmable(judgement, result, term_conjunction))
    }
}
