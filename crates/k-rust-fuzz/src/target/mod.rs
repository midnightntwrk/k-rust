//! Targets: what a case must do to be a hit, their resolution against a definition, and the
//! judgement of a case result (ARCHITECTURE 4). Owner: FZ-05; the differential judge is FZ-08's
//! ([`differential`]); the observer target is FZ-10's.
//!
//! Every target is an existential goal. A universal property is stated as the target "a clean
//! natural end violates P", with [`Target::negated_property`] set, and its hit is reported as a
//! property failure (ARCHITECTURE 4).

pub(crate) mod differential;
#[cfg(test)]
mod fixture_tests;
mod rule;
#[cfg(test)]
mod tests;

use serde::{Deserialize, Serialize};

use crate::{
    assemble::ProgramAssembly,
    error::{CampaignError, TargetProblem},
    exec::{self, CaseResult, Executor, LeafMatcher, OutcomeClass, TargetNeeds},
    report::EngineDefect,
    spec::CompiledDefinition,
};

/// A campaign's target (ARCHITECTURE 4.1).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
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
}

/// The kinds of target (ARCHITECTURE 4.1).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum TargetKind {
    /// A rewrite rule fires, is covered, or has its condition reached (ARCHITECTURE 4.2).
    Rule(RuleTarget),
    /// A configuration matches a compiled pattern (ARCHITECTURE 4.1).
    Pattern(PatternTarget),
    /// The mutant reaches a clean end the baseline cannot reach on the same input
    /// (ARCHITECTURE 4.3).
    Differential(DifferentialTarget),
    /// A client observer accepts (ARCHITECTURE 4.1, 9.2); refused until FZ-10.
    Observer(ObserverTarget),
}

/// A rule target (ARCHITECTURE 4.2).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
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
#[serde(tag = "by", content = "value", rename_all = "kebab-case")]
pub enum RuleRef {
    /// The rule's label as the catalog writes it (`IMP.overflow`), or, when no entry has that
    /// label, the label without its module (`overflow`).
    Label(String),
    /// The rule's unique id (`UNIQUE_ID`).
    UniqueId(String),
    /// The rule's source position: a catalog origin with this `source` whose `location` starts
    /// on `line`.
    Source {
        /// The source file: the catalog's `Source(path)` text, the path inside it, or a suffix
        /// of that path that starts after a `/` (`rules.k` for `Source(tests/rules/rules.k)`).
        source: String,
        /// The one-based line the rule starts on.
        line: u32,
    },
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
#[serde(rename_all = "kebab-case")]
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
    /// Any state on the explored path; needs G-4 and is refused until then.
    AnyState,
}

/// The differential target's options (ARCHITECTURE 4.3); the two definitions are
/// [`crate::Definitions::baseline`] and [`crate::Definitions::mutant`]. The mutant runs on the
/// campaign's path mode; the baseline always runs all paths.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct DifferentialTarget {}

/// Placeholder for the observer target, which FZ-10 defines with the `Observer` trait of
/// ARCHITECTURE 9.2; [`crate::Campaign::new`] refuses it until then.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct ObserverTarget {}

/// The judgement of one case against a resolved target.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Judgement {
    /// The case's class.
    pub(crate) class: OutcomeClass,
    /// For a hit, the index of the clean leaf that reaches the target.
    pub(crate) hit_leaf: Option<usize>,
    /// The target rule is in coverage `matched` but not `applied`: its condition was entered
    /// and it built no successor (a blocked rule, ARCHITECTURE 6.2).
    pub(crate) blocked: bool,
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
    /// The differential target, judged by [`differential::judge_pair`].
    Differential,
}

/// For each leaf of `result`, whether it matches the target's only matcher (ARCHITECTURE 4.1,
/// `at: final`).
///
/// [`crate::exec::LeafReport::matches`] is judged on every leaf whose state can be decided,
/// clean or not, so that a matching leaf that is not clean classes as `unsupported`, never as
/// `miss` (ARCHITECTURE 5.3). Whether a hit may rest on the leaf (clean, and a natural end under
/// `run-to-completion`) is [`crate::exec::classify`]'s question.
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
            Some(matched) => Ok(*matched),
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
    /// pattern compiles to a [`LeafMatcher`]. `at: any-state` and observers are refused until
    /// their tickets land. A differential target resolves here to its baseline's part; the pair
    /// is judged by [`differential::judge_pair`].
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
            TargetKind::Pattern(pattern) => match pattern.at {
                PatternAt::Final => {
                    matchers.push(
                        LeafMatcher::compile(executor, definition, assembly, &pattern.pattern)
                            .map_err(|message| {
                                CampaignError::Target(TargetProblem::Pattern(message))
                            })?,
                    );
                    Resolved::PatternFinal
                }
                PatternAt::AnyState => {
                    return Err(CampaignError::Target(TargetProblem::Unsupported(
                        "`at: any-state` needs a one-path search over the explored states \
                         (gap G-4)"
                            .to_owned(),
                    )));
                }
            },
            TargetKind::Differential(_) => Resolved::Differential,
            TargetKind::Observer(_) => {
                return Err(CampaignError::Target(TargetProblem::Unsupported(
                    "observer targets are not provided before FZ-10".to_owned(),
                )));
            }
        };
        Ok(Self {
            target: target.clone(),
            resolved,
            matchers,
        })
    }

    /// What every execute request must carry for this target (traces and terminal rules for
    /// `fired` without `run-to-completion`; ARCHITECTURE 5.1).
    ///
    /// The differential target's needs per side come from [`differential::plan`].
    pub(crate) fn needs(&self) -> TargetNeeds {
        match &self.resolved {
            Resolved::Rule { id, mode } => {
                rule::rule_needs(id, *mode, self.target.run_to_completion)
            }
            Resolved::PatternFinal | Resolved::Differential => TargetNeeds::default(),
        }
    }

    /// The leaf matchers [`Executor::run`] must judge for this target, in the order
    /// [`crate::exec::LeafReport::matches`] reports them.
    pub(crate) fn matchers(&self) -> Vec<&LeafMatcher> {
        self.matchers.iter().collect()
    }

    /// Judge one case: decide which leaves reach the target (from traces, terminal halts,
    /// coverage or pattern matches, per mode), then class the case with
    /// [`crate::exec::classify`].
    ///
    /// # Errors
    ///
    /// [`EngineDefect`] from classification; for a leaf without the pattern matcher's
    /// judgement; for a differential target, whose cases [`differential::judge_pair`] judges;
    /// and for a `hit` class with no clean reaching leaf.
    pub(crate) fn judge(&self, result: &CaseResult) -> Result<Judgement, EngineDefect> {
        let run_to_completion = self.target.run_to_completion;
        let (reached, blocked) = match &self.resolved {
            Resolved::Rule { id, mode } => (
                rule::rule_reached(id, *mode, run_to_completion, result),
                rule::blocked(id, result.coverage.as_ref()),
            ),
            Resolved::PatternFinal => (pattern_reached(result)?, false),
            Resolved::Differential => {
                return Err(EngineDefect {
                    case: None,
                    description: "a differential case was judged as a single run".to_owned(),
                });
            }
        };
        let class = exec::classify(result, &reached, run_to_completion)?;
        let hit_leaf = if class == OutcomeClass::Hit {
            let leaf = result
                .leaves
                .iter()
                .zip(&reached)
                .position(|(leaf, reached)| {
                    *reached && leaf.is_clean() && (!run_to_completion || leaf.natural_end)
                });
            if leaf.is_none() {
                return Err(EngineDefect {
                    case: None,
                    description: "a case classed `hit` has no clean leaf that reaches the target"
                        .to_owned(),
                });
            }
            leaf
        } else {
            None
        };
        Ok(Judgement {
            class,
            hit_leaf,
            blocked,
        })
    }
}
