//! The engine: campaign validation, the loop over cases, the proposer schedule, the budget,
//! confirmation, shrinking and the report (ARCHITECTURE 1, 7, 8, 9.2, 9.3). Owner: FZ-06.

mod campaign_loop;
mod live;
pub(crate) mod proposer;
mod runner;
mod schedule;
mod shrink;
#[cfg(test)]
mod tests;

use std::sync::{Arc, OnceLock};

use k_rust::backend::CancellationToken;

pub(crate) use self::schedule::derive_seed;
use self::{
    campaign_loop::{Cuts, Ending, LoopSettings, no_witness, report_without_cases, run_loop},
    live::{GraphCheck, LiveCases, LiveRunner},
    proposer::{BlindProposer, Proposer},
    schedule::Schedule,
};
use crate::{
    assemble::build_backend,
    error::CampaignError,
    graph::RuleGraph,
    holes::ResolvedHole,
    proposers::{
        climb::{ClimbHole, ClimbProposer},
        dictionary::{self, DictionaryProposer, HolePool},
    },
    report::{
        CampaignOutcome, ClimbParameters, DefinitionIdentity, DefinitionRole, DictionaryParameters,
        FuzzReport, GenerationCaps, HitLabel, ReportIdentity, Totals, digest_hex,
    },
    score::RuleScorer,
    spec::{
        BackendRoute, Budget, CampaignSpec, CaseOptions, CompiledDefinition, ProgramInput,
        ProposerConfig, ProposerKind,
    },
    target::{PatternAt, RuleMode, TargetKind, differential},
    values::{self, Generator, Value, ValueRng},
};

/// A validated campaign (ARCHITECTURE 9.2).
///
/// [`Campaign::new`] resolves the holes, the target and the definitions once; [`Campaign::run`]
/// runs cases on the calling thread until the budget is spent, a witness is confirmed, the
/// rejection cap is reached or the caller cancels.
pub struct Campaign {
    spec: Arc<CampaignSpec>,
    /// The case execution [`Campaign::new`] built, which the first run uses; later runs build
    /// their own.
    cases: Option<LiveCases>,
    explicit: Vec<Vec<Value>>,
    settings: LoopSettings,
    /// Differential: the definitions are equivalent, so no case runs (ARCHITECTURE 4.3).
    equivalent: bool,
    /// The immutable internalized definitions confirmations build fresh backends from, filled
    /// on the first confirmation and kept across runs.
    definition_cache: Arc<OnceLock<Result<live::DefinitionCache, String>>>,
    /// The rule graph and the campaign's entry, computed once in [`Campaign::new`] on a backend
    /// of their own, for the report's warnings and the per-case self-check (ARCHITECTURE 6.3).
    graph: Option<Arc<GraphCheck>>,
    /// The dictionary's pool of each hole (ARCHITECTURE 8.3), harvested once in
    /// [`Campaign::new`] when the dictionary has a positive weight.
    dictionary: Option<Arc<Vec<HolePool>>>,
}

impl Campaign {
    /// Validate `spec` (ARCHITECTURE 9.2): check that a mutant is given exactly for a
    /// differential target and that every weighted proposer is provided, build each
    /// definition's backend on its route and its program assembly, resolve the holes
    /// ([`crate::holes`]) and their generators ([`crate::values`]), resolve the target
    /// ([`crate::target`]), check the explicit assignments against the holes' constraints, and
    /// assemble and round-trip-check the program with its anchor values.
    ///
    /// The backend's acceptance of the anchors' initial state is not executed here: the first
    /// case runs it, and a refusal is a `rejected` case with the reason `backend-refused`.
    ///
    /// # Errors
    ///
    /// [`CampaignError`] for every refusal ARCHITECTURE 9.2 lists: a hole whose `find` or
    /// `literal` does not occur exactly once, overlapping spans, an anchor that does not parse
    /// back, a refused hole sort, explicit assignments that violate their constraints, an
    /// unknown, ambiguous or refused target, a hole sort missing on one side of a differential,
    /// and a program that does not assemble with its anchor values. In a differential campaign
    /// the program must assemble with its anchor values on the mutant too, since each hole's
    /// position is located on both sides: a mutant whose grammar refuses the anchor program is
    /// a [`CampaignError::Program`] or [`CampaignError::AnchorDoesNotParse`], not a campaign of
    /// rejected cases. Other values the mutant refuses make their cases `rejected`.
    pub fn new(spec: CampaignSpec) -> Result<Campaign, CampaignError> {
        check_definitions(&spec)?;
        check_proposers(&spec.proposers)?;
        if spec.rejection_cap == 0 {
            return Err(CampaignError::InvalidOptions {
                message: "the rejection cap must be at least 1: a cap of 0 would end the campaign \
                          before its first case"
                    .into(),
            });
        }
        let spec = Arc::new(spec);
        let cases = LiveCases::build(Arc::clone(&spec))?;
        let holes = &cases.baseline.holes.holes;
        let names: Vec<String> = holes.iter().map(|hole| hole.decl.name.clone()).collect();
        let anchors: Vec<Option<Value>> = holes.iter().map(|hole| hole.anchor.clone()).collect();
        for (index, assignment) in spec.proposers.explicit.iter().enumerate() {
            for hole in holes {
                if let Some(value) = assignment.get(&hole.decl.name) {
                    values::check_constraints(value, &hole.sort, &hole.decl.constraints).map_err(
                        |message| CampaignError::ExplicitAssignment {
                            index,
                            hole: hole.decl.name.clone(),
                            message,
                        },
                    )?;
                }
            }
        }
        let explicit = explicit_proposals(&names, &anchors, &spec.proposers)?;
        generators(&cases, &spec)?;
        // Each side's initial configuration at the anchors, or at the first explicit
        // assignment when some hole has no anchor, identifies its grammar (FZ-06 review S2).
        let known = anchors
            .iter()
            .cloned()
            .collect::<Option<Vec<Value>>>()
            .or_else(|| explicit.first().cloned());
        let mut initial = Vec::new();
        if let Some(values) = known {
            for (side, configuration) in cases
                .initial_configurations(&values)
                .into_iter()
                .enumerate()
            {
                match configuration {
                    Ok(configuration) => {
                        initial.push(Some(digest_hex(configuration.to_string().as_bytes())));
                    }
                    Err(reason) if side == 0 => {
                        return Err(CampaignError::Program {
                            message: format!(
                                "the program with its anchor values is refused: {reason:?}"
                            ),
                        });
                    }
                    // `LiveCases::build` already refused a mutant that does not assemble the
                    // program with its anchors (`RoundTripCheck::new` locates each hole on both
                    // sides). A mutant that prints or round-trips the anchors differently
                    // reaches here: it refuses those cases, and the frontend digest still
                    // identifies its grammar.
                    Err(_) => initial.push(None),
                }
            }
        }
        let equivalent = match &spec.definitions.mutant {
            Some(mutant) => differential::equivalent(&spec.definitions.baseline, mutant)?,
            None => false,
        };
        let graph = GraphCheck::build(&spec, &cases).map(Arc::new);
        let dictionary = (weight(&spec.proposers, ProposerKind::Dictionary) > 0)
            .then(|| dictionary_pools(&spec, &cases, graph.as_deref()))
            .transpose()?
            .map(Arc::new);
        let scorer = climb_scorer(&spec, &cases, graph.as_deref())?;
        let settings = LoopSettings {
            identity: identity(&spec, &initial)?,
            rejection_cap: spec.rejection_cap,
            options: spec.options.clone(),
            label: if spec.target.negated_property {
                HitLabel::PropertyFailure
            } else {
                HitLabel::Hit
            },
            clean_leaf_facts: clean_leaf_facts(&spec),
            constraints: holes
                .iter()
                .map(|hole| hole.decl.constraints.clone())
                .collect(),
            sort_overrides: holes
                .iter()
                .flat_map(ResolvedHole::sort_overrides)
                .collect(),
            warnings: graph
                .as_ref()
                .map(|graph| graph.warnings().to_vec())
                .unwrap_or_default(),
            scorer,
        };
        Ok(Campaign {
            spec,
            cases: Some(cases),
            explicit,
            settings,
            equivalent,
            definition_cache: Arc::new(OnceLock::new()),
            graph,
            dictionary,
        })
    }

    /// The specification this campaign was built from.
    #[must_use]
    pub fn spec(&self) -> &CampaignSpec {
        &self.spec
    }

    /// Run cases until `budget` is spent, a witness is confirmed and shrunk, the rejection cap
    /// is reached, or `cancel` is cancelled (ARCHITECTURE 9.2).
    ///
    /// Every case runs on the calling thread. `Budget::Work` charges every execution:
    /// confirmation, shrinking and both sides of a differential case included, and at least 1
    /// per case. The explicit proposer tries the anchors first (ARCHITECTURE 8.1); the other
    /// proposers are mixed by a deterministic schedule seeded from the campaign seed. A
    /// candidate hit becomes a witness only after a confirmation on a fresh backend agrees; a
    /// disagreement is an engine defect (ARCHITECTURE 7).
    ///
    /// Each run starts from fresh proposer state, and every run after the first also from
    /// fresh backends and assemblies, so a second run reports exactly what a fresh campaign
    /// with the same spec and budget reports: no solver cache or proposer state carries over
    /// (ARCHITECTURE 5.4).
    ///
    /// # Panics
    ///
    /// Never: [`Campaign::new`] built every hole's generator from the same holes and bounds,
    /// so building them again cannot fail.
    #[expect(
        clippy::needless_pass_by_value,
        reason = "ARCHITECTURE 9.2 fixes this signature; a token is a shared handle"
    )]
    pub fn run(&mut self, budget: Budget, cancel: Option<CancellationToken>) -> FuzzReport {
        if self.equivalent {
            return report_without_cases(&self.settings, budget, CampaignOutcome::Equivalent);
        }
        let mut cases = match self.cases.take() {
            Some(cases) => cases,
            None => match LiveCases::build(Arc::clone(&self.spec)) {
                Ok(cases) => cases,
                Err(error) => {
                    let no_witness = no_witness(
                        Ending::Aborted,
                        &Totals::default(),
                        &Cuts::default(),
                        budget,
                        &self.spec.options,
                        self.spec.rejection_cap,
                    );
                    return report_without_cases(
                        &self.settings,
                        budget,
                        CampaignOutcome::Aborted {
                            reason: format!("the campaign's backends did not rebuild: {error}"),
                            no_witness,
                        },
                    );
                }
            },
        };
        // The climb's score reads the condition entries of the target and its predecessors;
        // only a climbing campaign asks for them, so no other campaign's cases change.
        if let Some(scorer) = &self.settings.scorer {
            cases.request_conditions(scorer.condition_rules());
        }
        let generators = generators(&cases, &self.spec).expect("Campaign::new built them");
        // Campaign::new refused every other weighted proposer; the schedule takes them in
        // ProposerKind order when there are several.
        let mut proposers: Vec<(u32, Box<dyn Proposer>)> = Vec::new();
        if let Some(&weight) = self.spec.proposers.weights.get(&ProposerKind::Blind)
            && weight > 0
        {
            let rng = ValueRng::from_seed(derive_seed(self.spec.seed, "values"));
            proposers.push((weight, Box::new(BlindProposer::new(generators, rng))));
        }
        if let Some(pools) = &self.dictionary {
            let generators =
                self::generators(&cases, &self.spec).expect("Campaign::new built them");
            let proposer = DictionaryProposer::new(Arc::clone(pools), generators, self.spec.seed);
            proposers.push((
                weight(&self.spec.proposers, ProposerKind::Dictionary),
                Box::new(proposer),
            ));
        }
        if self.settings.scorer.is_some() {
            let generators =
                self::generators(&cases, &self.spec).expect("Campaign::new built them");
            let holes = cases
                .baseline
                .holes
                .holes
                .iter()
                .zip(generators)
                .map(|(hole, generator)| ClimbHole {
                    sort: hole.sort.clone(),
                    constraints: hole.decl.constraints.clone(),
                    generator,
                })
                .collect();
            let proposer = ClimbProposer::new(holes, self.spec.bounds, self.spec.seed);
            proposers.push((
                weight(&self.spec.proposers, ProposerKind::Climb),
                Box::new(proposer),
            ));
        }
        let mut schedule = Schedule::new(self.spec.seed, self.explicit.clone(), proposers);
        // One assembler per side for the whole run, so that every case reuses its parsers.
        let parts = cases.assembly_parts();
        let mut runner = LiveRunner {
            cases,
            assemblers: parts.assemblers(),
            cache: Arc::clone(&self.definition_cache),
            graph: self.graph.clone(),
        };
        run_loop(
            &mut runner,
            &mut schedule,
            &self.settings,
            budget,
            cancel.as_ref(),
        )
    }
}

/// The dictionary's pool of each hole (ARCHITECTURE 8.3), harvested from the campaign's rule
/// graph `graph`, or from a graph of the campaign's one internalization when there is no graph
/// check (a differential campaign, a template that does not build); only the
/// `from-definition` route makes the dictionary build a backend and graph of its own.
fn dictionary_pools(
    spec: &CampaignSpec,
    cases: &LiveCases,
    graph: Option<&GraphCheck>,
) -> Result<Vec<HolePool>, CampaignError> {
    let holes = &cases.baseline.holes.holes;
    let target = cases.target_rule_id();
    let harvest = match (graph, cases.baseline_internalized()) {
        (Some(check), _) => dictionary::harvest(spec, check.graph(), target)?,
        (None, Some(definition)) => dictionary::harvest(spec, &RuleGraph::new(definition), target)?,
        (None, None) => return dictionary::hole_pools(spec, holes),
    };
    Ok(dictionary::pools(&harvest, spec, holes))
}

/// The scorer of a climbing campaign's target (ARCHITECTURE 6.4; `crate::score`), or `None`
/// when the climb has no weight. It is built over the
/// campaign's rule graph `graph`, or a graph of the campaign's one internalization when there is
/// no graph check, or, on the `from-definition` route without one, a graph of a backend of its
/// own.
///
/// # Errors
///
/// [`CampaignError::InvalidOptions`] for a target that is not a rule: the signals a pattern,
/// differential or observer score needs are not reported yet (FZ-12 report); and
/// [`CampaignError::Definition`] when the rule graph cannot be built.
fn climb_scorer(
    spec: &CampaignSpec,
    cases: &LiveCases,
    graph: Option<&GraphCheck>,
) -> Result<Option<RuleScorer>, CampaignError> {
    if weight(&spec.proposers, ProposerKind::Climb) == 0 {
        return Ok(None);
    }
    let (TargetKind::Rule(_), Some(target)) = (&spec.target.kind, cases.target_rule_id()) else {
        return Err(CampaignError::InvalidOptions {
            message: "the climb proposer scores rule targets only in this milestone: a pattern, \
                      differential or observer target gives it no score"
                .into(),
        });
    };
    Ok(Some(match (graph, cases.baseline_internalized()) {
        (Some(check), _) => RuleScorer::new(check.graph(), target),
        (None, Some(definition)) => RuleScorer::new(&RuleGraph::new(definition), target),
        (None, None) => {
            let mut backend =
                build_backend(&spec.definitions.baseline, spec.options.backend.options())?;
            let graph =
                RuleGraph::of_backend(&mut backend).map_err(|error| CampaignError::Definition {
                    message: format!("the rule graph is not available: {error}"),
                })?;
            RuleScorer::new(&graph, target)
        }
    }))
}

/// A mutant is given exactly when the target is differential.
fn check_definitions(spec: &CampaignSpec) -> Result<(), CampaignError> {
    let differential = matches!(spec.target.kind, TargetKind::Differential(_));
    if differential == spec.definitions.mutant.is_some() {
        Ok(())
    } else {
        Err(CampaignError::DefinitionsMismatch)
    }
}

/// Every proposer with a positive weight is one this build provides: blind sampling, the
/// dictionary and the climb (ARCHITECTURE 8, 11); and the climb, which climbs from cases other
/// proposers make and spends at most half of the budget, comes with blind sampling or the
/// dictionary.
fn check_proposers(config: &ProposerConfig) -> Result<(), CampaignError> {
    if weight(config, ProposerKind::Climb) > 0
        && weight(config, ProposerKind::Blind) == 0
        && weight(config, ProposerKind::Dictionary) == 0
    {
        return Err(CampaignError::InvalidOptions {
            message: "the climb proposer climbs from the cases of blind sampling or the \
                      dictionary and spends at most half of the budget: give one of them a \
                      positive weight"
                .into(),
        });
    }
    for (kind, weight) in &config.weights {
        if *weight > 0
            && !matches!(
                kind,
                ProposerKind::Blind | ProposerKind::Dictionary | ProposerKind::Climb
            )
        {
            let name = serde_json::to_value(kind)
                .ok()
                .and_then(|name| name.as_str().map(str::to_owned))
                .unwrap_or_default();
            return Err(CampaignError::InvalidOptions {
                message: format!("the {name} proposer is not provided in this milestone"),
            });
        }
    }
    Ok(())
}

/// The weight of `kind` in `config`, 0 when it has none.
fn weight(config: &ProposerConfig, kind: ProposerKind) -> u32 {
    config.weights.get(&kind).copied().unwrap_or(0)
}

/// One generator per hole, in hole order.
fn generators(cases: &LiveCases, spec: &CampaignSpec) -> Result<Vec<Generator>, CampaignError> {
    cases
        .baseline
        .holes
        .holes
        .iter()
        .map(|hole| {
            Generator::new(&hole.sort, &hole.decl.constraints, &spec.bounds).map_err(|message| {
                CampaignError::InvalidConstraints {
                    hole: hole.decl.name.clone(),
                    message,
                }
            })
        })
        .collect()
}

/// The report identity of `spec`, with a placeholder budget the loop replaces
/// (ARCHITECTURE 5.4, 9.3).
fn identity(
    spec: &CampaignSpec,
    initial: &[Option<String>],
) -> Result<ReportIdentity, CampaignError> {
    let definition = |role,
                      definition: &CompiledDefinition,
                      initial: Option<&Option<String>>|
     -> Result<_, CampaignError> {
        let (route, order) = match &definition.route {
            BackendRoute::SourceExecution {
                execution_rewrite_order,
            } => (
                "source-execution",
                Some(digest_hex(execution_rewrite_order.join("\n").as_bytes())),
            ),
            BackendRoute::FromDefinition => ("from-definition", None),
        };
        Ok(DefinitionIdentity {
            role,
            main_module: definition.main_module.clone(),
            syntax_module: definition.syntax_module.clone(),
            frontend_digest: debug_digest(&definition.frontend_definition),
            execution_definition_digest: debug_digest(&definition.execution_definition),
            syntax_definition_digest: digest_hex(
                format!(
                    "{}\n{}",
                    definition.syntax_definition_kore, definition.macros_kore
                )
                .as_bytes(),
            ),
            initial_configuration_digest: initial.cloned().flatten(),
            execution_digest: definition.execution_digest()?.to_string(),
            route: route.into(),
            execution_rewrite_order_digest: order,
        })
    };
    let mut definitions = vec![definition(
        DefinitionRole::Baseline,
        &spec.definitions.baseline,
        initial.first(),
    )?];
    if let Some(mutant) = &spec.definitions.mutant {
        definitions.push(definition(DefinitionRole::Mutant, mutant, initial.get(1))?);
    }
    let program = match &spec.program {
        ProgramInput::Source(source) => format!("source:{}", json(source)),
        ProgramInput::KoreTemplate(pattern) => format!("kore:{pattern}"),
    };
    Ok(ReportIdentity {
        engine_version: crate::ENGINE_VERSION,
        k_rust_revision: spec.identity.k_rust_revision.clone(),
        definitions,
        program_digest: digest_hex(program.as_bytes()),
        overlay_digest: digest_hex(json(&spec.holes).as_bytes()),
        target_digest: digest_hex(json(&spec.target).as_bytes()),
        options: CaseOptions {
            max_work: spec.options.effective_max_work(),
            ..spec.options.clone()
        },
        proposers: spec.proposers.clone(),
        bounds: spec.bounds,
        caps: GenerationCaps::current(),
        rejection_cap: spec.rejection_cap,
        seed: spec.seed,
        budget: Budget::Cases(0),
        thread_stack_size: spec.identity.thread_stack_size,
        // k-rust's solver feature, whatever enabled it (Cargo unifies features across a build).
        solver: if k_rust::Z3_INFERENCE { "z3" } else { "none" }.into(),
        dictionary: (weight(&spec.proposers, ProposerKind::Dictionary) > 0)
            .then(DictionaryParameters::current),
        climb: (weight(&spec.proposers, ProposerKind::Climb) > 0).then(ClimbParameters::current),
    })
}

/// [`digest_hex`] of `value`'s `Debug` rendering, streamed into the hash. The frontend
/// definition types hold only ordered containers, so the rendering is deterministic for one
/// k-rust revision, which the identity also records.
fn debug_digest(value: &impl std::fmt::Debug) -> String {
    use sha2::{Digest as _, Sha256};
    use std::fmt::Write as _;
    struct Hasher(Sha256);
    impl std::fmt::Write for Hasher {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            self.0.update(text.as_bytes());
            Ok(())
        }
    }
    let mut hasher = Hasher(Sha256::new());
    write!(hasher, "{value:?}").expect("hashing does not fail");
    let digest = hasher.0.finalize();
    let mut text = String::with_capacity(64);
    for byte in digest {
        write!(text, "{byte:02x}").expect("writing to a String does not fail");
    }
    text
}

/// Canonical JSON of a spec part the identity digests.
fn json<T: serde::Serialize + ?Sized>(value: &T) -> String {
    serde_json::to_string(value).expect("spec parts have string keys and no floats")
}

/// The clean-leaf facts a hit of `spec`'s target rests on (ARCHITECTURE 4.3, 5.2), one per
/// check `exec` makes before a leaf is clean ([`crate::exec::UncleanReason`]):
/// - every target: the halt; a decided state, with no `undefined-initial-instances` on its
///   path (D16); ceil-freeness; no implementation-chosen value, contradicted claim, iteration
///   exhaustion or failed rule condition on the leaf; and a run with no stack stop, SMT
///   unknown, allowance refusal or unsupported hook (D21);
/// - a target that matches a pattern on the leaf (a pattern target, or any target with
///   `run-to-completion`, which matches the normal-termination pattern): a decided match;
/// - a target whose hit rests on run-level facts (the coverage modes, D18) or on a set of ends
///   (differential): no run-level fact off every leaf (D16).
fn clean_leaf_facts(spec: &CampaignSpec) -> Vec<String> {
    let mut facts: Vec<&str> = vec![
        "halt-stuck-or-target-terminal",
        "decided-state",
        "no-undefined-initial-instances",
        "ceil-free",
        "no-implementation-chosen-value",
        "no-contradicted-claim",
        "no-iteration-exhaustion",
        "no-rule-condition-failure",
        "no-stack-stops",
        "no-smt-unknowns",
        "no-allowance-refusal",
        "no-unsupported-hook",
    ];
    let natural_end = match &spec.target.kind {
        TargetKind::Pattern(pattern) => {
            facts.push("empty-match-constraints");
            facts.push("decided-match");
            pattern.at == PatternAt::Final && spec.target.run_to_completion
        }
        // The differential conditions depend on the kind of kill; the loop adds them per
        // witness.
        TargetKind::Differential(_) => {
            facts.push("no-run-facts-off-leaves");
            false
        }
        TargetKind::Rule(rule) => {
            if matches!(rule.mode, RuleMode::Covered | RuleMode::ConditionReached) {
                facts.push("no-run-facts-off-leaves");
            }
            spec.target.run_to_completion
        }
        TargetKind::Observer(_) => spec.target.run_to_completion,
    };
    if natural_end {
        if !facts.contains(&"decided-match") {
            facts.push("decided-match");
        }
        facts.push("natural-end");
    }
    facts.into_iter().map(str::to_owned).collect()
}

/// The explicit proposals (ARCHITECTURE 8.1), each a value per hole in hole order: the anchors
/// first when `config.anchors_first` and every hole has one, then each of `config.explicit`,
/// whose omitted holes keep their anchors.
///
/// # Errors
///
/// [`CampaignError::ExplicitAssignment`] for an assignment that names no hole, or that omits a
/// hole without an anchor.
pub(crate) fn explicit_proposals(
    names: &[String],
    anchors: &[Option<Value>],
    config: &ProposerConfig,
) -> Result<Vec<Vec<Value>>, CampaignError> {
    let mut proposals = Vec::with_capacity(config.explicit.len() + 1);
    if config.anchors_first
        && let Some(all) = anchors.iter().cloned().collect::<Option<Vec<Value>>>()
    {
        proposals.push(all);
    }
    for (index, assignment) in config.explicit.iter().enumerate() {
        if let Some(unknown) = assignment.keys().find(|name| !names.contains(name)) {
            return Err(CampaignError::ExplicitAssignment {
                index,
                hole: unknown.clone(),
                message: "no hole has this name".into(),
            });
        }
        let values = names
            .iter()
            .zip(anchors)
            .map(|(name, anchor)| {
                assignment
                    .get(name)
                    .or(anchor.as_ref())
                    .cloned()
                    .ok_or_else(|| CampaignError::ExplicitAssignment {
                        index,
                        hole: name.clone(),
                        message: "the hole has no anchor value and the assignment omits it".into(),
                    })
            })
            .collect::<Result<Vec<Value>, CampaignError>>()?;
        proposals.push(values);
    }
    Ok(proposals)
}
