//! Case execution over the real modules: values printed and checked ([`crate::values`]), the
//! program instantiated and assembled ([`crate::holes`], [`crate::assemble`]), executed and
//! judged ([`crate::exec`], [`crate::target`]). Owner: FZ-06.

use std::{
    collections::BTreeMap,
    fmt::Write as _,
    sync::{Arc, OnceLock},
};

use k_rust::{
    backend::{Backend, CancellationToken, HaltReasonOutput, StopCause},
    k_rust_backend::{
        data_term::{DataHeads, Finding},
        definition::BackendDefinition,
    },
    kore::ast::Pattern as KorePattern,
};

use super::{
    incidental,
    runner::{CaseCrash, CaseRun, CaseRunner, ConfirmFailure, Cut, HitDetail, JudgedComparability},
};
use crate::{
    assemble::{CaseAssembler, ProgramAssembly, build_backend},
    error::{CampaignError, SortRefusal},
    exec::{
        self, Abort, CaseRequestShape, CaseResult, CompiledPattern, Executor, FailureCause,
        NormalEnd, OutcomeClass, PatternCompiler, TargetNeeds, UncleanReason, UnjudgedReason,
    },
    graph::{self, RuleGraph, entry::Entry},
    holes::{self, HoleSite, InstantiatedProgram, PrintedValue, ResolvedHoles, RoundTripCheck},
    report::{
        CrashKind, CrashSide, CrashStage, DefinitionRole, FindingVerdict, HoleValue,
        IncidentalCase, KillKind, NormalEnds, Reaching, RejectionReason, TargetRule, WitnessSide,
    },
    score,
    spec::{BackendRoute, CampaignSpec, CaseOptions, CompiledDefinition, PathMode, ProgramInput},
    target::{self, HitSite, ResolvedTarget, RuleName, TargetKind, differential},
    values::{self, Value, print},
};

/// One definition's half of case execution: its assembly, executor, holes and round-trip check.
pub(crate) struct Side {
    definition: Arc<CompiledDefinition>,
    /// Shared with the run's [`CaseAssembler`] ([`RunAssemblers`]), which borrows it.
    assembly: Arc<ProgramAssembly>,
    executor: Executor,
    /// The normal-termination pattern, compiled once for this definition and prepared on the
    /// executor's backend.
    normal_end: NormalEnd,
    pub(crate) holes: ResolvedHoles,
    round_trip: Arc<RoundTripCheck>,
    shape: CaseRequestShape,
    /// The differential mutant's all-paths shape in the one-path mode, for the cases
    /// [`differential::needs_all_paths`] selects; `None` for every other side.
    all_paths_shape: Option<CaseRequestShape>,
    /// On the `source-execution` route, the internalized definition the backend's session holds
    /// (`Backend::select_definition`), shared, not copied: the campaign's only internalization
    /// of this definition, from which the rule graph's backend and the confirmations' backends
    /// are built by copy ([`GraphCheck::build`], [`DefinitionCache::build`]; phase-1 review N9).
    /// `None` on the `from-definition` route, whose backends internalize inside their sessions.
    internalized: Option<Arc<BackendDefinition>>,
}

#[cfg(test)]
impl Side {
    /// The side's executor.
    pub(crate) fn executor_mut(&mut self) -> &mut Executor {
        &mut self.executor
    }

    /// The internalized definition the side's backend was built from or holds
    /// ([`Self::internalized`]'s field).
    pub(crate) fn internalized(&self) -> Option<&Arc<BackendDefinition>> {
        self.internalized.as_ref()
    }
}

/// What a side may reuse from a [`DefinitionCache`]: the internalized definition its fresh
/// backend copies, the compiled normal-termination pattern, which only needs preparing on that
/// backend, and the hole resolution and round-trip positions, which are functions of the
/// grammar, the program and the hole declarations alone.
#[derive(Clone, Copy, Default)]
struct Seed<'a> {
    internalized: Option<&'a Arc<BackendDefinition>>,
    /// The definition's data heads, when the campaign's own side computed them (they run the
    /// full critical-pair check).
    data_heads: Option<&'a DataHeads>,
    normal_end: Option<&'a NormalEnd>,
    resolved: Option<(&'a ResolvedHoles, &'a Arc<RoundTripCheck>)>,
    /// The program assembly a rebuild reuses: the runner's assemblers borrow it
    /// ([`LiveRunner::recover`]); it is a function of the definition alone.
    assembly: Option<&'a Arc<ProgramAssembly>>,
}

/// The program assembly of `definition`: `reused` when a rebuild gives one, else a new one.
fn assembly_of(
    definition: &CompiledDefinition,
    reused: Option<&Arc<ProgramAssembly>>,
) -> Result<Arc<ProgramAssembly>, CampaignError> {
    match reused {
        Some(assembly) => Ok(Arc::clone(assembly)),
        None => Ok(Arc::new(ProgramAssembly::new(definition)?)),
    }
}

impl Side {
    fn build(
        spec: &CampaignSpec,
        definition: &Arc<CompiledDefinition>,
        role: DefinitionRole,
        seed: Seed<'_>,
    ) -> Result<Self, CampaignError> {
        let assembly = assembly_of(definition, seed.assembly)?;
        let (backend, internalized) = if let Some(internalized) = seed.internalized {
            // A fresh backend over a copy of the cached, immutable internalized definition.
            (
                Backend::from_internalized(
                    BackendDefinition::clone(internalized),
                    spec.options.backend.options(),
                )
                .map_err(CampaignError::from)?,
                Some(Arc::clone(internalized)),
            )
        } else {
            let mut backend = build_backend(definition, spec.options.backend.options())?;
            let internalized = match &definition.route {
                BackendRoute::SourceExecution { .. } => {
                    Some(backend.select_definition(None).map_err(|error| {
                        CampaignError::Definition {
                            message: format!("the main module does not load: {error}"),
                        }
                    })?)
                }
                BackendRoute::FromDefinition => None,
            };
            (backend, internalized)
        };
        let (executor, normal_end) = if let Some(normal_end) = seed.normal_end {
            (
                Executor::with_normal_end(backend, normal_end, &spec.options)?,
                normal_end.clone(),
            )
        } else {
            let compiler = PatternCompiler::new(definition)?;
            let normal_end = compiler.normal_end(assembly.grammar(), &spec.options)?;
            let executor = Executor::with_normal_end(backend, &normal_end, &spec.options)?
                .with_compiler(compiler);
            (executor, normal_end)
        };
        let mut executor = executor
            .with_assume_joined(crate::findings::for_side(role, &spec.options.assume_joined))
            .with_data_heads(seed.data_heads.cloned());
        if let Some((holes, round_trip)) = seed.resolved {
            return Ok(Self {
                definition: Arc::clone(definition),
                assembly,
                executor,
                normal_end,
                holes: holes.clone(),
                round_trip: Arc::clone(round_trip),
                shape: CaseRequestShape::new(&spec.options, &TargetNeeds::default()),
                all_paths_shape: None,
                internalized,
            });
        }
        let mut holes = executor
            .backend_mut()
            .with_solver(None, |backend, _| {
                holes::resolve(&spec.holes, &spec.program, definition, backend)
            })
            .map_err(|error| match (role, error) {
                (
                    DefinitionRole::Mutant,
                    CampaignError::RefusedHoleSort {
                        hole,
                        sort,
                        reason: SortRefusal::Unknown,
                    },
                ) => CampaignError::RefusedHoleSort {
                    hole,
                    sort,
                    reason: SortRefusal::MissingOnSide { side: "mutant" },
                },
                (_, error) => error,
            })?;
        let round_trip = Arc::new(RoundTripCheck::new(
            &assembly,
            definition,
            &spec.program,
            &holes,
        )?);
        // The values this side's grammar can hold at each span hole bound what is generated
        // (FZ-INTGEN, `holes::narrow`).
        holes.narrow(holes::probe_negatives(
            &holes,
            holes.text.as_ref(),
            &round_trip,
            &assembly,
            definition,
            &spec.program,
            role,
        )?)?;
        Ok(Self {
            definition: Arc::clone(definition),
            assembly,
            executor,
            normal_end,
            holes,
            round_trip,
            shape: CaseRequestShape::new(&spec.options, &TargetNeeds::default()),
            all_paths_shape: None,
            internalized,
        })
    }

    /// In the one-path mode, the differential mutant's all-paths run of `initial` when its
    /// one-path result `one_path` could kill only by a removed end
    /// ([`differential::needs_all_paths`]; ARCHITECTURE 4.3 as amended by FZ-DIFFEND); `None`
    /// otherwise, and for every other side. The case counts its work, and its result then
    /// stands for the mutant everywhere.
    fn rerun_on_all_paths(
        &mut self,
        initial: &KorePattern,
        baseline: &CaseResult,
        one_path: &CaseResult,
        run_to_completion: bool,
        cancel: Option<&CancellationToken>,
    ) -> Result<Option<CaseResult>, Abort> {
        match &self.all_paths_shape {
            Some(shape)
                if !refused(baseline)
                    && !refused(one_path)
                    && differential::needs_all_paths(baseline, one_path, run_to_completion) =>
            {
                Ok(Some(self.executor.run(initial, shape, &[], cancel)?))
            }
            Some(_) | None => Ok(None),
        }
    }

    /// Print, instantiate, assemble with `assembler` and round-trip-check `values`; the
    /// rejection reason when a step refuses them. `assembler` must be one of this side's
    /// assembly and definition ([`Self::assembler`]).
    fn prepare(
        &self,
        assembler: &mut CaseAssembler<'_>,
        program: &ProgramInput,
        values: &[Value],
    ) -> Result<Prepared, RejectionReason> {
        self.prepare_checked(assembler, program, values, true)
    }

    /// An assembler of this side's configurations, which keeps its program parser, macro
    /// expander and sort injectors across the cases it assembles.
    fn assembler(&self) -> CaseAssembler<'_> {
        self.assembly.assembler(&self.definition)
    }

    /// [`Self::prepare`], with the constraint check optional: an anchor may lie outside its
    /// hole's constraints, which narrow what is generated, and still identify the grammar.
    fn prepare_checked(
        &self,
        assembler: &mut CaseAssembler<'_>,
        program: &ProgramInput,
        values: &[Value],
        check_constraints: bool,
    ) -> Result<Prepared, RejectionReason> {
        prepare_values(
            &self.holes,
            &self.round_trip,
            assembler,
            program,
            values,
            check_constraints,
            &[],
        )
    }
}

/// Print, instantiate, assemble with `assembler` and round-trip-check `values` for `holes`; the
/// rejection reason when a step refuses them. The constraint check is optional (see
/// [`Side::prepare_checked`]). `replacements`, when not empty, holds one entry per hole: a hole
/// with `Some(kore)` has `kore` in the configuration instead of its value's KORE, placed after
/// the round-trip check at the hole's position (a template hole: substituted for its variable).
/// [`Prepared::printed`] keeps the values' own KORE.
fn prepare_values(
    holes: &ResolvedHoles,
    round_trip: &RoundTripCheck,
    assembler: &mut CaseAssembler<'_>,
    program: &ProgramInput,
    values: &[Value],
    check_constraints: bool,
    replacements: &[Option<KorePattern>],
) -> Result<Prepared, RejectionReason> {
    let mut printed = Vec::with_capacity(values.len());
    for (hole, value) in holes.holes.iter().zip(values) {
        if check_constraints {
            values::check_constraints(value, &hole.sort, &hole.decl.constraints)
                .map_err(|_| RejectionReason::Constraint)?;
        }
        // A template hole substitutes the KORE alone, so its K text is only the witness's,
        // and a value that has none is not refused for it.
        let k_text = print::print_k_text(value, &hole.sort);
        let k_text = if matches!(hole.site, HoleSite::KoreVariable(_)) {
            k_text.ok()
        } else {
            Some(k_text.map_err(|_| RejectionReason::Print)?)
        };
        let (kore, sort) =
            print::to_kore_with_sort(value, &hole.sort).map_err(|_| RejectionReason::Print)?;
        printed.push(PrintedValue { k_text, kore, sort });
    }
    let replaced = |index: usize| replacements.get(index).and_then(Option::as_ref);
    let substituted: Vec<PrintedValue> = printed
        .iter()
        .enumerate()
        .map(
            |(index, value)| match (&holes.holes[index].site, replaced(index)) {
                (HoleSite::KoreVariable(_), Some(kore)) => PrintedValue {
                    kore: kore.clone(),
                    ..value.clone()
                },
                _ => value.clone(),
            },
        )
        .collect();
    let instantiated = holes::instantiate(program, holes, &substituted);
    let mut configuration = assembler
        .assemble(&instantiated)
        .map_err(|_| RejectionReason::Assembly)?;
    round_trip
        .check(&configuration, &printed)
        .map_err(|_| RejectionReason::RoundTrip)?;
    for (index, position) in round_trip.positions().iter().enumerate() {
        if let (Some(kore), Some(path)) = (replaced(index), position)
            && !replace_subterm(&mut configuration, path, kore.clone())
        {
            return Err(RejectionReason::RoundTrip);
        }
    }
    Ok(Prepared {
        printed,
        instantiated,
        assembled: configuration,
    })
}

/// `holes::replace_at`, in the builds that have it (the solve proposer's, `z3`); no build
/// without it passes a replacement.
fn replace_subterm(pattern: &mut KorePattern, path: &[usize], kore: KorePattern) -> bool {
    #[cfg(feature = "z3")]
    {
        holes::replace_at(pattern, path, kore)
    }
    #[cfg(not(feature = "z3"))]
    {
        let _ = (pattern, path, kore);
        false
    }
}

/// What the solve proposer needs to build the baseline's configurations itself
/// (ARCHITECTURE 8.6): the baseline's definition, program assembly, hole resolution and
/// round-trip positions, and its internalized definition, from which the proposer builds a
/// backend of its own. Every part is shared, not copied, and immutable.
#[cfg(feature = "z3")]
pub(crate) struct ConfigurationBuilder {
    definition: Arc<CompiledDefinition>,
    assembly: Arc<ProgramAssembly>,
    holes: ResolvedHoles,
    round_trip: Arc<RoundTripCheck>,
    program: ProgramInput,
    internalized: Option<Arc<BackendDefinition>>,
}

#[cfg(feature = "z3")]
impl ConfigurationBuilder {
    /// The baseline's resolved holes.
    pub(crate) fn holes(&self) -> &ResolvedHoles {
        &self.holes
    }

    /// The baseline's compiled definition.
    pub(crate) fn definition(&self) -> &Arc<CompiledDefinition> {
        &self.definition
    }

    /// The baseline's internalized definition on the `source-execution` route
    /// ([`LiveCases::baseline_internalized`]).
    pub(crate) fn internalized(&self) -> Option<&Arc<BackendDefinition>> {
        self.internalized.as_ref()
    }

    /// The configuration of `values` (constraints checked, assembled, round-trip-checked) with
    /// `replacements` in place of the values of the holes that have one ([`prepare_values`]).
    pub(crate) fn configuration(
        &self,
        values: &[Value],
        replacements: &[Option<KorePattern>],
    ) -> Result<KorePattern, RejectionReason> {
        let mut assembler = self.assembly.assembler(&self.definition);
        prepare_values(
            &self.holes,
            &self.round_trip,
            &mut assembler,
            &self.program,
            values,
            true,
            replacements,
        )
        .map(|prepared| prepared.assembled)
    }
}

/// A case's values after printing and assembly.
struct Prepared {
    printed: Vec<PrintedValue>,
    instantiated: InstantiatedProgram,
    assembled: KorePattern,
}

/// How cases are judged.
enum Judge {
    /// Against a resolved rule or pattern target.
    Target(ResolvedTarget),
    /// As a baseline/mutant pair (ARCHITECTURE 4.3).
    Differential(Box<Side>),
}

/// The rule names of a campaign ([`LiveCases::rule_index`]).
pub(crate) struct RuleIndex {
    /// Every catalog id's names.
    pub(crate) names: Arc<BTreeMap<String, RuleName>>,
    /// The rule a rule target resolved to.
    pub(crate) target: Option<TargetRule>,
}

/// What a campaign states about its definitions' full critical-pair checks
/// ([`LiveCases::definition_findings`]).
#[derive(Debug, Default)]
pub(crate) struct DefinitionFindings {
    /// One warning per definition without data, and one stating the assumed pairs.
    pub(crate) warnings: Vec<String>,
    /// Every finding of every definition read, for the report.
    pub(crate) findings: Vec<crate::report::DefinitionFinding>,
    /// The definitions whose findings are not all assumed joined: they have no data.
    pub(crate) without_data: Vec<DefinitionRole>,
}

/// The campaign's case execution: one baseline [`Side`] and the judge.
pub(crate) struct LiveCases {
    spec: Arc<CampaignSpec>,
    pub(crate) baseline: Side,
    judge: Judge,
    /// The classes whose incidental finding the loop has kept ([`CaseRunner::incidental_kept`]).
    incidental_kept: Vec<OutcomeClass>,
}

impl LiveCases {
    /// Build every backend, assembly, hole resolution and target resolution the spec needs,
    /// from nothing: confirmation builds one per candidate (ARCHITECTURE 7).
    ///
    /// # Errors
    ///
    /// The [`CampaignError`] of the first module that refuses the spec.
    pub(crate) fn build(spec: Arc<CampaignSpec>) -> Result<Self, CampaignError> {
        Self::build_with(spec, None)
    }

    /// [`Self::build`], with each side's backend built from `cache`'s internalized definition
    /// when it holds one.
    pub(crate) fn build_with(
        spec: Arc<CampaignSpec>,
        cache: Option<&DefinitionCache>,
    ) -> Result<Self, CampaignError> {
        Self::build_seeded(spec, cache, &Sessions::default())
    }

    /// [`Self::build_with`], each side's backend built from `sessions`' internalized definition
    /// where it holds one and the cache does not (the `from-definition` route's rebuild after a
    /// crash, [`LiveRunner::recover`]).
    fn build_seeded(
        spec: Arc<CampaignSpec>,
        cache: Option<&DefinitionCache>,
        sessions: &Sessions,
    ) -> Result<Self, CampaignError> {
        fn seeded<'a>(
            seed: Seed<'a>,
            session: Option<&'a Arc<BackendDefinition>>,
            assembly: Option<&'a Arc<ProgramAssembly>>,
        ) -> Seed<'a> {
            Seed {
                internalized: seed.internalized.or(session),
                assembly,
                ..seed
            }
        }
        let mut baseline = Side::build(
            &spec,
            &spec.definitions.baseline,
            DefinitionRole::Baseline,
            seeded(
                cache.map(|cache| cache.baseline.seed()).unwrap_or_default(),
                sessions.baseline.as_ref(),
                sessions.baseline_assembly.as_ref(),
            ),
        )?;
        let judge = if let TargetKind::Differential(_) = spec.target.kind {
            let mutant_definition = spec
                .definitions
                .mutant
                .as_ref()
                .ok_or(CampaignError::DefinitionsMismatch)?;
            let plan = differential::plan(&spec.options);
            let mut mutant = Side::build(
                &spec,
                mutant_definition,
                DefinitionRole::Mutant,
                seeded(
                    cache
                        .and_then(|cache| cache.mutant.as_ref())
                        .map(SideCache::seed)
                        .unwrap_or_default(),
                    sessions.mutant.as_ref(),
                    sessions.mutant_assembly.as_ref(),
                ),
            )?;
            // A value the mutant's grammar cannot hold at a hole makes every case with it
            // `rejected`, so the mutant's narrowings bound the baseline's generation too.
            baseline.holes.narrow(holes::probe_negatives(
                &baseline.holes,
                mutant.holes.text.as_ref(),
                &mutant.round_trip,
                &mutant.assembly,
                &mutant.definition,
                &spec.program,
                DefinitionRole::Mutant,
            )?)?;
            baseline.shape = CaseRequestShape::new(&spec.options, &plan.baseline);
            mutant.shape = CaseRequestShape::new(&spec.options, &plan.mutant);
            mutant.all_paths_shape = plan
                .mutant_all_paths
                .as_ref()
                .map(|needs| CaseRequestShape::new(&spec.options, needs));
            Judge::Differential(Box::new(mutant))
        } else {
            let target = ResolvedTarget::resolve_with(
                &spec.target,
                &mut baseline.executor,
                &spec.definitions.baseline,
                &baseline.assembly,
                cache.map(|cache| cache.target_patterns.as_slice()),
            )?;
            baseline.shape =
                CaseRequestShape::new(&spec.options, &target.needs(spec.options.paths));
            Judge::Target(target)
        };
        Ok(Self {
            spec,
            baseline,
            judge,
            incidental_kept: Vec::new(),
        })
    }

    /// Whether a run or its judgement panicked on one of the sides' executors
    /// (`Executor::poisoned`).
    pub(crate) fn poisoned(&self) -> bool {
        self.baseline.executor.poisoned()
            || matches!(&self.judge, Judge::Differential(mutant) if mutant.executor.poisoned())
    }

    /// The internalized definition each side's backend session holds
    /// (`Backend::select_definition`), on the `from-definition` route, whose cache holds none:
    /// the object the campaign's backend executes, which a rebuild copies instead of
    /// internalizing the KORE again ([`LiveRunner::recover`]). Reading it reads only the
    /// session's shared `Arc`. `None` for a side on the `source-execution` route, and for one
    /// whose session does not answer.
    fn sessions(&mut self) -> Sessions {
        let of = |side: &mut Side| match side.definition.route {
            BackendRoute::FromDefinition => {
                side.executor.backend_mut().select_definition(None).ok()
            }
            BackendRoute::SourceExecution { .. } => None,
        };
        let baseline = of(&mut self.baseline);
        let mutant = match &mut self.judge {
            Judge::Differential(mutant) => of(mutant),
            Judge::Target(_) => None,
        };
        Sessions {
            baseline,
            mutant,
            ..Sessions::default()
        }
    }

    /// Each side's initial configuration for `values` (the baseline, then the mutant of a
    /// differential campaign), without the constraint check; `Err` for a side that refuses them.
    pub(crate) fn initial_configurations(
        &self,
        values: &[Value],
    ) -> Vec<Result<KorePattern, RejectionReason>> {
        let mut sides = vec![&self.baseline];
        if let Judge::Differential(mutant) = &self.judge {
            sides.push(mutant);
        }
        sides
            .into_iter()
            .map(|side| {
                side.prepare_checked(&mut side.assembler(), &self.spec.program, values, false)
                    .map(|prepared| prepared.assembled)
            })
            .collect()
    }

    /// What the campaign states about each definition's full critical-pair check
    /// (`k_rust_backend::data_term`): computed only when the campaign reads data ends (a
    /// differential target, or `requires_data_end`), and empty otherwise. A definition whose
    /// check reports findings that are not assumed joined has no data, so the campaign is not
    /// comparable (ARCHITECTURE 4.3); each such definition gets one warning, and every finding
    /// a report entry.
    ///
    /// # Errors
    ///
    /// [`CampaignError::InvalidOptions`] when `CaseOptions::assume_joined` names a finding while
    /// the campaign reads no data end, or a name matches no finding of either definition, a
    /// decided finding, more than one finding of one definition, or different findings on the
    /// two.
    pub(crate) fn definition_findings(&mut self) -> Result<DefinitionFindings, CampaignError> {
        let assume_joined = self.spec.options.assume_joined.clone();
        let mut sides = vec![(DefinitionRole::Baseline, &mut self.baseline)];
        match &mut self.judge {
            Judge::Differential(mutant) => sides.push((DefinitionRole::Mutant, mutant)),
            Judge::Target(_) if self.spec.target.requires_data_end() => {}
            Judge::Target(_) => {
                if let Some(name) = assume_joined.first() {
                    return Err(CampaignError::InvalidOptions {
                        message: format!(
                            "assume-joined names `{name}`, but this campaign reads no data end: \
                             only a differential target, or a rule or pattern target with \
                             run-to-completion and data-end, judges ends by the definitions' \
                             critical-pair checks"
                        ),
                    });
                }
                return Ok(DefinitionFindings::default());
            }
        }
        let mut stated = DefinitionFindings::default();
        // The finding each name matches on each definition, by its equations' identities.
        let mut matched: Vec<Vec<(DefinitionRole, Vec<String>, String)>> =
            vec![Vec::new(); assume_joined.len()];
        for (role, side) in sides {
            let side_name = match role {
                DefinitionRole::Baseline => "baseline",
                DefinitionRole::Mutant => "mutant",
            };
            let text = side.holes.text.clone();
            let heads = match side.executor.data_heads() {
                Ok(heads) => heads,
                Err(error) => {
                    stated.warnings.push(format!(
                        "definition-not-confluent ({side_name}): the main module does not load: \
                         {error}"
                    ));
                    stated.without_data.push(role);
                    continue;
                }
            };
            match_assumed(&assume_joined, role, heads, &mut matched)?;
            if !heads.confluent() {
                stated.without_data.push(role);
                stated
                    .warnings
                    .push(not_confluent_warning(side_name, heads));
            }
            let entries = crate::findings::report(role, heads, text.as_ref());
            // A pair the campaign assumes joined although the check shows it does not join: the
            // verdicts then hold for a reading its evaluation does not have.
            for entry in entries
                .iter()
                .filter(|entry| entry.assumed && entry.verdict == FindingVerdict::Genuine)
            {
                stated.warnings.push(format!(
                    "assume-joined ({side_name}): `{}` is genuine: {}; the verdicts hold only for \
                     the definition read as if this pair joined, not \
                     for the definition as written",
                    entry.name.as_deref().unwrap_or_default(),
                    entry.reason
                ));
            }
            stated.findings.extend(entries);
        }
        if let Some(warning) = check_assumed(&assume_joined, &matched)? {
            stated.warnings.push(warning);
        }
        Ok(stated)
    }

    /// The baseline's internalized definition on the `source-execution` route, the campaign's
    /// only internalization of it ([`Side::internalized`]); `None` on the `from-definition`
    /// route.
    pub(crate) fn baseline_internalized(&self) -> Option<&Arc<BackendDefinition>> {
        self.baseline.internalized.as_ref()
    }

    /// The names of every id in the rule catalog of the definition whose coverage a case
    /// records (the mutant's in a differential campaign, [`run_of`], the baseline's otherwise),
    /// and the rule a rule target resolved to with its names.
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when the backend gives no catalog.
    pub(crate) fn rule_index(&mut self) -> Result<RuleIndex, CampaignError> {
        let target = self.target_rule_id().map(str::to_owned);
        let side = match &mut self.judge {
            Judge::Differential(mutant) => mutant,
            Judge::Target(_) => &mut self.baseline,
        };
        let catalog = side
            .executor
            .backend_mut()
            .rule_catalog(None)
            .map_err(|error| CampaignError::Definition {
                message: format!("the rule catalog is not available: {error}"),
            })?;
        let names = target::rule_names(&catalog);
        let target = target.and_then(|id| {
            let name = names.get(&id)?.clone();
            Some(TargetRule { id, name })
        });
        Ok(RuleIndex {
            names: Arc::new(names),
            target,
        })
    }

    /// The catalog id of a rule target's rule, as the target resolved it; `None` for every
    /// other target kind.
    pub(crate) fn target_rule_id(&self) -> Option<&str> {
        match &self.judge {
            Judge::Target(target) => target.rule_id(),
            Judge::Differential(_) => None,
        }
    }

    /// Ask every case of the baseline to record the condition entries of `rules`
    /// (`collectConditions`), which the climb's score reads (`crate::score`). Asking changes no
    /// other field of a result, so the class, the coverage and the witness are unchanged.
    pub(crate) fn request_conditions(&mut self, rules: Vec<String>) {
        self.baseline.shape = self.baseline.shape.with_conditions(rules);
    }

    /// Ask every case of every side to count how many times its run applied each rule
    /// (`collectCounts`), which the corpus's keep rule reads (`crate::proposers::corpus`).
    /// Asking changes no other field of a result, so the class, the coverage sets and the
    /// witness are unchanged.
    pub(crate) fn request_counts(&mut self) {
        self.baseline.shape = self.baseline.shape.with_counts();
        if let Judge::Differential(mutant) = &mut self.judge {
            mutant.shape = mutant.shape.with_counts();
            mutant.all_paths_shape = mutant
                .all_paths_shape
                .as_ref()
                .map(CaseRequestShape::with_counts);
        }
    }

    /// What the solve proposer builds the baseline's configurations from
    /// ([`ConfigurationBuilder`]).
    #[cfg(feature = "z3")]
    pub(crate) fn configuration_builder(&self) -> ConfigurationBuilder {
        let side = &self.baseline;
        ConfigurationBuilder {
            definition: Arc::clone(&side.definition),
            assembly: Arc::clone(&side.assembly),
            holes: side.holes.clone(),
            round_trip: Arc::clone(&side.round_trip),
            program: self.spec.program.clone(),
            internalized: side.internalized.clone(),
        }
    }

    /// Which normal end each side's classes rest on (ARCHITECTURE 5.2).
    pub(crate) fn normal_ends(&self) -> NormalEnds {
        NormalEnds {
            baseline: self.baseline.normal_end.kind(),
            mutant: match &self.judge {
                Judge::Differential(mutant) => Some(mutant.normal_end.kind()),
                Judge::Target(_) => None,
            },
        }
    }

    /// What a run's [`RunAssemblers`] borrow: each side's program assembly and definition.
    pub(crate) fn assembly_parts(&self) -> AssemblyParts {
        let part = |side: &Side| (Arc::clone(&side.assembly), Arc::clone(&side.definition));
        AssemblyParts {
            baseline: part(&self.baseline),
            mutant: match &self.judge {
                Judge::Differential(mutant) => Some(part(mutant)),
                Judge::Target(_) => None,
            },
        }
    }

    fn hole_values(&self, values: &[Value], printed: &[PrintedValue]) -> Vec<HoleValue> {
        self.baseline
            .holes
            .holes
            .iter()
            .zip(values.iter().zip(printed))
            .map(|(hole, (value, printed))| HoleValue {
                name: hole.decl.name.clone(),
                location: hole.decl.location.clone(),
                k_text: printed.k_text.clone(),
                kore: printed.kore.to_string(),
                value: value.clone(),
            })
            .collect()
    }

    /// The `krun` command line equivalent to a run of `instantiated` on `definition`, whose
    /// compiled directory is left as `directory` (`<definition-dir>`, `<mutant-dir>`), under
    /// strategy `paths` and with `terminal_rules` as krun's terminal rules; `None` when no `krun`
    /// run is: the `from-definition` route, a KORE template, or a program without `$PGM` (krun
    /// would read `$PGM` from its standard input).
    fn krun_command(
        definition: &CompiledDefinition,
        directory: &str,
        options: &CaseOptions,
        paths: PathMode,
        terminal_rules: &[String],
        instantiated: &InstantiatedProgram,
    ) -> Option<String> {
        Self::krun_line(
            definition,
            directory,
            options,
            paths,
            terminal_rules,
            instantiated,
            None,
        )
    }

    /// [`Self::krun_command`], or with `search_pattern` the `krun` search that reproduces a
    /// pattern target `at: any-state`: every reachable configuration matched against the
    /// pattern (`--search-all --pattern`, which explores every path), in place of `--strategy`
    /// (FZ-STATESET-MATCH, ARCHITECTURE 9.3).
    fn krun_line(
        definition: &CompiledDefinition,
        directory: &str,
        options: &CaseOptions,
        paths: PathMode,
        terminal_rules: &[String],
        instantiated: &InstantiatedProgram,
        search_pattern: Option<&str>,
    ) -> Option<String> {
        if definition.route == BackendRoute::FromDefinition {
            return None;
        }
        let InstantiatedProgram::Source {
            program: Some(program),
            config_vars,
        } = instantiated
        else {
            return None;
        };
        let mut line = format!(
            "krust krun --definition {directory} -m {} --syntax-module {}",
            quote(&definition.main_module),
            quote(&definition.syntax_module)
        );
        write!(line, " -s {}", quote(&program.start_sort)).expect("writing to a String");
        if let Some(pattern) = search_pattern {
            write!(line, " --io off --search-all --pattern {}", quote(pattern))
                .expect("writing to a String");
        } else {
            line.push_str(" --io off --strategy ");
            line.push_str(match paths {
                PathMode::OnePath => "any",
                PathMode::AllPaths => "all",
            });
        }
        if let Some(depth) = options.max_depth {
            write!(line, " --depth {depth}").expect("writing to a String");
        }
        // A `fired` target under one path stops at its rule (FZ-05, D16); so must krun.
        for rule in terminal_rules {
            write!(line, " --terminal-rule {}", quote(rule)).expect("writing to a String");
        }
        write!(
            line,
            " --max-simplification-iterations {} --smt-timeout {} --smt-retry-limit {}",
            options.max_simplification_iterations,
            options.backend.smt_timeout_ms,
            options.backend.smt_retry_limit
        )
        .expect("writing to a String");
        for (name, value) in config_vars {
            write!(line, " -c {}", quote(&format!("{name}={value}"))).expect("writing to a String");
        }
        // `--io off` buffers standard input into `$STDIN`; the campaign binds it empty.
        write!(line, " -e {} < /dev/null", quote(&program.text)).expect("writing to a String");
        // The search explores every reachable configuration; with no depth bound it ends only
        // when they are finitely many, so the line says so, and names the work bound the run
        // used, which krun cannot take.
        let unbounded_search = search_pattern.is_some() && options.max_depth.is_none();
        match (options.effective_max_work(), unbounded_search) {
            (Some(work), false) => write!(
                line,
                "  # the campaign also bounds max-work {work}, which krun cannot"
            ),
            (Some(work), true) => write!(
                line,
                "  # the campaign bounded max-work {work}, which krun cannot, and no depth: \
                 this search may not terminate"
            ),
            (None, true) => write!(
                line,
                "  # the campaign bounded no depth: this search may not terminate"
            ),
            (None, false) => Ok(()),
        }
        .expect("writing to a String");
        Some(line)
    }

    /// What re-enters a differential case as a test: the `krun` lines of the baseline on all
    /// paths, as it runs, and of the mutant in `paths`, the mode its judged result ran in, and
    /// the instantiated program text.
    fn reentry(
        spec: &CampaignSpec,
        baseline: &Prepared,
        mutant: &Prepared,
        paths: PathMode,
    ) -> (Option<String>, Option<String>, Option<String>) {
        let line = |definition, directory, paths, instantiated| {
            Self::krun_command(
                definition,
                directory,
                &spec.options,
                paths,
                &[],
                instantiated,
            )
        };
        (
            line(
                &spec.definitions.baseline,
                "<definition-dir>",
                PathMode::AllPaths,
                &baseline.instantiated,
            ),
            spec.definitions.mutant.as_ref().and_then(|definition| {
                line(definition, "<mutant-dir>", paths, &mutant.instantiated)
            }),
            program_text(&baseline.instantiated),
        )
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one case of a rule, pattern or observer target: its run, judgement and crash"
    )]
    fn run_target(
        &mut self,
        assemblers: &mut RunAssemblers<'_>,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, Abort> {
        let prepared =
            match self
                .baseline
                .prepare(&mut assemblers.baseline, &self.spec.program, values)
            {
                Ok(prepared) => prepared,
                Err(reason) => return Ok(CaseRun::rejected(reason, 0)),
            };
        let Judge::Target(target) = &self.judge else {
            unreachable!("run_target is called for rule and pattern targets")
        };
        let side = &mut self.baseline;
        // `run_and_judge` is `run` then `judge` for rule and pattern targets; an observer target
        // also walks its observer over the observed run (FZ-10). The program's run of every path
        // that judged a hit's comparability under `comparable-end`, when the case made one,
        // counts in the case's work, load records and determinism (`target::comparable`).
        let target::JudgedRun {
            result,
            judgement: judged,
            hit_step,
            state_match,
            progress,
            comparable,
            every_path,
        } = target.run_and_judge(&mut side.executor, &prepared.assembled, &side.shape, cancel)?;
        let sides: Vec<_> = std::iter::once(&result).chain(&every_path).collect();
        let mut run = run_of(&result, &sides);
        // The class of the case's leaves, which decides its incidental finding: the class, or
        // the one `fired-off-trace` replaced (`Judgement::demoted_from`).
        let mut leaves_class = None;
        run.pattern_body_matches = target.pattern_body_matches(&result);
        run.progress = progress;
        run.cut = cut_of(&result);
        match judged {
            Ok(judgement) => {
                run.class = judgement.class;
                leaves_class = judgement.demoted_from;
                run.unjudged = data_reason(judgement.reason, &self.baseline, None);
                run.blocked = judgement.blocked;
                if judgement.class == OutcomeClass::Hit {
                    // A leaf hit names its leaf; a hit of the whole run (D16) names none, and
                    // rests on every leaf's configuration; an any-state hit names the
                    // configuration it reached, at its depth, which need not be a leaf's.
                    let reached = match judgement.hit_site {
                        // Its depth is `hit_step`; it names no leaf, so no leaf's steps.
                        Some(HitSite::StateMatch { depth }) => state_match
                            .as_ref()
                            .filter(|hit| hit.depth == depth)
                            .map(|hit| (None, None, hit.configuration.to_string())),
                        Some(HitSite::Leaf(index)) => result
                            .leaves
                            .get(index)
                            .map(|leaf| (Some(index), Some(leaf.depth), leaf.state.to_string())),
                        Some(HitSite::Run) => Some((
                            None,
                            None,
                            result
                                .leaves
                                .iter()
                                .map(|leaf| leaf.state.to_string())
                                .collect::<Vec<_>>()
                                .join("\n"),
                        )),
                        None => None,
                    };
                    if let Some((leaf, steps, reaching_state)) = reached {
                        run.hit = Some(HitDetail {
                            holes: self.hole_values(values, &prepared.printed),
                            sides: vec![side_of(DefinitionRole::Baseline, &prepared, &result)],
                            reaching: Reaching {
                                role: DefinitionRole::Baseline,
                                leaf: leaf.map(index_u64),
                                // An observer hit's step on the hit leaf's path (ARCHITECTURE
                                // 9.2); the leaf runs on to its end, at depth `steps`. An
                                // any-state hit's depth, with its configuration.
                                step: hit_step,
                                configuration: state_match
                                    .as_ref()
                                    .map(|hit| hit.configuration.to_string()),
                            },
                            kill: None,
                            steps,
                            reaching_state,
                            krun_command: Self::krun_line(
                                &self.spec.definitions.baseline,
                                "<definition-dir>",
                                &self.spec.options,
                                self.spec.options.paths,
                                &target.needs(self.spec.options.paths).terminal_rules,
                                &prepared.instantiated,
                                state_match
                                    .as_ref()
                                    .and_then(|_| any_state_pattern(&self.spec.target)),
                            ),
                            mutant_krun_command: None,
                            program: program_text(&prepared.instantiated),
                            comparable: comparable.clone(),
                            config_vars: binding_texts(&prepared.instantiated),
                        });
                    } else {
                        run.class = OutcomeClass::Unsupported;
                        run.unjudged = Some(UnjudgedReason::EngineDefect);
                        run.defects
                            .push("a hit names no leaf of the result".to_owned());
                    }
                }
            }
            Err(defect) => {
                run.class = OutcomeClass::Unsupported;
                run.unjudged = Some(UnjudgedReason::EngineDefect);
                run.defects.push(defect.description);
            }
        }
        // The case's one run is the finding's: its determinism is the case's. A case that
        // `fired-off-trace` made `unsupported` keeps the finding of its leaves' class: that
        // reason says the target cannot be judged, not that the leaves are not real.
        let class = leaves_class.unwrap_or(run.class);
        if self.wants_incidental(class, !run.outside_determinism) {
            let paths = self.spec.options.paths;
            let terminal_rules = target.needs(paths).terminal_rules;
            run.incidental =
                self.incidental_of(class, values, &prepared, &result, paths, &terminal_rules);
        }
        run.warnings.extend(partial_warnings(&result, run.unjudged));
        if run.class == OutcomeClass::Rejected {
            run.rejection = Some(RejectionReason::BackendRefused);
        }
        // A crash of the case's run, or of the program's run of every path that judged its
        // comparability, is the case's (FZ-CRASH).
        let paths = self.spec.options.paths;
        let terminal_rules = target.needs(paths).terminal_rules;
        let definition = &self.spec.definitions.baseline;
        run.crash = Self::crash_of(
            &self.spec,
            &result,
            CrashSide::Baseline,
            definition,
            "<definition-dir>",
            paths,
            &terminal_rules,
            &prepared,
            cancel,
        )
        .or_else(|| {
            every_path.as_ref().and_then(|every_path| {
                Self::crash_of(
                    &self.spec,
                    every_path,
                    CrashSide::Baseline,
                    definition,
                    "<definition-dir>",
                    PathMode::AllPaths,
                    &[],
                    &prepared,
                    cancel,
                )
            })
        });
        Ok(run)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one differential case: both sides' runs, their judgement and the witness detail"
    )]
    fn run_differential(
        &mut self,
        assemblers: &mut RunAssemblers<'_>,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, Abort> {
        let Judge::Differential(mutant) = &mut self.judge else {
            unreachable!("run_differential is called for differential targets")
        };
        let mutant_assembler = assemblers
            .mutant
            .as_mut()
            .expect("a differential run has a mutant assembler (LiveCases::assembly_parts)");
        let baseline_case =
            match self
                .baseline
                .prepare(&mut assemblers.baseline, &self.spec.program, values)
            {
                Ok(prepared) => prepared,
                Err(reason) => return Ok(CaseRun::rejected(reason, 0)),
            };
        let mutant_case = match mutant.prepare(mutant_assembler, &self.spec.program, values) {
            Ok(prepared) => prepared,
            Err(reason) => return Ok(CaseRun::rejected(reason, 0)),
        };
        let side = &mut self.baseline;
        let run_to_completion = self.spec.target.run_to_completion;
        let (baseline, one_path, rerun) = run_sides(
            side,
            mutant,
            &baseline_case.assembled,
            &mutant_case.assembled,
            run_to_completion,
            cancel,
        )?;
        let (mutated, paths) = match &rerun {
            Some(all_paths) => (all_paths, PathMode::AllPaths),
            None => (&one_path, self.spec.options.paths),
        };
        let sides: Vec<_> = [&baseline, &one_path].into_iter().chain(&rerun).collect();
        let mut run = run_of(mutated, &sides);
        run.baseline_ended_within = ended_within(&baseline);
        // A crash of the baseline's run, else of the mutant's (FZ-CRASH), also of a case that
        // either side's refusal makes `rejected`.
        let spec = &*self.spec;
        let mutant_definition = spec
            .definitions
            .mutant
            .as_deref()
            .unwrap_or(&spec.definitions.baseline);
        run.crash = Self::crash_of(
            spec,
            &baseline,
            CrashSide::Baseline,
            &spec.definitions.baseline,
            "<definition-dir>",
            PathMode::AllPaths,
            &[],
            &baseline_case,
            cancel,
        )
        .or_else(|| {
            Self::crash_of(
                spec,
                &one_path,
                CrashSide::Mutant,
                mutant_definition,
                "<mutant-dir>",
                spec.options.paths,
                &[],
                &mutant_case,
                cancel,
            )
        })
        .or_else(|| {
            rerun.as_ref().and_then(|rerun| {
                Self::crash_of(
                    spec,
                    rerun,
                    CrashSide::Mutant,
                    mutant_definition,
                    "<mutant-dir>",
                    PathMode::AllPaths,
                    &[],
                    &mutant_case,
                    cancel,
                )
            })
        });
        // A value either side's backend refuses makes the case `rejected` (ARCHITECTURE 4.3,
        // 5.3), before the pair is judged: a refused baseline is not an incomplete one.
        if refused(&baseline) || refused(mutated) {
            run.class = OutcomeClass::Rejected;
            run.rejection = Some(RejectionReason::BackendRefused);
            return Ok(run);
        }
        // The judged result is the re-run's when there is one (with its all-paths mode): the
        // class, the reason, the cut and the partial-function warnings all read it.
        match differential::judge_pair_explained(&baseline, mutated, paths, run_to_completion) {
            Ok((judgement, reason)) => {
                run.class = judgement.class;
                run.unjudged = data_reason(reason, &self.baseline, Some(mutant));
                let judged = match judgement.class {
                    OutcomeClass::BaselineIncomplete => &baseline,
                    _ => mutated,
                };
                run.warnings.extend(partial_warnings(judged, reason));
                run.cut = cut_of(judged);
                if judgement.class == OutcomeClass::Hit {
                    // An added end: the killing mutant leaf. A removed end (all-paths mode, or the
                    // one-path mode's all-paths re-run): the
                    // baseline end the mutant cannot reach. Both sides list every leaf.
                    let witness = judgement.witness().and_then(|(kind, index)| {
                        let (role, side) = match kind {
                            KillKind::AddedEnd => (DefinitionRole::Mutant, mutated),
                            KillKind::RemovedEnd => (DefinitionRole::Baseline, &baseline),
                        };
                        side.leaves.get(index).map(|leaf| (kind, role, index, leaf))
                    });
                    if let Some((kind, role, index, leaf)) = witness {
                        let (krun_command, mutant_krun_command, program) =
                            Self::reentry(&self.spec, &baseline_case, &mutant_case, paths);
                        run.hit = Some(HitDetail {
                            holes: self.hole_values(values, &baseline_case.printed),
                            sides: vec![
                                side_of(DefinitionRole::Baseline, &baseline_case, &baseline),
                                side_of(DefinitionRole::Mutant, &mutant_case, mutated),
                            ],
                            reaching: Reaching {
                                role,
                                leaf: Some(index_u64(index)),
                                step: None,
                                configuration: None,
                            },
                            kill: Some(kind),
                            steps: Some(leaf.depth),
                            reaching_state: leaf.state.to_string(),
                            krun_command,
                            mutant_krun_command,
                            program,
                            comparable: None,
                            config_vars: binding_texts(&baseline_case.instantiated),
                        });
                    } else {
                        run.class = OutcomeClass::Unsupported;
                        run.unjudged = Some(UnjudgedReason::EngineDefect);
                        run.defects
                            .push("a kill names no leaf of either result".to_owned());
                    }
                }
                run.incidental = self.baseline_incidental(values, &baseline_case, &baseline);
            }
            Err(defect) => {
                run.class = OutcomeClass::Unsupported;
                run.unjudged = Some(UnjudgedReason::EngineDefect);
                run.defects.push(defect.description);
            }
        }
        if run.class == OutcomeClass::Rejected {
            run.rejection = Some(RejectionReason::BackendRefused);
        }
        Ok(run)
    }
}

/// The findings each name of `assume_joined` matches on the definition `role` with `heads`,
/// added to `matched` (in the order of `assume_joined`).
///
/// # Errors
///
/// [`CampaignError::InvalidOptions`] when a name matches a decided finding, which cannot be
/// assumed, or more than one finding of the definition.
fn match_assumed(
    assume_joined: &[String],
    role: DefinitionRole,
    heads: &DataHeads,
    matched: &mut [Vec<(DefinitionRole, Vec<String>, String)>],
) -> Result<(), CampaignError> {
    let side_name = match role {
        DefinitionRole::Baseline => "baseline",
        DefinitionRole::Mutant => "mutant",
    };
    for (given, found) in assume_joined.iter().zip(matched) {
        let (prefix, rest) = crate::findings::side_of(given);
        if prefix.is_some_and(|prefix| prefix != role) {
            continue;
        }
        if let Some((decided, why)) = crate::findings::decided_named(rest, heads) {
            return Err(CampaignError::InvalidOptions {
                message: format!(
                    "assume-joined names `{given}`, which matches `{decided}` of the \
                     {side_name}, a decided finding that cannot be assumed: {why}; change that \
                     equation"
                ),
            });
        }
        let pairs = crate::findings::named_findings(rest, heads);
        if pairs.len() > 1 {
            let candidates = pairs
                .iter()
                .map(|(_, written)| written.clone())
                .collect::<Vec<_>>()
                .join("; ");
            return Err(CampaignError::InvalidOptions {
                message: format!(
                    "assume-joined names `{given}`, which matches more than one finding of the \
                     {side_name} ({candidates}); give more of each file's path"
                ),
            });
        }
        found.extend(
            pairs
                .into_iter()
                .map(|(identities, written)| (role, identities, written)),
        );
    }
    Ok(())
}

/// The warning for a definition (`side_name`) whose check reports findings not assumed joined,
/// so no end of it is data, counting them by verdict.
fn not_confluent_warning(side_name: &str, heads: &DataHeads) -> String {
    let count = |predicate: fn(&Finding) -> bool| {
        heads
            .findings()
            .iter()
            .filter(|finding| predicate(finding))
            .count()
    };
    let genuine = count(Finding::is_genuine);
    let decided = count(Finding::is_decided);
    let total = heads.findings().len();
    format!(
        "definition-not-confluent ({side_name}): its full critical-pair check reports {total} \
         finding{} not assumed joined ({genuine} genuine, {} undecided{}), so no end of it is \
         data; each is listed in the report's definition-findings",
        if total == 1 { "" } else { "s" },
        total - genuine - decided,
        if decided == 0 {
            String::new()
        } else {
            format!(", {decided} decided")
        }
    )
}

/// The names of `assume_joined` against the pair each matched on each definition (`matched`,
/// in the same order): refused when one matches no pair, or different equation pairs on the two
/// definitions; otherwise the warning stating the premise, when there is one.
fn check_assumed(
    assume_joined: &[String],
    matched: &[Vec<(DefinitionRole, Vec<String>, String)>],
) -> Result<Option<String>, CampaignError> {
    for (given, found) in assume_joined.iter().zip(matched) {
        if found.is_empty() {
            return Err(CampaignError::InvalidOptions {
                message: format!(
                    "assume-joined names `{given}`, which matches no unjoined pair, nor any other \
                     finding, of the definitions' critical-pair checks; name a finding as the \
                     report's definition-findings name it (FIRST,SECOND@POSITION for a pair, \
                     hook:EQUATION, equation:EQUATION or precondition:... for the others), \
                     optionally after `baseline:` or `mutant:`"
                ),
            });
        }
        if let [(_, first, written_first), (_, second, written_second)] = &found[..]
            && first != second
        {
            return Err(CampaignError::InvalidOptions {
                message: format!(
                    "assume-joined names `{given}`, which matches different equation pairs or \
                     findings on the two definitions (baseline {written_first}, mutant {written_second}); name each \
                     with `baseline:` or `mutant:` before it"
                ),
            });
        }
    }
    Ok((!assume_joined.is_empty()).then(|| {
        format!(
            "assume-joined: the verdicts of this campaign hold for the definitions read as if \
             the findings {} did not hold (each pair joined, each equation agreeing with its \
             hook or applied as written, each precondition met), not for the definitions as \
             written",
            assume_joined
                .iter()
                .map(|name| format!("`{name}`"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }))
}

/// `reason`, with [`UnjudgedReason::DefinitionNotConfluent`] in place of a reason that an end
/// is not data ([`UnjudgedReason::ReachedEndNotData`], [`UnjudgedReason::MutantEndNotData`],
/// [`UnjudgedReason::BaselineEndNotData`]) when a definition of the case has no data: its full
/// critical-pair check reported findings, so none of its ends is data, and the side's own reason
/// would send the reader to the end instead of the definition.
fn data_reason(
    reason: Option<UnjudgedReason>,
    baseline: &Side,
    mutant: Option<&Side>,
) -> Option<UnjudgedReason> {
    let without_data = |side: &Side| {
        side.executor
            .computed_data_heads()
            .is_some_and(|heads| !heads.confluent())
    };
    match reason {
        Some(
            UnjudgedReason::ReachedEndNotData
            | UnjudgedReason::MutantEndNotData
            | UnjudgedReason::BaselineEndNotData,
        ) if without_data(baseline) || mutant.is_some_and(without_data) => {
            Some(UnjudgedReason::DefinitionNotConfluent)
        }
        reason => reason,
    }
}

impl LiveCases {
    /// The crash of `result`, the run of `side` from `prepared`, made with strategy `paths` and
    /// `terminal_rules` on `definition` (whose compiled directory a `krun` line leaves as
    /// `directory`), when its failure is a crash (`crate::exec::CaseFailure::crash_kind`), or,
    /// without a failure, when one of its leaves halted on an internal cause (the first in leaf
    /// order, `crate::exec::CaseResult::internal_halt`; FZ-CRASH-CAUSE): a crash of kind
    /// `internal-halt` at stage `execute`, whose site is the cause. The backend did not panic,
    /// so the runner is not poisoned and nothing is rebuilt.
    #[expect(
        clippy::too_many_arguments,
        reason = "what a krun line of the crashed run needs, beside the run"
    )]
    fn crash_of(
        spec: &CampaignSpec,
        result: &CaseResult,
        side: CrashSide,
        definition: &CompiledDefinition,
        directory: &str,
        paths: PathMode,
        terminal_rules: &[String],
        prepared: &Prepared,
        cancel: Option<&CancellationToken>,
    ) -> Option<Box<CaseCrash>> {
        let (kind, stage, message, location, cause_site) = if let Some(failure) = &result.failure {
            let kind = failure.crash_kind()?;
            let location = match &failure.cause {
                FailureCause::Panic(record) => record.location.clone(),
                _ => None,
            };
            (kind, failure.stage, failure.message.clone(), location, None)
        } else {
            let internal = result.internal_halt()?;
            (
                CrashKind::InternalHalt,
                CrashStage::Execute,
                internal.message.clone(),
                None,
                Some(internal.site.clone()),
            )
        };
        let krun_command = (stage == CrashStage::Execute)
            .then(|| {
                Self::krun_command(
                    definition,
                    directory,
                    &spec.options,
                    paths,
                    terminal_rules,
                    &prepared.instantiated,
                )
            })
            .flatten();
        Some(Box::new(CaseCrash {
            kind,
            side,
            stage,
            message,
            location,
            cause_site,
            clock: result.safety_limit_hit || cancel.is_some_and(CancellationToken::is_cancelled),
            krun_command,
            program: program_text(&prepared.instantiated),
            config_vars: binding_texts(&prepared.instantiated),
        }))
    }

    /// Whether a run of class `class` gets an incidental finding
    /// ([`crate::report::Incidentals`]): the class is `stuck` or `undefined`, the run the finding
    /// comes from is inside the determinism contract (`reproduces`), so that the finding
    /// reproduces, and the loop has not kept a finding of that class yet
    /// ([`CaseRunner::incidental_kept`]). Only that run counts: in a differential case a clock
    /// or stack fact of the mutant's run says nothing about the baseline's.
    fn wants_incidental(&self, class: OutcomeClass, reproduces: bool) -> bool {
        matches!(class, OutcomeClass::Stuck | OutcomeClass::Undefined)
            && reproduces
            && !self.incidental_kept.contains(&class)
    }

    /// The incidental finding of a differential case with `values`: the baseline's own run of
    /// the case (`baseline`, all paths, from `baseline_case`), classed alone with no target,
    /// whatever the pair's class ([`crate::report::Incidentals`]). A stop or undefined step only
    /// the mutant has is no finding, and whether the finding reproduces is the baseline run's
    /// determinism alone.
    fn baseline_incidental(
        &self,
        values: &[Value],
        baseline_case: &Prepared,
        baseline: &CaseResult,
    ) -> Option<(OutcomeClass, Box<IncidentalCase>)> {
        let class = exec::classify(baseline, &vec![false; baseline.leaves.len()], false).ok()?;
        if !self.wants_incidental(class, baseline.determinism_breaks().is_empty()) {
            return None;
        }
        self.incidental_of(
            class,
            values,
            baseline_case,
            baseline,
            PathMode::AllPaths,
            &[],
        )
    }

    /// The incidental finding of class `class` of a case with `values`, from the baseline's
    /// prepared case and its `result`, run in `paths` with `terminal_rules`: the first leaf that
    /// shows the class ([`incidental::shows`]), with `case` 0 (the loop numbers it); `None` when
    /// no leaf does.
    ///
    /// `krun` reports an undefined step only when every leaf of its run is one (it prints the
    /// other leaves' configurations and drops the undefined steps), so when another leaf of
    /// `result` is not, the krun line says that it will not show the finding.
    fn incidental_of(
        &self,
        class: OutcomeClass,
        values: &[Value],
        prepared: &Prepared,
        result: &CaseResult,
        paths: PathMode,
        terminal_rules: &[String],
    ) -> Option<(OutcomeClass, Box<IncidentalCase>)> {
        let index = incidental::leaf_of(result, class)?;
        let leaf = result.leaves.get(index)?;
        let leaves = index_u64(result.leaves.len());
        let hidden = class == OutcomeClass::Undefined
            && result.leaves.iter().any(|leaf| {
                !matches!(
                    leaf.halt,
                    HaltReasonOutput::Trivial | HaltReasonOutput::Vacuous
                )
            });
        let krun_command = Self::krun_command(
            &self.baseline.definition,
            "<definition-dir>",
            &self.spec.options,
            paths,
            terminal_rules,
            &prepared.instantiated,
        )
        .map(|line| {
            if hidden {
                let note = format!(
                    "krun reports an undefined step only when every path takes one, and another \
                     path of this run does not: this finding is leaf {index} of {leaves}, an \
                     undefined step at step {}",
                    leaf.depth.saturating_add(1)
                );
                // One trailing comment: a line that already has one (the max-work note) takes
                // the note as a further clause of it.
                if line.contains("  # ") {
                    format!("{line}; {note}")
                } else {
                    format!("{line}  # {note}")
                }
            } else {
                line
            }
        });
        let finding = IncidentalCase {
            case: 0,
            holes: self.hole_values(values, &prepared.printed),
            leaves,
            leaf: index_u64(index),
            steps: leaf.depth,
            k_heads: incidental::k_heads(&leaf.state, self.baseline.holes.text.as_ref()),
            configuration: leaf.state.to_string(),
            krun_command,
            // A differential campaign's finding is always its baseline's own all-paths run
            // (`Self::baseline_incidental`).
            baseline_run: self.spec.definitions.mutant.is_some(),
        };
        Some((class, Box::new(finding)))
    }
}

/// The run-level parts of a [`CaseRun`]: coverage from `covered`, work and determinism and load
/// records from every side.
fn run_of(covered: &CaseResult, sides: &[&CaseResult]) -> CaseRun {
    let (applied, matched, applied_counts) =
        covered
            .coverage
            .as_ref()
            .map_or_else(Default::default, |coverage| {
                (
                    coverage.applied.clone(),
                    coverage.matched.clone(),
                    coverage.applied_counts.clone().unwrap_or_default(),
                )
            });
    let conditions = covered
        .coverage
        .as_ref()
        .and_then(|coverage| coverage.conditions.as_deref());
    let guards = conditions.map(score::records::guards).unwrap_or_default();
    let comparisons = conditions
        .map(|conditions| {
            score::records::comparisons(conditions, crate::proposers::runtime::MAX_COMPARISONS)
        })
        .unwrap_or_default();
    let mut load_records = Vec::new();
    for side in sides {
        load_records.extend(side.load_records.iter().cloned());
    }
    CaseRun {
        class: OutcomeClass::Unsupported,
        work: sides
            .iter()
            .map(|side| side.work.max(1))
            .fold(0, u64::saturating_add),
        applied,
        matched,
        applied_counts,
        blocked: false,
        guards,
        comparisons,
        progress: None,
        outside_determinism: sides
            .iter()
            .any(|side| !side.determinism_breaks().is_empty()),
        rejection: None,
        unjudged: None,
        load_records,
        defects: Vec::new(),
        warnings: Vec::new(),
        hit: None,
        incidental: None,
        cut: Cut::default(),
        baseline_ended_within: None,
        pattern_body_matches: None,
        crash: None,
        poisoned: false,
    }
}

/// For a case not judged because a leaf is not ceil-free ([`UnjudgedReason::NotCeilFree`]: an
/// `unsupported` case, or a `baseline-incomplete` one whose baseline holds such a leaf), a
/// warning naming each partial function whose application a leaf of `result` holds, and one for
/// a term-level `\and` of two different sides; the report lists each distinct text once, so the
/// warnings name the functions, not the cases.
fn partial_warnings(result: &CaseResult, reason: Option<UnjudgedReason>) -> Vec<String> {
    if reason != Some(UnjudgedReason::NotCeilFree) {
        return Vec::new();
    }
    let mut functions: Vec<&str> = result
        .leaves
        .iter()
        .flat_map(|leaf| &leaf.unclean)
        .filter_map(|reason| match reason {
            UncleanReason::NotCeilFree(Some(function)) => Some(function.as_str()),
            _ => None,
        })
        .collect();
    functions.sort_unstable();
    functions.dedup();
    functions
        .into_iter()
        .map(|function| {
            if function == crate::exec::run::AND_NOTE {
                return "not-ceil-free: a leaf holds a term-level `\\and` of two different \
                        terms, which denotes a value only where they are equal, so the case \
                        could not be judged"
                    .to_owned();
            }
            format!(
                "not-ceil-free: a leaf holds an application of `{function}` that no equation \
                 evaluates (a partial function, or one defined only by `anywhere` or overload \
                 rules), so the configuration may denote no value and the case could not be \
                 judged; a program or hole range whose runs avoid that application can be"
            )
        })
        .collect()
}

/// Which bounds stopped paths of `result` ([`Cut`]).
fn cut_of(result: &CaseResult) -> Cut {
    use HaltReasonOutput as H;
    let halted = |halts: &[H]| result.leaves.iter().any(|leaf| halts.contains(&leaf.halt));
    Cut {
        depth: halted(&[H::DepthBound, H::BreadthBound]),
        work: halted(&[H::WorkBound]),
        clock: result.safety_limit_hit
            || halted(&[H::Timeout, H::Cancelled])
            || result.failure.as_ref().is_some_and(|failure| {
                matches!(
                    failure.cause,
                    FailureCause::Stop(StopCause::Cancelled | StopCause::Deadline(_))
                )
            }),
    }
}

/// Whether the backend refused `result`'s initial state: an `Err` for a refused state, or every
/// leaf `vacuous` at depth 0, which classification makes `rejected`.
pub(crate) fn refused(result: &CaseResult) -> bool {
    matches!(
        exec::classify(result, &vec![false; result.leaves.len()], false),
        Ok(OutcomeClass::Rejected)
    )
}

fn index_u64(index: usize) -> u64 {
    u64::try_from(index).expect("a leaf index fits in u64")
}

/// Run both sides of a differential case on their initial configurations, the mutant also on
/// all paths where [`Side::rerun_on_all_paths`] asks for it, each leaf's data judgement checked
/// by the other definition too ([`judge_data_in`]): the baseline's result, the mutant's one-path
/// result and its all-paths re-run.
fn run_sides(
    baseline_side: &mut Side,
    mutant: &mut Side,
    baseline_state: &KorePattern,
    mutant_state: &KorePattern,
    run_to_completion: bool,
    cancel: Option<&CancellationToken>,
) -> Result<(CaseResult, CaseResult, Option<CaseResult>), Abort> {
    let mut baseline =
        baseline_side
            .executor
            .run(baseline_state, &baseline_side.shape, &[], cancel)?;
    let mut one_path = mutant
        .executor
        .run(mutant_state, &mutant.shape, &[], cancel)?;
    judge_data_in(&mut mutant.executor, &mut baseline);
    judge_data_in(&mut baseline_side.executor, &mut one_path);
    let mut rerun = mutant.rerun_on_all_paths(
        mutant_state,
        &baseline,
        &one_path,
        run_to_completion,
        cancel,
    )?;
    if let Some(all_paths) = &mut rerun {
        judge_data_in(&mut baseline_side.executor, all_paths);
    }
    Ok((baseline, one_path, rerun))
}

/// Keep a leaf of `result` judged data only where `other`, the executor of the pair's other
/// definition, judges its state data too ([`Executor::is_data_here`]). Condition 4 compares ends
/// across the two definitions, so each compared end must be data in both, each judged by its own
/// definition (`k_rust_backend::data_term`, "Two definitions").
fn judge_data_in(other: &mut Executor, result: &mut CaseResult) {
    for leaf in &mut result.leaves {
        if leaf.data_end == Some(true) && !other.is_data_here(&leaf.state) {
            leaf.data_end = Some(false);
        }
    }
}

fn side_of(role: DefinitionRole, prepared: &Prepared, result: &CaseResult) -> WitnessSide {
    WitnessSide {
        role,
        initial_configuration: prepared.assembled.to_string(),
        final_configurations: result
            .leaves
            .iter()
            .map(|leaf| leaf.state.to_string())
            .collect(),
        halts: result.leaves.iter().map(|leaf| leaf.halt).collect(),
    }
}

/// The work of `baseline`, a differential case's baseline run, when no bound and no clock cut
/// it: every path of it reached its end.
fn ended_within(baseline: &CaseResult) -> Option<u64> {
    let cut = cut_of(baseline);
    (!(cut.depth || cut.work || cut.clock)).then_some(baseline.work)
}

/// The instantiated program text of a case, for a campaign with a program text.
fn program_text(instantiated: &InstantiatedProgram) -> Option<String> {
    match instantiated {
        InstantiatedProgram::Source {
            program: Some(program),
            ..
        } => Some(program.text.clone()),
        _ => None,
    }
}

/// The instantiated configuration-variable bindings of a case, by name; empty for a KORE
/// template.
fn binding_texts(instantiated: &InstantiatedProgram) -> BTreeMap<String, String> {
    match instantiated {
        InstantiatedProgram::Source { config_vars, .. } => config_vars.iter().cloned().collect(),
        InstantiatedProgram::Kore(_) => BTreeMap::new(),
    }
}

/// `text` quoted for a POSIX shell.
/// The pattern of a target `at: any-state`.
fn any_state_pattern(target: &crate::Target) -> Option<&str> {
    match &target.kind {
        TargetKind::Pattern(crate::target::PatternTarget {
            pattern,
            at: crate::target::PatternAt::AnyState,
        }) => Some(pattern),
        TargetKind::Rule(_)
        | TargetKind::Pattern(_)
        | TargetKind::Differential(_)
        | TargetKind::Observer(_) => None,
    }
}

fn quote(text: &str) -> String {
    if !text.is_empty()
        && text
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "-_./=:".contains(c))
    {
        return text.to_owned();
    }
    format!("'{}'", text.replace('\'', r"'\''"))
}

/// What confirmations reuse (ARCHITECTURE 7): each side's internalized definition, which every
/// confirmation copies into a fresh backend; its compiled normal-termination pattern and the
/// target's compiled patterns, which are backend-independent KORE that each fresh backend
/// prepares for itself (`exec::run::PatternCompiler`: a function of the definition, the program
/// grammar and the pattern text); and its hole resolution and round-trip positions, which
/// depend only on the grammar, the program and the hole declarations. Every confirmation still
/// builds a fresh `Backend`, a fresh program assembly that assembles its configuration from the
/// instantiated text, and a freshly resolved target (its rule looked up in the fresh backend's
/// catalog, its patterns prepared on it). Internalization is a pure function of the KORE
/// definition, the main module and the rewrite order; the result is immutable apart from lazily computed facts of the
/// definition itself (`OnceLock`s of inhabited sorts and the like), which are the same whoever
/// computes them. Every mutable cache that could make a run depend on earlier runs (the
/// solver and its cache of decided answers, the session's module table) belongs to the
/// `Backend`, which each confirmation builds anew, so no such state is shared.
///
/// Confirmation therefore re-executes the case independently, but it does not re-derive the
/// hole resolution or the round-trip positions: they are computed on a build of their own, by
/// the same code that computed the campaign's, so a defect of that code is not caught by
/// confirmation (phase-1 review N8, accepted by INT-A item 3).
///
/// The internalized definition is not internalized again: it is the one the campaign's own
/// backend was built from, which that backend's session holds behind an `Arc` and never
/// changes ([`Side::internalized`]). It is shared rather than copied, so a campaign internalizes
/// each definition once and the cache adds no copy of it (phase-1 review N9). Sharing it shares
/// no run state: the facts a run may have filled in lazily are functions of the definition
/// alone, computed by infallible initializers, so a copy taken after some runs behaves as one
/// taken before any.
///
/// Only the `source-execution` route's internalization is cached: the `from-definition` route
/// internalizes inside the backend's session, and a confirmation on it builds its backend from
/// the KORE as the campaign's own backend was built.
pub(crate) struct DefinitionCache {
    baseline: SideCache,
    mutant: Option<SideCache>,
    /// The target's patterns compiled for the baseline definition
    /// ([`ResolvedTarget::compiled_patterns`]); empty for a differential target.
    target_patterns: Vec<CompiledPattern>,
}

/// One side's part of a [`DefinitionCache`].
struct SideCache {
    internalized: Option<Arc<BackendDefinition>>,
    data_heads: Option<DataHeads>,
    normal_end: NormalEnd,
    holes: ResolvedHoles,
    round_trip: Arc<RoundTripCheck>,
}

impl SideCache {
    fn seed(&self) -> Seed<'_> {
        Seed {
            internalized: self.internalized.as_ref(),
            data_heads: self.data_heads.as_ref(),
            normal_end: Some(&self.normal_end),
            resolved: Some((&self.holes, &self.round_trip)),
            assembly: None,
        }
    }

    fn of(side: Side) -> Self {
        Self {
            internalized: side.internalized,
            data_heads: side.executor.computed_data_heads().cloned(),
            normal_end: side.normal_end,
            holes: side.holes,
            round_trip: side.round_trip,
        }
    }
}

impl DefinitionCache {
    /// Take each `source-execution` definition's internalization from `cases`, the campaign's
    /// own case execution, then, on a build of its own (not the campaign's), compile the
    /// normal-termination pattern and the target's patterns, resolve the holes and locate their
    /// positions once.
    ///
    /// # Errors
    ///
    /// The first refusal, as a [`CampaignError`].
    pub(crate) fn build(
        spec: &Arc<CampaignSpec>,
        cases: &LiveCases,
    ) -> Result<Self, CampaignError> {
        let of = |side: &Side| {
            (
                side.internalized.clone(),
                side.executor.computed_data_heads().cloned(),
            )
        };
        let baseline = of(&cases.baseline);
        let mutant = match &cases.judge {
            Judge::Differential(mutant) => of(mutant),
            Judge::Target(_) => (None, None),
        };
        let side = |definition,
                    role,
                    (internalized, data_heads): &(
            Option<Arc<BackendDefinition>>,
            Option<DataHeads>,
        )| {
            Side::build(
                spec,
                definition,
                role,
                Seed {
                    internalized: internalized.as_ref(),
                    data_heads: data_heads.as_ref(),
                    ..Seed::default()
                },
            )
        };
        let mut baseline_side = side(
            &spec.definitions.baseline,
            DefinitionRole::Baseline,
            &baseline,
        )?;
        let target_patterns = if let TargetKind::Differential(_) = spec.target.kind {
            Vec::new()
        } else {
            ResolvedTarget::resolve(
                &spec.target,
                &mut baseline_side.executor,
                &spec.definitions.baseline,
                &baseline_side.assembly,
            )?
            .compiled_patterns()
        };
        let baseline = SideCache::of(baseline_side);
        let mutant = match &spec.definitions.mutant {
            Some(definition) => Some(SideCache::of(side(
                definition,
                DefinitionRole::Mutant,
                &mutant,
            )?)),
            None => None,
        };
        Ok(Self {
            baseline,
            mutant,
            target_patterns,
        })
    }
}

/// The rule graph of the baseline definition with the campaign's entry (ARCHITECTURE 6.3),
/// computed once per campaign from the hole template ([`graph::entry::hole_template`]) on the
/// graph's own backend, which no case uses, so that its solver cache is no case's. On the
/// `source-execution` route that backend is built from a copy of the campaign's internalized
/// definition ([`Side::internalized`]) rather than from a second internalization (phase-1
/// review N9).
///
/// The graph's warnings go into the report, and every case's coverage `applied` is checked
/// against the entry: a rule applied outside the graph, or an id the definition does not know,
/// is an engine defect noted on the case ([`RuleGraph::unreachable_applied`]), and an id the
/// check cannot judge is a warning. The check costs under 1% of a case on the IMP and maze
/// fixtures (a breadth-first search over the graph per case), so it runs on every case. Differential
/// campaigns are not checked: a case's coverage there is the mutant's, and each side would need
/// its own graph.
pub(crate) struct GraphCheck {
    graph: RuleGraph,
    entry: Entry,
    /// The warnings for the report: the vacuous-template warning, and for a rule target the
    /// `statically-unreachable` warning.
    warnings: Vec<String>,
}

impl GraphCheck {
    /// Build the graph and the entry for `cases`' baseline and target, or `None` when there is
    /// no entry: a differential campaign, a template that cannot be built (a hole position that
    /// does not lead to a subterm, a hole sort without a KORE sort), a backend or graph that
    /// does not build, or a template that does not execute at depth 0. No entry means no
    /// warning and no self-check, never a refusal of the campaign.
    pub(crate) fn build(spec: &CampaignSpec, cases: &LiveCases) -> Option<Self> {
        let Judge::Target(target) = &cases.judge else {
            return None;
        };
        let side = &cases.baseline;
        let mut holes = Vec::new();
        for (position, hole) in side.round_trip.positions().iter().zip(&side.holes.holes) {
            if let Some(path) = position {
                holes.push((path.clone(), hole.kore_sort().ok()?));
            }
        }
        let template = graph::entry::hole_template(side.round_trip.anchor_configuration(), &holes)?;
        let options = spec.options.backend.options();
        let mut backend = match &side.internalized {
            Some(internalized) => {
                Backend::from_internalized(BackendDefinition::clone(internalized), options).ok()?
            }
            None => build_backend(&spec.definitions.baseline, options).ok()?,
        };
        let graph = RuleGraph::of_backend(&mut backend).ok()?;
        let entry = graph
            .entry(&mut backend, side.shape.request(template))
            .ok()?;
        let mut warnings = Vec::new();
        warnings.extend(graph.vacuous_warning(&entry).ok().flatten());
        if let Some(id) = target.rule_id() {
            warnings.extend(graph.statically_unreachable(&entry, id).ok().flatten());
        }
        Some(Self {
            graph,
            entry,
            warnings,
        })
    }

    /// The rule graph of the baseline definition, which the dictionary also harvests from
    /// (ARCHITECTURE 8.3), so that it builds no graph or backend of its own.
    pub(crate) fn graph(&self) -> &RuleGraph {
        &self.graph
    }

    /// The warnings the report carries for this campaign.
    pub(crate) fn warnings(&self) -> &[String] {
        &self.warnings
    }

    /// The self-check of one case whose coverage `applied` holds `applied`: the engine defects
    /// (one per applied rule the graph cannot reach from the entry and per unknown id,
    /// [`graph::entry::AppliedCheck::defects`]) and the warnings (one per id shared by a rule
    /// and an equation whose rule is unreachable, which the check cannot judge).
    pub(crate) fn check(&self, applied: &[String]) -> (Vec<String>, Vec<String>) {
        match self
            .graph
            .unreachable_applied(&self.entry, applied.iter().map(String::as_str))
        {
            Ok(check) => (check.defects(), check.warnings()),
            Err(foreign) => (vec![foreign.to_string()], Vec::new()),
        }
    }
}

/// Each side's program assembly and definition, shared with its [`Side`], which a run's
/// [`RunAssemblers`] borrow ([`LiveCases::assembly_parts`]).
pub(crate) struct AssemblyParts {
    baseline: (Arc<ProgramAssembly>, Arc<CompiledDefinition>),
    mutant: Option<(Arc<ProgramAssembly>, Arc<CompiledDefinition>)>,
}

impl AssemblyParts {
    /// One assembler per side, for every case of a run.
    pub(crate) fn assemblers(&self) -> RunAssemblers<'_> {
        RunAssemblers {
            baseline: self.baseline.0.assembler(&self.baseline.1),
            mutant: self
                .mutant
                .as_ref()
                .map(|(assembly, definition)| assembly.assembler(definition)),
        }
    }
}

/// The assemblers a run keeps for its cases, one per side: each keeps its program parser, macro
/// expander and sort injectors across the cases, which a fresh assembler per case would
/// rebuild (D14, G16). The assembler's caches depend on the grammar alone, and it is left
/// empty after every configuration it assembles or refuses, so a case's configuration is the
/// one a fresh assembler builds (`assemble.rs`).
pub(crate) struct RunAssemblers<'a> {
    baseline: CaseAssembler<'a>,
    mutant: Option<CaseAssembler<'a>>,
}

/// The campaign's runner: the campaign's own [`LiveCases`] for cases, assembled by the run's
/// [`RunAssemblers`], and a fresh [`LiveCases`] with fresh assemblers per confirmation, built
/// from the campaign's [`DefinitionCache`] (filled on the first confirmation).
pub(crate) struct LiveRunner<'a> {
    pub(crate) cases: LiveCases,
    /// The parts [`Self::assemblers`] borrow: [`Self::cases`]' first build's
    /// [`LiveCases::assembly_parts`], immutable functions of the definitions and the program
    /// grammar, which a rebuild's sides reuse, so that its fresh assemblers are built from the
    /// rebuilt sides' own assemblies.
    pub(crate) parts: &'a AssemblyParts,
    /// The assemblers of [`Self::cases`]' sides, built from [`Self::parts`].
    pub(crate) assemblers: RunAssemblers<'a>,
    pub(crate) cache: Arc<OnceLock<Result<DefinitionCache, String>>>,
    /// The campaign's rule-graph self-check, run on every case's coverage.
    pub(crate) graph: Option<Arc<GraphCheck>>,
    /// What the run asked of [`Self::cases`] after building it, which every rebuild asks
    /// again ([`RunSetup`]).
    pub(crate) setup: RunSetup,
    /// The internalized definitions the `from-definition` route's rebuilds copy, read from the
    /// campaign's backend sessions at the first rebuild ([`LiveCases::sessions`]).
    pub(crate) sessions: Option<Sessions>,
}

/// What a run asks of its case execution after building it (`Campaign::run`): the condition
/// entries of the climb's, the solve proposer's and the corpus's rules, and the corpus's
/// applied counts. The run applies it to its [`LiveCases`], and every rebuild after a crash
/// applies it again ([`LiveRunner::recover`]), so that a rebuilt runner's cases record what the
/// campaign's own would have (FZ-CRASH review S1).
#[derive(Clone, Debug, Default)]
pub(crate) struct RunSetup {
    /// The rules whose condition entries every case records; empty for none.
    pub(crate) condition_rules: Vec<String>,
    /// Every case counts how many times its run applied each rule.
    pub(crate) counts: bool,
}

impl RunSetup {
    /// Ask `cases` for what this setup names.
    pub(crate) fn apply(&self, cases: &mut LiveCases) {
        if !self.condition_rules.is_empty() {
            cases.request_conditions(self.condition_rules.clone());
        }
        if self.counts {
            cases.request_counts();
        }
    }
}

/// Each side's internalized definition, held by its backend session on the `from-definition`
/// route ([`LiveCases::sessions`]).
#[derive(Clone, Default)]
pub(crate) struct Sessions {
    baseline: Option<Arc<BackendDefinition>>,
    mutant: Option<Arc<BackendDefinition>>,
    /// Each side's program assembly from the runner's parts, which a rebuild reuses.
    baseline_assembly: Option<Arc<ProgramAssembly>>,
    mutant_assembly: Option<Arc<ProgramAssembly>>,
}

impl CaseRunner for LiveRunner<'_> {
    fn run_case(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, Abort> {
        let mut run = run_live(&mut self.cases, &mut self.assemblers, values, cancel)?;
        run.poisoned = self.cases.poisoned();
        self.self_check(&mut run);
        Ok(run)
    }

    /// A fresh [`LiveCases`] in place of the campaign's (FZ-CRASH): built from the
    /// confirmations' [`DefinitionCache`] as a confirmation is (`LiveCases::build_with`), each
    /// `from-definition` side's backend from a copy of the internalized definition its old
    /// session held ([`Sessions`]), with the run's [`RunSetup`] applied, fresh assemblers, and
    /// the incidental classes already kept. Building the cache from the campaign's
    /// possibly poisoned cases is sound: it reads only the shared internalized definitions and
    /// the data heads, which are set only once computed.
    fn recover(&mut self) -> Result<(), String> {
        #[cfg(test)]
        if crate::exec::run::seam::recover_fails() {
            return Err("the test seam refuses the rebuild".into());
        }
        let spec = Arc::clone(&self.cases.spec);
        let cases = &self.cases;
        let cache = self
            .cache
            .get_or_init(|| DefinitionCache::build(&spec, cases).map_err(|error| error.to_string()))
            .as_ref()
            .map_err(|error| format!("the definition cache did not build: {error}"))?;
        let parts = self.parts;
        let sessions = self.sessions.get_or_insert_with(|| Sessions {
            baseline_assembly: Some(Arc::clone(&parts.baseline.0)),
            mutant_assembly: parts
                .mutant
                .as_ref()
                .map(|(assembly, _)| Arc::clone(assembly)),
            ..self.cases.sessions()
        });
        let mut fresh = LiveCases::build_seeded(spec, Some(cache), sessions)
            .map_err(|error| error.to_string())?;
        self.setup.apply(&mut fresh);
        fresh.incidental_kept = std::mem::take(&mut self.cases.incidental_kept);
        self.cases = fresh;
        self.assemblers = self.parts.assemblers();
        Ok(())
    }

    /// A fresh `Backend` (fresh solver, fresh session) over a copy of the cached internalized
    /// definition, with a fresh assembly, fresh hole resolution and a freshly resolved target.
    ///
    /// A confirmation is self-checked against the rule graph like a case.
    fn confirm(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, ConfirmFailure> {
        let mut fresh = self.fresh()?;
        let parts = fresh.assembly_parts();
        let mut assemblers = parts.assemblers();
        let mut run =
            run_live(&mut fresh, &mut assemblers, values, cancel).map_err(ConfirmFailure::Abort)?;
        self.self_check(&mut run);
        Ok(run)
    }

    /// The comparable judgement of `values` on fresh cases built as a confirmation's
    /// ([`Self::fresh`]), so that a crash of that judgement is re-run independently of the
    /// campaign's backends.
    fn confirm_comparability(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Option<Result<JudgedComparability, ConfirmFailure>> {
        let mut fresh = match self.fresh() {
            Ok(fresh) => fresh,
            Err(failure) => return Some(Err(failure)),
        };
        let parts = fresh.assembly_parts();
        let mut assemblers = parts.assemblers();
        comparability_on(&mut fresh, &mut assemblers, values, cancel).map(Ok)
    }

    fn comparability_pending(&self) -> bool {
        match &self.cases.judge {
            Judge::Target(target) => target.judges_outside_the_case(&self.cases.baseline.shape),
            Judge::Differential(_) => false,
        }
    }

    fn incidental_kept(&mut self, class: OutcomeClass) {
        self.cases.incidental_kept.push(class);
    }

    fn comparability(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Option<JudgedComparability> {
        comparability_on(&mut self.cases, &mut self.assemblers, values, cancel)
    }

    fn admissible(&self, hole: usize, value: &Value) -> bool {
        self.cases
            .baseline
            .holes
            .holes
            .get(hole)
            .is_some_and(|hole| {
                values::check_constraints(value, &hole.sort, &hole.constraints).is_ok()
            })
    }
}

/// The comparable judgement of a witness case with `values` that its case did not make, on
/// `cases` assembled by `assemblers` ([`CaseRunner::comparability`]), with the crash of its run
/// of every path and whether a panic was caught.
fn comparability_on(
    cases: &mut LiveCases,
    assemblers: &mut RunAssemblers<'_>,
    values: &[Value],
    cancel: Option<&CancellationToken>,
) -> Option<JudgedComparability> {
    let Judge::Target(target) = &cases.judge else {
        return None;
    };
    let prepared = cases
        .baseline
        .prepare(&mut assemblers.baseline, &cases.spec.program, values)
        .ok()?;
    let side = &mut cases.baseline;
    let (comparable, work, every_path) =
        target.comparability(&mut side.executor, &prepared.assembled, &side.shape, cancel)?;
    let crash = every_path.as_ref().and_then(|every_path| {
        LiveCases::crash_of(
            &cases.spec,
            every_path,
            CrashSide::Baseline,
            &cases.spec.definitions.baseline,
            "<definition-dir>",
            PathMode::AllPaths,
            &[],
            &prepared,
            cancel,
        )
    });
    Some(JudgedComparability {
        comparable,
        work,
        crash,
        poisoned: cases.poisoned(),
    })
}

impl LiveRunner<'_> {
    /// Fresh cases as a confirmation builds them: a fresh `Backend` over a copy of the cached
    /// internalized definition, with a fresh assembly, hole resolution and target.
    fn fresh(&self) -> Result<LiveCases, ConfirmFailure> {
        let spec = Arc::clone(&self.cases.spec);
        let cases = &self.cases;
        let cache = self
            .cache
            .get_or_init(|| DefinitionCache::build(&spec, cases).map_err(|error| error.to_string()))
            .as_ref()
            .map_err(|error| {
                ConfirmFailure::Failed(format!(
                    "the confirmation's definition cache did not build: {error}"
                ))
            })?;
        LiveCases::build_with(spec, Some(cache)).map_err(|error| {
            ConfirmFailure::Failed(format!(
                "the fresh backend or assembly did not build: {error}"
            ))
        })
    }

    /// The rule-graph self-check of an executed run: its engine defects and warnings are added
    /// to the run's.
    fn self_check(&self, run: &mut CaseRun) {
        if let Some(graph) = &self.graph
            && run.class != OutcomeClass::Rejected
        {
            let (defects, warnings) = graph.check(&run.applied);
            run.defects.extend(defects);
            run.warnings.extend(warnings);
        }
    }
}

fn run_live(
    cases: &mut LiveCases,
    assemblers: &mut RunAssemblers<'_>,
    values: &[Value],
    cancel: Option<&CancellationToken>,
) -> Result<CaseRun, Abort> {
    if matches!(cases.judge, Judge::Differential(_)) {
        cases.run_differential(assemblers, values, cancel)
    } else {
        cases.run_target(assemblers, values, cancel)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::{
        holes::{HoleDecl, HoleLocation, SpanAddress},
        spec::{
            CallerIdentity, CaseOptions, DEFAULT_REJECTION_CAP, Definitions, ProposerConfig,
            ProposerKind,
        },
        support::{COIN, IMP},
        target::{PatternAt, PatternTarget, Target},
        values::{Constraints, GenerationBounds},
    };

    fn int_hole(name: &str, find: &str, literal: &str) -> HoleDecl {
        HoleDecl {
            name: name.into(),
            sort: "Int".into(),
            location: HoleLocation::Span(SpanAddress {
                program: "imp/le.imp".into(),
                line: None,
                column: None,
                find: find.into(),
                literal: literal.into(),
            }),
            constraints: Constraints::default(),
            allow_refused_sort: false,
        }
    }

    /// IMP's `le.imp` with `x` and `y` as holes, and the property that `r` ends as 1, on
    /// `route`.
    fn le_spec(route: Option<BackendRoute>) -> Arc<CampaignSpec> {
        let compiled = IMP.compiled();
        let definition = match route {
            Some(route) => compiled.definition_on(route),
            None => compiled.definition(),
        };
        Arc::new(CampaignSpec {
            definitions: Definitions {
                baseline: Arc::new(definition),
                mutant: None,
            },
            program: ProgramInput::Source(compiled.program_source("imp/le.imp")),
            holes: vec![int_hole("X", "x = 3;", "3"), int_hole("Y", "y = 5;", "5")],
            target: Target {
                kind: TargetKind::Pattern(PatternTarget {
                    pattern: concat!(
                        r#"<k> .K </k> <state> (#token("r", "Id") |-> R:Int) _:Map </state> "#,
                        "requires R =/=Int 1"
                    )
                    .into(),
                    at: PatternAt::Final,
                }),
                run_to_completion: false,
                negated_property: true,
                data_end: true,
                comparable: false,
                query_confirmable: false,
            },
            options: CaseOptions::default(),
            proposers: ProposerConfig {
                anchors_first: true,
                explicit: Vec::new(),
                weights: BTreeMap::from([(ProposerKind::Blind, 1)]),
            },
            bounds: GenerationBounds::default(),
            rejection_cap: DEFAULT_REJECTION_CAP,
            seed: 1,
            identity: CallerIdentity::default(),
        })
    }

    fn int(n: i64) -> Value {
        Value::Int(n.into())
    }

    /// Phase-1 review N9: the campaign's backend, the rule graph's and the confirmations' are
    /// all built from one internalization, which the confirmation cache shares without a copy,
    /// while each backend still holds its own copy of it.
    #[test]
    fn a_source_campaign_internalizes_its_definition_once() {
        let spec = le_spec(None);
        let mut cases = LiveCases::build(Arc::clone(&spec)).expect("the campaign builds");
        let internalized = cases
            .baseline
            .internalized
            .clone()
            .expect("the source-execution route keeps its internalization");
        let own = cases
            .baseline
            .executor
            .backend_mut()
            .select_definition(None)
            .expect("loads");
        assert!(Arc::ptr_eq(&own, &internalized), "shared, not copied");
        assert!(GraphCheck::build(&spec, &cases).is_some());
        let cache = DefinitionCache::build(&spec, &cases).expect("the cache builds");
        let cached = cache.baseline.internalized.as_ref().expect("cached");
        assert!(Arc::ptr_eq(cached, &internalized), "the cache adds no copy");
        let mut fresh =
            LiveCases::build_with(Arc::clone(&spec), Some(&cache)).expect("a confirmation builds");
        let copy = fresh
            .baseline
            .executor
            .backend_mut()
            .select_definition(None)
            .expect("loads");
        assert!(
            !Arc::ptr_eq(&copy, &internalized),
            "a confirmation's backend runs on its own copy"
        );
        // The confirmation built from the shared internalization judges as the campaign does:
        // the anchors (3, 5) take the `x <= y` branch, and (5, 3) violates the property.
        let parts = cases.assembly_parts();
        let fresh_parts = fresh.assembly_parts();
        for (values, class) in [
            ([int(3), int(5)], OutcomeClass::Miss),
            ([int(5), int(3)], OutcomeClass::Hit),
        ] {
            let campaign =
                run_live(&mut cases, &mut parts.assemblers(), &values, None).expect("runs");
            let confirmed =
                run_live(&mut fresh, &mut fresh_parts.assemblers(), &values, None).expect("runs");
            assert_eq!(campaign.class, class);
            assert_eq!(confirmed.class, class);
            assert_eq!(
                campaign.hit.map(|hit| hit.reaching_state),
                confirmed.hit.map(|hit| hit.reaching_state)
            );
        }
    }

    /// Accepts at the first step of every path.
    struct FirstStep;

    impl crate::target::Observer for FirstStep {
        type State = ();

        fn start(&self) {}

        fn branch(&self, (): &()) {}

        fn step(
            &self,
            (): &mut (),
            _pre: &crate::target::ConfigurationView,
            _post: &crate::target::ConfigurationView,
        ) -> crate::target::ObserverVerdict {
            crate::target::ObserverVerdict::Hit
        }
    }

    /// FZ-10 review N4: an observer witness names the step at which the observer accepted, as
    /// well as the leaf's own step count, from the case and from its confirmation alike.
    #[test]
    fn an_observer_witness_names_its_hit_step() {
        let compiled = COIN.compiled();
        let spec = Arc::new(CampaignSpec {
            program: ProgramInput::Source(compiled.program_source("coin/count.pgm")),
            holes: vec![HoleDecl {
                name: "N".into(),
                sort: "Int".into(),
                location: HoleLocation::Span(SpanAddress {
                    program: "coin/count.pgm".into(),
                    line: None,
                    column: None,
                    find: "count(3)".into(),
                    literal: "3".into(),
                }),
                constraints: Constraints::default(),
                allow_refused_sort: false,
            }],
            target: Target {
                kind: TargetKind::Observer(crate::target::ObserverTarget::new(
                    "first-step",
                    FirstStep,
                )),
                run_to_completion: false,
                negated_property: false,
                data_end: true,
                comparable: false,
                query_confirmable: false,
            },
            definitions: Definitions {
                baseline: Arc::new(compiled.definition()),
                mutant: None,
            },
            ..CampaignSpec::clone(&le_spec(None))
        });
        let mut cases = LiveCases::build(Arc::clone(&spec)).expect("the campaign builds");
        let cache = DefinitionCache::build(&spec, &cases).expect("the cache builds");
        let mut fresh =
            LiveCases::build_with(Arc::clone(&spec), Some(&cache)).expect("a confirmation builds");
        for cases in [&mut cases, &mut fresh] {
            let parts = cases.assembly_parts();
            let run = run_live(cases, &mut parts.assemblers(), &[int(3)], None).expect("runs");
            assert_eq!(run.class, OutcomeClass::Hit, "{run:?}");
            let hit = run.hit.expect("a hit");
            assert_eq!(hit.reaching.step, Some(1));
            assert!(
                hit.steps > Some(1),
                "the leaf runs on to its end: {:?}",
                hit.steps
            );
        }
    }

    /// FZ-ANYSTATE: a campaign whose pattern is matched `at: any-state` confirms its hit, and the
    /// witness names the depth of the reaching configuration (`count(1)`, two steps after
    /// `count(3)`) and the configuration, with the natural end among its facts under
    /// `run-to-completion`.
    #[test]
    fn an_any_state_witness_names_its_first_reaching_step() {
        let compiled = COIN.compiled();
        let spec = CampaignSpec {
            program: ProgramInput::Source(compiled.program_source("coin/count.pgm")),
            holes: vec![HoleDecl {
                name: "N".into(),
                sort: "Int".into(),
                location: HoleLocation::Span(SpanAddress {
                    program: "coin/count.pgm".into(),
                    line: None,
                    column: None,
                    find: "count(3)".into(),
                    literal: "3".into(),
                }),
                constraints: Constraints::default(),
                allow_refused_sort: false,
            }],
            target: Target {
                kind: TargetKind::Pattern(PatternTarget {
                    pattern: "<k> count(1) ~> _ </k>".into(),
                    at: PatternAt::AnyState,
                }),
                run_to_completion: true,
                negated_property: false,
                data_end: true,
                comparable: false,
                query_confirmable: false,
            },
            definitions: Definitions {
                baseline: Arc::new(compiled.definition()),
                mutant: None,
            },
            proposers: ProposerConfig {
                anchors_first: true,
                explicit: Vec::new(),
                weights: BTreeMap::new(),
            },
            ..CampaignSpec::clone(&le_spec(None))
        };
        let report = crate::Campaign::new(spec)
            .expect("the campaign builds")
            .run(crate::spec::Budget::Cases(1), None);
        assert!(
            report.engine_defects.is_empty(),
            "{:?}",
            report.engine_defects
        );
        let witness = report.witness().expect("a confirmed witness");
        assert_eq!(witness.first.reaching.step, Some(2), "{witness:?}");
        // The reaching configuration names no leaf (FZ-STATESET-MATCH): the witness carries it,
        // and no leaf's step count.
        assert_eq!(witness.first.reaching.leaf, None, "{witness:?}");
        assert_eq!(witness.first.steps, None, "{witness:?}");
        let configuration = witness
            .first
            .reaching
            .configuration
            .as_deref()
            .expect("the reaching configuration");
        assert!(configuration.contains("Lblcount"), "{configuration}");
        // Its krun line is the search that finds it, when the route has one.
        if let Some(krun) = &witness.krun_command {
            assert!(
                krun.contains(" --search-all --pattern ") && !krun.contains("--strategy"),
                "{krun}"
            );
            // A depth bound bounds the search; without one the line says it may not end.
            assert!(
                krun.contains(" --depth ") || krun.contains("this search may not terminate"),
                "{krun}"
            );
        }
        assert!(
            witness
                .clean_leaf_facts
                .iter()
                .any(|fact| fact == "natural-end"),
            "{:?}",
            witness.clean_leaf_facts
        );
    }

    /// Accepts at step `n` of the `n`-th path it is started on: its verdict depends on state
    /// hidden in the observer, which ARCHITECTURE 9.2 forbids.
    struct StepByWalk(std::sync::atomic::AtomicU32);

    impl crate::target::Observer for StepByWalk {
        /// The step to accept at, and the steps seen.
        type State = (u32, u32);

        fn start(&self) -> (u32, u32) {
            let walk = self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            (walk + 1, 0)
        }

        fn branch(&self, state: &(u32, u32)) -> (u32, u32) {
            *state
        }

        fn step(
            &self,
            (accept, seen): &mut (u32, u32),
            _pre: &crate::target::ConfigurationView,
            _post: &crate::target::ConfigurationView,
        ) -> crate::target::ObserverVerdict {
            *seen += 1;
            if seen == accept {
                crate::target::ObserverVerdict::Hit
            } else {
                crate::target::ObserverVerdict::Nothing
            }
        }
    }

    /// HARD-B review S1: an observer that breaks the determinism contract accepts the case at
    /// step 1 and its confirmation at step 2, in the same final configuration. The witness would
    /// report the confirmation's step; confirmation compares where the target was reached, the
    /// hit step included, so the disagreement is an engine defect and no witness is reported.
    #[test]
    fn a_confirmation_at_another_hit_step_is_an_engine_defect() {
        let compiled = COIN.compiled();
        let spec = CampaignSpec {
            program: ProgramInput::Source(compiled.program_source("coin/count.pgm")),
            holes: vec![HoleDecl {
                name: "N".into(),
                sort: "Int".into(),
                location: HoleLocation::Span(SpanAddress {
                    program: "coin/count.pgm".into(),
                    line: None,
                    column: None,
                    find: "count(3)".into(),
                    literal: "3".into(),
                }),
                constraints: Constraints::default(),
                allow_refused_sort: false,
            }],
            target: Target {
                kind: TargetKind::Observer(crate::target::ObserverTarget::new(
                    "step-by-walk",
                    StepByWalk(std::sync::atomic::AtomicU32::new(0)),
                )),
                run_to_completion: false,
                negated_property: false,
                data_end: true,
                comparable: false,
                query_confirmable: false,
            },
            definitions: Definitions {
                baseline: Arc::new(compiled.definition()),
                mutant: None,
            },
            proposers: ProposerConfig {
                anchors_first: true,
                explicit: Vec::new(),
                weights: BTreeMap::new(),
            },
            ..CampaignSpec::clone(&le_spec(None))
        };
        let report = crate::Campaign::new(spec)
            .expect("the campaign builds")
            .run(crate::spec::Budget::Cases(1), None);
        assert!(
            report.witness().is_none(),
            "a witness from a disagreeing confirmation: {:?}",
            report.witness()
        );
        assert_eq!(report.totals.unconfirmed, 1, "{report:?}");
        assert!(
            report
                .engine_defects
                .iter()
                .any(|defect| defect.description.contains("confirmation")),
            "{:?}",
            report.engine_defects
        );
    }

    /// A VALUES campaign whose `$REC` hole's anchor is `rec(1, unit, t)`, where `t` is a tree
    /// `nodes` nodes deep: a value of `nodes + 3` levels (the record, the nodes, `leaf(0)` and
    /// its Int).
    fn deep_record_campaign(nodes: usize) -> Result<crate::Campaign, CampaignError> {
        let compiled = crate::support::VALUES.compiled();
        let tree = format!(
            "{}leaf(0){}",
            "node(".repeat(nodes),
            ", leaf(0))".repeat(nodes)
        );
        let record = format!("rec(1, unit, {tree})");
        let bindings = [
            ("SHAPE", "circle(5)"),
            ("REC", record.as_str()),
            ("PAIR", "1 & 2"),
            ("WRAPPER", "wrap(3)"),
            ("ACCOUNT", "account(1, .Map)"),
            ("LIST", ".List"),
            ("SET", ".Set"),
            ("MAP", ".Map"),
        ];
        crate::Campaign::new(CampaignSpec {
            program: ProgramInput::Source(crate::spec::ProgramSource {
                program: Some(crate::spec::ProgramText {
                    name: "run.values".into(),
                    text: "run".into(),
                    start_sort: "Pgm".into(),
                }),
                config_vars: bindings
                    .iter()
                    .map(|(name, value)| ((*name).to_owned(), (*value).to_owned()))
                    .collect(),
            }),
            holes: vec![HoleDecl {
                name: "R".into(),
                sort: "Rec".into(),
                location: HoleLocation::ConfigVar { name: "REC".into() },
                constraints: Constraints::default(),
                allow_refused_sort: false,
            }],
            target: Target {
                kind: TargetKind::Pattern(PatternTarget {
                    pattern: "<k> .K </k>".into(),
                    at: PatternAt::Final,
                }),
                run_to_completion: false,
                negated_property: false,
                data_end: true,
                comparable: false,
                query_confirmable: false,
            },
            definitions: Definitions {
                baseline: Arc::new(compiled.definition()),
                mutant: None,
            },
            proposers: ProposerConfig {
                anchors_first: true,
                explicit: Vec::new(),
                weights: BTreeMap::new(),
            },
            ..CampaignSpec::clone(&le_spec(None))
        })
    }

    /// HARD-B review S3, round 3: an anchor of [`crate::values::MAX_VALUE_DEPTH`] levels is
    /// admitted, becomes the witness, and its report reads back; one level deeper is refused
    /// by `Campaign::new`. Run on a thread of a 2 MiB stack, the size of a test thread.
    #[test]
    fn an_anchor_at_the_depth_bound_reaches_a_report_that_reads_back() {
        let nodes = crate::values::MAX_VALUE_DEPTH - 3;
        let (deeper, report) = std::thread::Builder::new()
            .stack_size(2 << 20)
            .spawn(move || {
                let deeper = deep_record_campaign(nodes + 1).map(|_| ());
                let report = deep_record_campaign(nodes)
                    .expect("an anchor at the bound is admitted")
                    .run(crate::spec::Budget::Cases(1), None);
                (deeper, report)
            })
            .expect("a thread")
            .join()
            .expect("no overflow");
        assert!(
            matches!(deeper, Err(CampaignError::AnchorDoesNotParse { .. })),
            "{deeper:?}"
        );
        let witness = report.witness().expect("the anchor reaches the target");
        assert!(matches!(witness.first.holes[0].value, Value::Apply { .. }));
        let text = report.to_canonical_json();
        assert_eq!(crate::FuzzReport::from_json(&text).ok(), Some(report));
    }

    /// The dictionary's harvest from the campaign's rule graph and resolved target equals the
    /// harvest it makes on a backend and graph of its own (DICT's request after N9), for a rule
    /// target and for a pattern target.
    #[test]
    fn the_dictionary_harvests_the_same_from_the_campaigns_graph() {
        use crate::{
            proposers::dictionary::{self, Harvest},
            target::{RuleMode, RuleRef, RuleTarget},
        };
        let compiled = COIN.compiled();
        let rule = Arc::new(CampaignSpec {
            program: ProgramInput::Source(compiled.program_source("coin/count.pgm")),
            holes: Vec::new(),
            target: Target {
                kind: TargetKind::Rule(RuleTarget {
                    rule: RuleRef::Label("count-done".to_owned()),
                    mode: RuleMode::Fired,
                }),
                run_to_completion: false,
                negated_property: false,
                data_end: true,
                comparable: false,
                query_confirmable: false,
            },
            definitions: Definitions {
                baseline: Arc::new(compiled.definition()),
                mutant: None,
            },
            ..CampaignSpec::clone(&le_spec(None))
        });
        for spec in [rule, le_spec(None)] {
            let cases = LiveCases::build(Arc::clone(&spec)).expect("the campaign builds");
            let check = GraphCheck::build(&spec, &cases).expect("a graph check");
            let target = cases.target_rule_id();
            let shared = dictionary::harvest(&spec, check.graph(), target).expect("harvests");
            let own = Harvest::for_campaign(&spec).expect("harvests");
            assert!(!own.literals().is_empty());
            assert_eq!(shared.literals(), own.literals());
            let internalized = cases.baseline_internalized().expect("source route");
            let graph = RuleGraph::new(internalized);
            let fresh = dictionary::harvest(&spec, &graph, target).expect("harvests");
            assert_eq!(fresh.literals(), own.literals());
        }
    }

    /// The `from-definition` route internalizes inside each backend's session: nothing is
    /// shared, and the graph and the confirmations build their backends from the KORE.
    #[test]
    fn a_from_definition_campaign_shares_no_internalization() {
        let spec = le_spec(Some(BackendRoute::FromDefinition));
        let cases = LiveCases::build(Arc::clone(&spec)).expect("the campaign builds");
        assert!(cases.baseline.internalized.is_none());
        assert!(GraphCheck::build(&spec, &cases).is_some());
        let cache = DefinitionCache::build(&spec, &cases).expect("the cache builds");
        assert!(cache.baseline.internalized.is_none());
        let fresh =
            LiveCases::build_with(Arc::clone(&spec), Some(&cache)).expect("a confirmation builds");
        assert!(fresh.baseline.internalized.is_none());
    }
}
