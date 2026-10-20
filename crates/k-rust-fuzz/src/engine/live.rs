//! Case execution over the real modules: values printed and checked ([`crate::values`]), the
//! program instantiated and assembled ([`crate::holes`], [`crate::assemble`]), executed and
//! judged ([`crate::exec`], [`crate::target`]). Owner: FZ-06.

use std::{
    fmt::Write as _,
    sync::{Arc, OnceLock},
};

use k_rust::{
    backend::{Backend, CancellationToken},
    k_rust_backend::definition::BackendDefinition,
    kore::ast::Pattern as KorePattern,
};

use super::runner::{CaseRun, CaseRunner, HitDetail};
use crate::{
    assemble::{ProgramAssembly, build_backend},
    error::{CampaignError, SortRefusal},
    exec::{
        self, Abort, CaseRequestShape, CaseResult, CompiledPattern, Executor, NormalEnd,
        OutcomeClass, PatternCompiler, TargetNeeds,
    },
    graph::{self, RuleGraph, entry::Entry},
    holes::{self, InstantiatedProgram, PrintedValue, ResolvedHoles, RoundTripCheck},
    report::{DefinitionRole, HoleValue, KillKind, Reaching, RejectionReason, WitnessSide},
    spec::{BackendRoute, CampaignSpec, CompiledDefinition, PathMode, ProgramInput},
    target::{HitSite, ResolvedTarget, TargetKind, differential},
    values::{self, Value, print},
};

/// One definition's half of case execution: its assembly, executor, holes and round-trip check.
pub(crate) struct Side {
    role: DefinitionRole,
    definition: Arc<CompiledDefinition>,
    assembly: ProgramAssembly,
    executor: Executor,
    /// The normal-termination pattern, compiled once for this definition and prepared on the
    /// executor's backend.
    normal_end: NormalEnd,
    pub(crate) holes: ResolvedHoles,
    round_trip: Arc<RoundTripCheck>,
    shape: CaseRequestShape,
}

/// What a side may reuse from a [`DefinitionCache`]: the internalized definition its fresh
/// backend copies, the compiled normal-termination pattern, which only needs preparing on that
/// backend, and the hole resolution and round-trip positions, which are functions of the
/// grammar, the program and the hole declarations alone.
#[derive(Clone, Copy, Default)]
struct Seed<'a> {
    internalized: Option<&'a BackendDefinition>,
    normal_end: Option<&'a NormalEnd>,
    resolved: Option<(&'a ResolvedHoles, &'a Arc<RoundTripCheck>)>,
}

impl Side {
    fn build(
        spec: &CampaignSpec,
        definition: &Arc<CompiledDefinition>,
        role: DefinitionRole,
        seed: Seed<'_>,
    ) -> Result<Self, CampaignError> {
        let assembly = ProgramAssembly::new(definition)?;
        let backend = match seed.internalized {
            // A fresh backend over a copy of the cached, immutable internalized definition.
            Some(internalized) => {
                Backend::from_internalized(internalized.clone(), spec.options.backend.options())
                    .map_err(CampaignError::from)?
            }
            None => build_backend(definition, spec.options.backend.options())?,
        };
        let (mut executor, normal_end) = match seed.normal_end {
            Some(normal_end) => (
                Executor::with_normal_end(backend, normal_end, &spec.options)?,
                normal_end.clone(),
            ),
            None => {
                let compiler = PatternCompiler::new(definition)?;
                let normal_end = compiler.normal_end(assembly.grammar(), &spec.options)?;
                let executor = Executor::with_normal_end(backend, &normal_end, &spec.options)?
                    .with_compiler(compiler);
                (executor, normal_end)
            }
        };
        if let Some((holes, round_trip)) = seed.resolved {
            return Ok(Self {
                role,
                definition: Arc::clone(definition),
                assembly,
                executor,
                normal_end,
                holes: holes.clone(),
                round_trip: Arc::clone(round_trip),
                shape: CaseRequestShape::new(&spec.options, &TargetNeeds::default()),
            });
        }
        let holes = executor
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
        Ok(Self {
            role,
            definition: Arc::clone(definition),
            assembly,
            executor,
            normal_end,
            holes,
            round_trip,
            shape: CaseRequestShape::new(&spec.options, &TargetNeeds::default()),
        })
    }

    /// Print, instantiate, assemble and round-trip-check `values`; the rejection reason when a
    /// step refuses them.
    fn prepare(
        &self,
        program: &ProgramInput,
        values: &[Value],
    ) -> Result<Prepared, RejectionReason> {
        self.prepare_checked(program, values, true)
    }

    /// [`Self::prepare`], with the constraint check optional: an anchor may lie outside its
    /// hole's constraints, which narrow what is generated, and still identify the grammar.
    fn prepare_checked(
        &self,
        program: &ProgramInput,
        values: &[Value],
        check_constraints: bool,
    ) -> Result<Prepared, RejectionReason> {
        let mut printed = Vec::with_capacity(values.len());
        for (hole, value) in self.holes.holes.iter().zip(values) {
            if check_constraints {
                values::check_constraints(value, &hole.sort, &hole.decl.constraints)
                    .map_err(|_| RejectionReason::Constraint)?;
            }
            let k_text =
                print::print_k_text(value, &hole.sort).map_err(|_| RejectionReason::Print)?;
            let kore = print::to_kore(value, &hole.sort).map_err(|_| RejectionReason::Print)?;
            printed.push(PrintedValue { k_text, kore });
        }
        let instantiated = holes::instantiate(program, &self.holes, &printed);
        let assembled = self
            .assembly
            .assemble(&self.definition, &instantiated)
            .map_err(|_| RejectionReason::Assembly)?;
        self.round_trip
            .check(&assembled, &printed)
            .map_err(|_| RejectionReason::RoundTrip)?;
        Ok(Prepared {
            printed,
            instantiated,
            assembled,
        })
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

/// The campaign's case execution: one baseline [`Side`] and the judge.
pub(crate) struct LiveCases {
    spec: Arc<CampaignSpec>,
    pub(crate) baseline: Side,
    judge: Judge,
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
        let mut baseline = Side::build(
            &spec,
            &spec.definitions.baseline,
            DefinitionRole::Baseline,
            cache.map(|cache| cache.baseline.seed()).unwrap_or_default(),
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
                cache
                    .and_then(|cache| cache.mutant.as_ref())
                    .map(SideCache::seed)
                    .unwrap_or_default(),
            )?;
            baseline.shape = CaseRequestShape::new(&spec.options, &plan.baseline);
            mutant.shape = CaseRequestShape::new(&spec.options, &plan.mutant);
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
        })
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
                side.prepare_checked(&self.spec.program, values, false)
                    .map(|prepared| prepared.assembled)
            })
            .collect()
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

    /// The `krun` command line equivalent to a case of this campaign, or `None` when no `krun`
    /// run is: a differential pair, the `from-definition` route, a KORE template, or a program
    /// without `$PGM` (krun would read `$PGM` from its standard input).
    fn krun_command(&self, instantiated: &InstantiatedProgram) -> Option<String> {
        let Judge::Target(target) = &self.judge else {
            return None;
        };
        let definition = &self.spec.definitions.baseline;
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
        let options = &self.spec.options;
        let mut line = format!(
            "krust krun --definition <definition-dir> -m {} --syntax-module {}",
            quote(&definition.main_module),
            quote(&definition.syntax_module)
        );
        write!(line, " -s {}", quote(&program.start_sort)).expect("writing to a String");
        line.push_str(" --io off --strategy ");
        line.push_str(match options.paths {
            PathMode::OnePath => "any",
            PathMode::AllPaths => "all",
        });
        if let Some(depth) = options.max_depth {
            write!(line, " --depth {depth}").expect("writing to a String");
        }
        // A `fired` target under one path stops at its rule (FZ-05, D16); so must krun.
        for rule in target.needs(options.paths).terminal_rules {
            write!(line, " --terminal-rule {}", quote(&rule)).expect("writing to a String");
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
        if let Some(work) = options.effective_max_work() {
            write!(
                line,
                "  # the campaign also bounds max-work {work}, which krun cannot"
            )
            .expect("writing to a String");
        }
        Some(line)
    }

    fn run_target(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, Abort> {
        let prepared = match self.baseline.prepare(&self.spec.program, values) {
            Ok(prepared) => prepared,
            Err(reason) => return Ok(CaseRun::rejected(reason, 0)),
        };
        let Judge::Target(target) = &self.judge else {
            unreachable!("run_target is called for rule and pattern targets")
        };
        let side = &mut self.baseline;
        // `run_and_judge` is `run` then `judge` for rule and pattern targets; an observer target
        // also walks its observer over the observed run (FZ-10).
        let (result, judged) =
            target.run_and_judge(&mut side.executor, &prepared.assembled, &side.shape, cancel)?;
        let mut run = run_of(&result, &[&result]);
        match judged {
            Ok(judgement) => {
                run.class = judgement.class;
                run.blocked = judgement.blocked;
                if judgement.class == OutcomeClass::Hit {
                    // A leaf hit names its leaf; a hit of the whole run (D16) names none, and
                    // rests on every leaf's configuration.
                    let reached = match judgement.hit_site {
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
                            },
                            kill: None,
                            steps,
                            reaching_state,
                            krun_command: self.krun_command(&prepared.instantiated),
                        });
                    } else {
                        run.class = OutcomeClass::Unsupported;
                        run.defects
                            .push("a hit names no leaf of the result".to_owned());
                    }
                }
            }
            Err(defect) => {
                run.class = OutcomeClass::Unsupported;
                run.defects.push(defect.description);
            }
        }
        if run.class == OutcomeClass::Rejected {
            run.rejection = Some(RejectionReason::BackendRefused);
        }
        Ok(run)
    }

    fn run_differential(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, Abort> {
        let Judge::Differential(mutant) = &mut self.judge else {
            unreachable!("run_differential is called for differential targets")
        };
        let baseline_case = match self.baseline.prepare(&self.spec.program, values) {
            Ok(prepared) => prepared,
            Err(reason) => return Ok(CaseRun::rejected(reason, 0)),
        };
        let mutant_case = match mutant.prepare(&self.spec.program, values) {
            Ok(prepared) => prepared,
            Err(reason) => return Ok(CaseRun::rejected(reason, 0)),
        };
        let side = &mut self.baseline;
        let baseline = side
            .executor
            .run(&baseline_case.assembled, &side.shape, &[], cancel)?;
        let mutated = mutant
            .executor
            .run(&mutant_case.assembled, &mutant.shape, &[], cancel)?;
        let mut run = run_of(&mutated, &[&baseline, &mutated]);
        // A value either side's backend refuses makes the case `rejected` (ARCHITECTURE 4.3,
        // 5.3), before the pair is judged: a refused baseline is not an incomplete one.
        if refused(&baseline) || refused(&mutated) {
            run.class = OutcomeClass::Rejected;
            run.rejection = Some(RejectionReason::BackendRefused);
            return Ok(run);
        }
        match differential::judge_pair(
            &baseline,
            &mutated,
            self.spec.options.paths,
            self.spec.target.run_to_completion,
        ) {
            Ok(judgement) => {
                run.class = judgement.class;
                if judgement.class == OutcomeClass::Hit {
                    // An added end: the killing mutant leaf. A removed end (all-paths mode): the
                    // baseline end the mutant cannot reach. Both sides list every leaf.
                    let witness = match (judgement.killing_leaf, judgement.removed_end) {
                        (Some(index), _) => mutated
                            .leaves
                            .get(index)
                            .map(|leaf| (KillKind::AddedEnd, DefinitionRole::Mutant, index, leaf)),
                        (None, Some(index)) => baseline.leaves.get(index).map(|leaf| {
                            (KillKind::RemovedEnd, DefinitionRole::Baseline, index, leaf)
                        }),
                        (None, None) => None,
                    };
                    match witness {
                        Some((kind, role, index, leaf)) => {
                            let holes = self.hole_values(values, &baseline_case.printed);
                            run.hit = Some(HitDetail {
                                holes,
                                sides: vec![
                                    side_of(DefinitionRole::Baseline, &baseline_case, &baseline),
                                    side_of(DefinitionRole::Mutant, &mutant_case, &mutated),
                                ],
                                reaching: Reaching {
                                    role,
                                    leaf: Some(index_u64(index)),
                                },
                                kill: Some(kind),
                                steps: Some(leaf.depth),
                                reaching_state: leaf.state.to_string(),
                                krun_command: None,
                            });
                        }
                        None => {
                            run.class = OutcomeClass::Unsupported;
                            run.defects
                                .push("a kill names no leaf of either result".to_owned());
                        }
                    }
                }
            }
            Err(defect) => {
                run.class = OutcomeClass::Unsupported;
                run.defects.push(defect.description);
            }
        }
        if run.class == OutcomeClass::Rejected {
            run.rejection = Some(RejectionReason::BackendRefused);
        }
        Ok(run)
    }
}

/// The run-level parts of a [`CaseRun`]: coverage from `covered`, work and determinism and load
/// records from every side.
fn run_of(covered: &CaseResult, sides: &[&CaseResult]) -> CaseRun {
    let (applied, matched) = covered
        .coverage
        .as_ref()
        .map_or_else(Default::default, |coverage| {
            (coverage.applied.clone(), coverage.matched.clone())
        });
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
        blocked: false,
        outside_determinism: sides
            .iter()
            .any(|side| !side.determinism_breaks().is_empty()),
        rejection: None,
        load_records,
        defects: Vec::new(),
        hit: None,
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

fn side_of(role: DefinitionRole, prepared: &Prepared, result: &CaseResult) -> WitnessSide {
    WitnessSide {
        role,
        initial_configuration: prepared.assembled.to_string(),
        final_configurations: result
            .leaves
            .iter()
            .map(|leaf| leaf.state.to_string())
            .collect(),
    }
}

/// `text` quoted for a POSIX shell.
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
    internalized: Option<BackendDefinition>,
    normal_end: NormalEnd,
    holes: ResolvedHoles,
    round_trip: Arc<RoundTripCheck>,
}

impl SideCache {
    fn seed(&self) -> Seed<'_> {
        Seed {
            internalized: self.internalized.as_ref(),
            normal_end: Some(&self.normal_end),
            resolved: Some((&self.holes, &self.round_trip)),
        }
    }

    fn of(side: Side, internalized: Option<BackendDefinition>) -> Self {
        Self {
            internalized,
            normal_end: side.normal_end,
            holes: side.holes,
            round_trip: side.round_trip,
        }
    }
}

impl DefinitionCache {
    /// Internalize every `source-execution` definition of `spec` once, then, on a build of its
    /// own (not the campaign's), compile the normal-termination pattern and the target's
    /// patterns, resolve the holes and locate their positions once.
    ///
    /// # Errors
    ///
    /// The first refusal, as a [`CampaignError`].
    pub(crate) fn build(spec: &Arc<CampaignSpec>) -> Result<Self, CampaignError> {
        let internalize = |definition: &CompiledDefinition| match &definition.route {
            BackendRoute::SourceExecution {
                execution_rewrite_order,
            } => Backend::internalize_source_definition(
                &definition.kore,
                &definition.main_module,
                execution_rewrite_order,
            )
            .map(Some)
            .map_err(CampaignError::from),
            BackendRoute::FromDefinition => Ok(None),
        };
        let baseline = internalize(&spec.definitions.baseline)?;
        let mutant = match &spec.definitions.mutant {
            Some(mutant) => internalize(mutant)?,
            None => None,
        };
        let side = |definition, role, internalized: &Option<BackendDefinition>| {
            Side::build(
                spec,
                definition,
                role,
                Seed {
                    internalized: internalized.as_ref(),
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
        let baseline = SideCache::of(baseline_side, baseline);
        let mutant = match &spec.definitions.mutant {
            Some(definition) => Some(SideCache::of(
                side(definition, DefinitionRole::Mutant, &mutant)?,
                mutant,
            )),
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
/// graph's own backend, which no case uses, so that its solver cache is no case's.
///
/// The graph's warnings go into the report, and every case's coverage `applied` is checked
/// against the entry: a rule applied outside the graph, or an id the definition does not know,
/// is an engine defect noted on the case ([`RuleGraph::unreachable_applied`]). Differential
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
        let mut backend =
            build_backend(&spec.definitions.baseline, spec.options.backend.options()).ok()?;
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

    /// The warnings the report carries for this campaign.
    pub(crate) fn warnings(&self) -> &[String] {
        &self.warnings
    }

    /// The engine defects of one case whose coverage `applied` holds `applied`: one description
    /// per applied rule the graph cannot reach from the entry and per unknown id
    /// ([`graph::entry::AppliedCheck::defects`]). Ambiguous ids (shared by a rule and an
    /// equation) are not defects and are not reported per case.
    pub(crate) fn defects(&self, applied: &[String]) -> Vec<String> {
        match self
            .graph
            .unreachable_applied(&self.entry, applied.iter().map(String::as_str))
        {
            Ok(check) => check.defects(),
            Err(foreign) => vec![foreign.to_string()],
        }
    }
}

/// The campaign's runner: the campaign's own [`LiveCases`] for cases, a fresh one per
/// confirmation, built from the campaign's [`DefinitionCache`] (filled on the first
/// confirmation).
pub(crate) struct LiveRunner {
    pub(crate) cases: LiveCases,
    pub(crate) cache: Arc<OnceLock<Result<DefinitionCache, String>>>,
    /// The campaign's rule-graph self-check, run on every case's coverage.
    pub(crate) graph: Option<Arc<GraphCheck>>,
}

impl CaseRunner for LiveRunner {
    fn run_case(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, Abort> {
        let mut run = run_live(&mut self.cases, values, cancel)?;
        if let Some(graph) = &self.graph
            && run.class != OutcomeClass::Rejected
        {
            run.defects.extend(graph.defects(&run.applied));
        }
        Ok(run)
    }

    /// A fresh `Backend` (fresh solver, fresh session) over a copy of the cached internalized
    /// definition, with a fresh assembly, fresh hole resolution and a freshly resolved target.
    fn confirm(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, String> {
        let spec = Arc::clone(&self.cases.spec);
        let cache = self
            .cache
            .get_or_init(|| DefinitionCache::build(&spec).map_err(|error| error.to_string()))
            .as_ref()
            .map_err(|error| format!("the definition did not internalize: {error}"))?;
        let mut fresh = LiveCases::build_with(spec, Some(cache))
            .map_err(|error| format!("the fresh backend or assembly did not build: {error}"))?;
        run_live(&mut fresh, values, cancel).map_err(|abort| abort.reason)
    }

    fn admissible(&self, hole: usize, value: &Value) -> bool {
        self.cases
            .baseline
            .holes
            .holes
            .get(hole)
            .is_some_and(|hole| {
                values::check_constraints(value, &hole.sort, &hole.decl.constraints).is_ok()
            })
    }
}

fn run_live(
    cases: &mut LiveCases,
    values: &[Value],
    cancel: Option<&CancellationToken>,
) -> Result<CaseRun, Abort> {
    if matches!(cases.judge, Judge::Differential(_)) {
        cases.run_differential(values, cancel)
    } else {
        cases.run_target(values, cancel)
    }
}
