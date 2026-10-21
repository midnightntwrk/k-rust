//! Case execution over the real modules: values printed and checked ([`crate::values`]), the
//! program instantiated and assembled ([`crate::holes`], [`crate::assemble`]), executed and
//! judged ([`crate::exec`], [`crate::target`]). Owner: FZ-06.

use std::{
    fmt::Write as _,
    sync::{Arc, OnceLock},
};

use k_rust::{
    backend::{Backend, CancellationToken, HaltReasonOutput, StopCause},
    k_rust_backend::definition::BackendDefinition,
    kore::ast::Pattern as KorePattern,
};

use super::runner::{CaseRun, CaseRunner, ConfirmFailure, Cut, HitDetail};
use crate::{
    assemble::{CaseAssembler, ProgramAssembly, build_backend},
    error::{CampaignError, SortRefusal},
    exec::{
        self, Abort, CaseRequestShape, CaseResult, CompiledPattern, Executor, FailureCause,
        NormalEnd, OutcomeClass, PatternCompiler, TargetNeeds,
    },
    graph::{self, RuleGraph, entry::Entry},
    holes::{self, HoleSite, InstantiatedProgram, PrintedValue, ResolvedHoles, RoundTripCheck},
    report::{DefinitionRole, HoleValue, KillKind, Reaching, RejectionReason, WitnessSide},
    spec::{BackendRoute, CampaignSpec, CompiledDefinition, PathMode, ProgramInput},
    target::{HitSite, ResolvedTarget, TargetKind, differential},
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
    /// On the `source-execution` route, the internalized definition the backend's session holds
    /// (`Backend::select_definition`), shared, not copied: the campaign's only internalization
    /// of this definition, from which the rule graph's backend and the confirmations' backends
    /// are built by copy ([`GraphCheck::build`], [`DefinitionCache::build`]; phase-1 review N9).
    /// `None` on the `from-definition` route, whose backends internalize inside their sessions.
    internalized: Option<Arc<BackendDefinition>>,
}

/// What a side may reuse from a [`DefinitionCache`]: the internalized definition its fresh
/// backend copies, the compiled normal-termination pattern, which only needs preparing on that
/// backend, and the hole resolution and round-trip positions, which are functions of the
/// grammar, the program and the hole declarations alone.
#[derive(Clone, Copy, Default)]
struct Seed<'a> {
    internalized: Option<&'a Arc<BackendDefinition>>,
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
        let assembly = Arc::new(ProgramAssembly::new(definition)?);
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
        let (mut executor, normal_end) = if let Some(normal_end) = seed.normal_end {
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
        if let Some((holes, round_trip)) = seed.resolved {
            return Ok(Self {
                definition: Arc::clone(definition),
                assembly,
                executor,
                normal_end,
                holes: holes.clone(),
                round_trip: Arc::clone(round_trip),
                shape: CaseRequestShape::new(&spec.options, &TargetNeeds::default()),
                internalized,
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
            definition: Arc::clone(definition),
            assembly,
            executor,
            normal_end,
            holes,
            round_trip,
            shape: CaseRequestShape::new(&spec.options, &TargetNeeds::default()),
            internalized,
        })
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
        let mut printed = Vec::with_capacity(values.len());
        for (hole, value) in self.holes.holes.iter().zip(values) {
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
        let instantiated = holes::instantiate(program, &self.holes, &printed);
        let configuration = assembler
            .assemble(&instantiated)
            .map_err(|_| RejectionReason::Assembly)?;
        self.round_trip
            .check(&configuration, &printed)
            .map_err(|_| RejectionReason::RoundTrip)?;
        Ok(Prepared {
            printed,
            instantiated,
            assembled: configuration,
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
                side.prepare_checked(&mut side.assembler(), &self.spec.program, values, false)
                    .map(|prepared| prepared.assembled)
            })
            .collect()
    }

    /// The baseline's internalized definition on the `source-execution` route, the campaign's
    /// only internalization of it ([`Side::internalized`]); `None` on the `from-definition`
    /// route.
    pub(crate) fn baseline_internalized(&self) -> Option<&Arc<BackendDefinition>> {
        self.baseline.internalized.as_ref()
    }

    /// The catalog id of a rule target's rule, as the target resolved it; `None` for every
    /// other target kind.
    pub(crate) fn target_rule_id(&self) -> Option<&str> {
        match &self.judge {
            Judge::Target(target) => target.rule_id(),
            Judge::Differential(_) => None,
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
        // also walks its observer over the observed run (FZ-10).
        let judged =
            target.run_and_judge(&mut side.executor, &prepared.assembled, &side.shape, cancel)?;
        let (result, hit_step, judged) = (judged.result, judged.hit_step, judged.judgement);
        let mut run = run_of(&result, &[&result]);
        run.cut = cut_of(&result);
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
                                // An observer hit's step on the hit leaf's path (ARCHITECTURE
                                // 9.2); the leaf runs on to its end, at depth `steps`.
                                step: hit_step,
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
                run.cut = cut_of(if judgement.class == OutcomeClass::BaselineIncomplete {
                    &baseline
                } else {
                    &mutated
                });
                if judgement.class == OutcomeClass::Hit {
                    // An added end: the killing mutant leaf. A removed end (all-paths mode): the
                    // baseline end the mutant cannot reach. Both sides list every leaf.
                    let witness = judgement.witness().and_then(|(kind, index)| {
                        let (role, side) = match kind {
                            KillKind::AddedEnd => (DefinitionRole::Mutant, &mutated),
                            KillKind::RemovedEnd => (DefinitionRole::Baseline, &baseline),
                        };
                        side.leaves.get(index).map(|leaf| (kind, role, index, leaf))
                    });
                    if let Some((kind, role, index, leaf)) = witness {
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
                                step: None,
                            },
                            kill: Some(kind),
                            steps: Some(leaf.depth),
                            reaching_state: leaf.state.to_string(),
                            krun_command: None,
                        });
                    } else {
                        run.class = OutcomeClass::Unsupported;
                        run.defects
                            .push("a kill names no leaf of either result".to_owned());
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
        warnings: Vec::new(),
        hit: None,
        cut: Cut::default(),
    }
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

    fn of(side: Side) -> Self {
        Self {
            internalized: side.internalized,
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
        let baseline = cases.baseline.internalized.clone();
        let mutant = match &cases.judge {
            Judge::Differential(mutant) => mutant.internalized.clone(),
            Judge::Target(_) => None,
        };
        let side = |definition, role, internalized: &Option<Arc<BackendDefinition>>| {
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
    /// The assemblers of [`Self::cases`]' sides, built from its [`LiveCases::assembly_parts`].
    pub(crate) assemblers: RunAssemblers<'a>,
    pub(crate) cache: Arc<OnceLock<Result<DefinitionCache, String>>>,
    /// The campaign's rule-graph self-check, run on every case's coverage.
    pub(crate) graph: Option<Arc<GraphCheck>>,
}

impl CaseRunner for LiveRunner<'_> {
    fn run_case(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, Abort> {
        let mut run = run_live(&mut self.cases, &mut self.assemblers, values, cancel)?;
        self.self_check(&mut run);
        Ok(run)
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
        let mut fresh = LiveCases::build_with(spec, Some(cache)).map_err(|error| {
            ConfirmFailure::Failed(format!(
                "the fresh backend or assembly did not build: {error}"
            ))
        })?;
        let parts = fresh.assembly_parts();
        let mut assemblers = parts.assemblers();
        let mut run =
            run_live(&mut fresh, &mut assemblers, values, cancel).map_err(ConfirmFailure::Abort)?;
        self.self_check(&mut run);
        Ok(run)
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

impl LiveRunner<'_> {
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

    /// The dictionary's harvest from the campaign's rule graph and resolved target equals the
    /// harvest it makes on a backend and graph of its own (DICT's request after N9), for a rule
    /// target and for a pattern target.
    #[test]
    fn the_dictionary_harvests_the_same_from_the_campaigns_graph() {
        use crate::{
            proposers::dictionary::{Harvest, RADIUS},
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
            let shared = Harvest::from_graph(check.graph(), cases.target_rule_id(), RADIUS);
            let own = Harvest::for_campaign(&spec).expect("harvests");
            assert!(!own.literals().is_empty());
            assert_eq!(shared.literals(), own.literals());
            let internalized = cases.baseline_internalized().expect("source route");
            let graph = RuleGraph::new(internalized);
            let fresh = Harvest::from_graph(&graph, cases.target_rule_id(), RADIUS);
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
