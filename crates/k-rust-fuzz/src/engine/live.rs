//! Case execution over the real modules: values printed and checked ([`crate::values`]), the
//! program instantiated and assembled ([`crate::holes`], [`crate::assemble`]), executed and
//! judged ([`crate::exec`], [`crate::target`]). Owner: FZ-06.

use std::{fmt::Write as _, sync::Arc};

use k_rust::{backend::CancellationToken, kore::ast::Pattern as KorePattern};

use super::runner::{CaseRun, CaseRunner, HitDetail};
use crate::{
    assemble::ProgramAssembly,
    error::{CampaignError, SortRefusal},
    exec::{Abort, CaseRequestShape, CaseResult, Executor, OutcomeClass, TargetNeeds},
    holes::{self, InstantiatedProgram, PrintedValue, ResolvedHoles, RoundTripCheck},
    report::{DefinitionRole, HoleValue, RejectionReason, WitnessSide},
    spec::{BackendRoute, CampaignSpec, CompiledDefinition, PathMode, ProgramInput},
    target::{ResolvedTarget, TargetKind, differential},
    values::{self, Value, print},
};

/// One definition's half of case execution: its assembly, executor, holes and round-trip check.
pub(crate) struct Side {
    role: DefinitionRole,
    definition: Arc<CompiledDefinition>,
    assembly: ProgramAssembly,
    executor: Executor,
    pub(crate) holes: ResolvedHoles,
    round_trip: RoundTripCheck,
    shape: CaseRequestShape,
}

impl Side {
    fn build(
        spec: &CampaignSpec,
        definition: &Arc<CompiledDefinition>,
        role: DefinitionRole,
    ) -> Result<Self, CampaignError> {
        let assembly = ProgramAssembly::new(definition)?;
        let mut executor = Executor::new(definition, &assembly, &spec.options)?;
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
        let round_trip = RoundTripCheck::new(&assembly, definition, &spec.program, &holes)?;
        Ok(Self {
            role,
            definition: Arc::clone(definition),
            assembly,
            executor,
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
        let mut printed = Vec::with_capacity(values.len());
        for (hole, value) in self.holes.holes.iter().zip(values) {
            values::check_constraints(value, &hole.sort, &hole.decl.constraints)
                .map_err(|_| RejectionReason::Constraint)?;
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
        let mut baseline =
            Side::build(&spec, &spec.definitions.baseline, DefinitionRole::Baseline)?;
        let judge = if let TargetKind::Differential(_) = spec.target.kind {
            let mutant_definition = spec
                .definitions
                .mutant
                .as_ref()
                .ok_or(CampaignError::DefinitionsMismatch)?;
            let plan = differential::plan(&spec.options);
            let mut mutant = Side::build(&spec, mutant_definition, DefinitionRole::Mutant)?;
            baseline.shape = CaseRequestShape::new(&spec.options, &plan.baseline);
            mutant.shape = CaseRequestShape::new(&spec.options, &plan.mutant);
            Judge::Differential(Box::new(mutant))
        } else {
            let target = ResolvedTarget::resolve(
                &spec.target,
                &mut baseline.executor,
                &spec.definitions.baseline,
                &baseline.assembly,
            )?;
            baseline.shape = CaseRequestShape::new(&spec.options, &target.needs());
            Judge::Target(target)
        };
        Ok(Self {
            spec,
            baseline,
            judge,
        })
    }

    /// The baseline configuration with every hole at its anchor, when every hole has one.
    pub(crate) fn anchor_configuration(&self) -> Option<Result<KorePattern, RejectionReason>> {
        let anchors: Option<Vec<Value>> = self
            .baseline
            .holes
            .holes
            .iter()
            .map(|hole| hole.anchor.clone())
            .collect();
        anchors.map(|values| {
            self.baseline
                .prepare(&self.spec.program, &values)
                .map(|prepared| prepared.assembled)
        })
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

    fn krun_command(&self, instantiated: &InstantiatedProgram) -> Option<String> {
        if matches!(self.judge, Judge::Differential(_)) {
            return None;
        }
        let definition = &self.spec.definitions.baseline;
        if definition.route == BackendRoute::FromDefinition {
            return None;
        }
        let InstantiatedProgram::Source {
            program,
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
        if let Some(program) = program {
            write!(line, " -s {}", quote(&program.start_sort)).expect("writing to a String");
        }
        line.push_str(" --io off --strategy ");
        line.push_str(match options.paths {
            PathMode::OnePath => "any",
            PathMode::AllPaths => "all",
        });
        if let Some(depth) = options.max_depth {
            write!(line, " --depth {depth}").expect("writing to a String");
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
        if let Some(program) = program {
            write!(line, " -e {}", quote(&program.text)).expect("writing to a String");
        }
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
        let result =
            side.executor
                .run(&prepared.assembled, &side.shape, &target.matchers(), cancel)?;
        let mut run = run_of(&result, &[&result]);
        match target.judge(&result) {
            Ok(judgement) => {
                run.class = judgement.class;
                run.blocked = judgement.blocked;
                if judgement.class == OutcomeClass::Hit {
                    let leaf = judgement
                        .hit_leaf
                        .and_then(|index| result.leaves.get(index));
                    match leaf {
                        Some(leaf) => {
                            run.hit = Some(HitDetail {
                                holes: self.hole_values(values, &prepared.printed),
                                sides: vec![side_of(DefinitionRole::Baseline, &prepared, &result)],
                                steps: leaf.depth,
                                reaching_state: leaf.state.to_string(),
                                krun_command: self.krun_command(&prepared.instantiated),
                            });
                        }
                        None => {
                            run.class = OutcomeClass::Unsupported;
                            run.defects
                                .push("a hit names no leaf of the result".to_owned());
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
        match differential::judge_pair(
            &baseline,
            &mutated,
            self.spec.options.paths,
            self.spec.target.run_to_completion,
        ) {
            Ok(judgement) => {
                run.class = judgement.class;
                if judgement.class == OutcomeClass::Hit {
                    match judgement
                        .killing_leaf
                        .and_then(|index| mutated.leaves.get(index))
                    {
                        Some(leaf) => {
                            let holes = self.hole_values(values, &baseline_case.printed);
                            run.hit = Some(HitDetail {
                                holes,
                                sides: vec![
                                    side_of(DefinitionRole::Baseline, &baseline_case, &baseline),
                                    side_of(DefinitionRole::Mutant, &mutant_case, &mutated),
                                ],
                                steps: leaf.depth,
                                reaching_state: leaf.state.to_string(),
                                krun_command: None,
                            });
                        }
                        None => {
                            run.class = OutcomeClass::Unsupported;
                            run.defects
                                .push("a kill names no leaf of the mutant's result".to_owned());
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

/// The campaign's runner: the campaign's own [`LiveCases`] for cases, a fresh one per
/// confirmation.
pub(crate) struct LiveRunner {
    pub(crate) cases: LiveCases,
}

impl CaseRunner for LiveRunner {
    fn run_case(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, Abort> {
        run_live(&mut self.cases, values, cancel)
    }

    fn confirm(
        &mut self,
        values: &[Value],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, String> {
        let mut fresh = LiveCases::build(Arc::clone(&self.cases.spec))
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
