use crate::{
    CollectorPlan, DefinitionRequest, DiagnosticEnvelope, DiagnosticStage, FacetSelector,
    GenerationError, KrsCfg, PlanningError, RegistrationMode, diagnostic_envelope,
    metadata::cargo_metadata,
};
use krs_collector::{CollectionError, FacadeAliases};
use krs_compiler::{
    DEFINITION_ARTIFACT, DEFINITION_IR_ARTIFACT, DESCRIPTOR_ARTIFACT, DescriptorLoweringError,
    EmitError, LoweringError, ReferenceExpansionError, SEMANTIC_ARTIFACT, SOURCES_ARTIFACT,
    SPEC_ARTIFACT, SYMBOLS_ARTIFACT, emit_k, expand_package_reference_source,
    lower_descriptor_bundle, lower_semantic_theory,
};
use krs_diagnostic::{Diagnostic, ToDiagnostic};
use krs_ir::measure::Timings;
use krs_ir::measure::{Counters, Measurement};
use krs_ir::{DescriptorBundle, PackageId};
use krs_k_rust::{
    Backend, CompiledArtifacts, ConfigurationContext, DefinitionCompileError,
    FRONTEND_CAPABILITIES, Route,
};
use std::borrow::Cow;
use std::error::Error;
use std::ffi::OsStr;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

mod agreement;
mod collector;
mod counters;
mod exec;
mod output;
mod result_cache;
mod stage_cache;
use collector::{
    build_collector_measured, discover_runtime, generate_collector, run_collector,
    rustc_host_target,
};
use counters::{count_bundle, count_definition};
use output::{prepare_output, write_output};
use result_cache::ResultCache;
use stage_cache::StageCache;

/// Category of a production KRS command.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CommandKind {
    /// Check Rust and the complete selected KRS theory.
    Check,
    /// Print the deterministic layer-2 Rust reference surface.
    Expand,
    /// Emit the complete canonical source projection and shared sidecars.
    EmitK,
    /// Compile the same Definition IR through the native frontend.
    Build,
    /// Parse program text with the definition's program grammar.
    Parse,
    /// Run a program on one path, as krun does.
    Run,
    /// Return the set of reachable states, as `krun --search` does.
    Search,
    /// Prove the definition's claims, as kprove does.
    Prove,
}

impl CommandKind {
    /// The command-line spelling, as recorded in measurement documents.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Check => "check",
            Self::Expand => "expand",
            Self::EmitK => "emit-k",
            Self::Build => "build",
            Self::Parse => "parse",
            Self::Run => "run",
            Self::Search => "search",
            Self::Prove => "prove",
        }
    }

    /// Whether a successful result is stored and restored by the result cache.
    /// Runs and their relatives are never cached (they reuse only the compiled stage).
    #[must_use]
    pub const fn reuses_results(self) -> bool {
        matches!(self, Self::Check | Self::EmitK | Self::Build)
    }
}

/// A production command with its command-specific inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Command {
    /// Check Rust and the selected KRS theory as every command that compiles it would.
    Check {
        /// The one native backend dialect to judge (`--backend`); every native route when absent.
        backend: Option<Backend>,
        /// Print each package's program-syntax partition instead of the summary.
        partition: bool,
    },
    /// Print the deterministic layer-2 Rust reference surface.
    Expand,
    /// Emit the canonical source projection and shared sidecars.
    EmitK {
        /// Artifact directory to populate.
        output: PathBuf,
    },
    /// Compile Definition IR with a native backend dialect into an artifact directory.
    Build {
        /// Native backend dialect to compile.
        backend: Backend,
        /// Artifact directory to populate.
        output: PathBuf,
    },
    /// Parse program text (`krs parse`).
    Parse(ParseRequest),
    /// Run a program (`krs run`).
    Run(RunRequest),
    /// Search a program's reachable states (`krs search`).
    Search(SearchRequest),
    /// Prove claims (`krs prove`).
    Prove(ProveRequest),
}

pub use exec::{
    ColorChoice, ParseRequest, ProgramSource, ProveRequest, RunRequest, SearchRequest, TermOutput,
};

impl Command {
    /// Return the command category recorded in measurements and cache file names.
    #[must_use]
    pub const fn kind(&self) -> CommandKind {
        match self {
            Self::Check { .. } => CommandKind::Check,
            Self::Expand => CommandKind::Expand,
            Self::EmitK { .. } => CommandKind::EmitK,
            Self::Build { .. } => CommandKind::Build,
            Self::Parse(_) => CommandKind::Parse,
            Self::Run(_) => CommandKind::Run,
            Self::Search(_) => CommandKind::Search,
            Self::Prove(_) => CommandKind::Prove,
        }
    }

    /// The native backend dialect, for the commands that check or compile one.
    #[must_use]
    pub const fn backend(&self) -> Option<Backend> {
        match self {
            Self::Check { backend, .. } => *backend,
            Self::Build { backend, .. } => Some(*backend),
            Self::Expand
            | Self::EmitK { .. }
            | Self::Parse(_)
            | Self::Run(_)
            | Self::Search(_)
            | Self::Prove(_) => None,
        }
    }

    /// Whether a `check` prints the program-syntax partition (`--partition`).
    #[must_use]
    pub const fn partition(&self) -> bool {
        matches!(
            self,
            Self::Check {
                partition: true,
                ..
            }
        )
    }

    /// The artifact directory, for the commands that write one.
    #[must_use]
    pub fn output(&self) -> Option<&Path> {
        match self {
            Self::EmitK { output } | Self::Build { output, .. } => Some(output),
            Self::Check { .. }
            | Self::Expand
            | Self::Parse(_)
            | Self::Run(_)
            | Self::Search(_)
            | Self::Prove(_) => None,
        }
    }
}

/// Diagnostic presentation selected by the command-line caller.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum MessageFormat {
    /// Render annotated source snippets for people.
    #[default]
    Human,
    /// Preserve schema-1 envelope lines and unlocated prose.
    Json,
}

/// Explicit input to one production command execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandRequest {
    /// Command to execute.
    pub command: Command,
    /// Cargo manifest used for metadata and collector planning.
    pub manifest_path: PathBuf,
    /// Selected root definition facet.
    pub root: FacetSelector,
    /// Explicitly composed dependency facets.
    pub dependencies: Vec<FacetSelector>,
    /// KRS-owned rustc cfg values.
    pub cfg: Vec<KrsCfg>,
    /// Descriptor registration mechanism of the generated collector.
    ///
    /// [`RegistrationMode::Explicit`] is build and parity tooling; authored
    /// packages use the default.
    pub registration: RegistrationMode,
    /// Force the full pipeline even when an unchanged result is available.
    pub no_reuse: bool,
    /// Presentation of diagnostics; execution and artifact caching are independent of it.
    pub message_format: MessageFormat,
    /// `krs --profile`: overrides every package's raw K `profile` metadata.
    pub profile: Option<krs_ir::RawKProfile>,
}

/// Stable command stdout and success diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandOutcome {
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    exit_code: i32,
    warnings: crate::DiagnosticReports,
}

impl CommandOutcome {
    /// Native warnings reported after successful execution, including cache restoration.
    #[must_use]
    pub const fn warnings(&self) -> &crate::DiagnosticReports {
        &self.warnings
    }

    /// Bytes to write to stdout after successful execution.
    #[must_use]
    pub fn stdout(&self) -> &[u8] {
        &self.stdout
    }

    /// Status and trace lines to write to stderr after the diagnostics.
    #[must_use]
    pub fn stderr(&self) -> &[u8] {
        &self.stderr
    }

    /// The process exit status: 0 for a completed result, 1 for an inconclusive one.
    #[must_use]
    pub const fn exit_code(&self) -> i32 {
        self.exit_code
    }
}

struct PreparedDefinition {
    /// Allowed quoted hooks and `raw_k!` sentences, and functions only Z3
    /// can evaluate (`smt_hook` without equations), reported on every command.
    raw_k_warnings: Vec<krs_diagnostic::Diagnostic>,
    /// `k::is!` and `k::project!` terms that test nothing, and optional or
    /// collection cells K starts present without `initial`, reported on every
    /// build.
    sort_test_warnings: Vec<krs_diagnostic::Diagnostic>,
    bundle: DescriptorBundle,
    semantic: krs_ir_levels::SemanticTheory,
    lowered: krs_compiler::LoweredDefinition,
    /// k-rust's compiles of `lowered`, kept only for the agreement test.
    compiles: agreement::CompileMemo,
}

type OutputArtifact = (String, Vec<u8>);

struct CommandExecution {
    outcome: CommandOutcome,
    artifacts: Vec<OutputArtifact>,
}

impl CommandExecution {
    fn without_artifacts(outcome: CommandOutcome) -> Self {
        Self {
            outcome,
            artifacts: Vec::new(),
        }
    }
}

/// Execute one complete Cargo/collector/compiler command pipeline.
///
/// Every command collects the same canonical [`DescriptorBundle`], lowers it
/// through the same semantic theory and Definition IR, and then dispatches
/// only at the final command-specific stage. `build` calls only the permanent
/// structured native seam; it never invokes the provisional oracle or parses
/// emitted K source.
///
/// # Errors
///
/// Returns a typed stage error.
/// A native compilation or adapter failure without diagnostics is [`CommandError::Native`].
/// Native failures carrying diagnostics are [`CommandError::NativeDiagnostics`];
/// each diagnostic is translated independently and unlocated diagnostics remain available for prose.
pub fn execute_command(request: &CommandRequest) -> Result<CommandOutcome, CommandError> {
    execute_command_measured(request, &mut Measurement::disabled())
}

/// [`execute_command`] that records opt-in phase timings and work counters
/// (`krs-timings/1` and `krs-counters/1`, documented in [`krs_ir::measure`]).
///
/// Measurement never changes stdout or any artifact. On failure, `measurement`
/// holds every completed span and names the failing one.
///
/// # Errors
///
/// Fails exactly when [`execute_command`] fails.
pub fn execute_command_measured(
    request: &CommandRequest,
    measurement: &mut Measurement,
) -> Result<CommandOutcome, CommandError> {
    execute_command_reported(request, measurement).0
}

/// Executes a command and retains selected package paths for diagnostic rendering.
/// Source context remains available on failure and on cache restoration.
pub fn execute_command_reported(
    request: &CommandRequest,
    measurement: &mut Measurement,
) -> (
    Result<CommandOutcome, CommandError>,
    crate::DiagnosticSources,
) {
    let mut sources = crate::DiagnosticSources::default();
    let result = execute_with_sources(request, measurement, &mut sources);
    (result, sources)
}

fn execute_with_sources(
    request: &CommandRequest,
    measurement: &mut Measurement,
    sources: &mut crate::DiagnosticSources,
) -> Result<CommandOutcome, CommandError> {
    measurement.counters.set("result.reused", 0u64);
    validate_request(request)?;
    let timings = &mut measurement.timings;
    let metadata = timings.try_span("cargo.metadata.input", |_| {
        cargo_metadata(&request.manifest_path)
    })?;
    let host_target = timings.try_span("host.discover", |_| rustc_host_target())?;

    let runtime = timings.try_span("cargo.metadata.runtime", |_| discover_runtime())?;
    let plan = timings.try_span("collector.plan", |_| {
        let plan = CollectorPlan::resolve_definition(
            &metadata,
            &DefinitionRequest {
                root: request.root.clone(),
                dependencies: request.dependencies.clone(),
                host_target,
                cfg: request.cfg.clone(),
            },
            runtime,
        )?;
        Ok::<_, CommandError>(match request.registration {
            RegistrationMode::Inventory => plan,
            RegistrationMode::Explicit => plan.with_explicit_registration()?,
        })
    })?;
    *sources = crate::DiagnosticSources::from_plan(&plan);
    let collector_directory = generate_collector(&metadata, &plan, measurement)?;
    let executable = build_collector_measured(&collector_directory, &plan, measurement)?;
    let cache = ResultCache::new(&collector_directory, &executable, request);
    let reuse =
        !request.no_reuse && std::env::var_os("KRS_NO_REUSE").as_deref() != Some(OsStr::new("1"));
    if request.command.kind().reuses_results() && reuse {
        let started = std::time::Instant::now();
        if let Some(outcome) = cache.restore(request, &mut measurement.counters)? {
            measurement
                .timings
                .record("result.reuse", started.elapsed().as_secs_f64(), 0);
            measurement.counters.set("result.reused", 1u64);
            return Ok(outcome);
        }
    }
    let (stdout, read_set) = run_collector(&collector_directory, &executable, measurement)?;
    let prepared = prepare(stdout, request.profile, measurement)?;

    let mut outcome = match &request.command {
        Command::Check { backend, partition } => {
            check(&prepared, *backend, *partition, measurement)
                .map(CommandExecution::without_artifacts)
        }
        Command::Expand => measurement
            .timings
            .try_span("expand.render", |_| expand(&prepared, &plan))
            .map(CommandExecution::without_artifacts),
        Command::EmitK { output } => emit(&prepared, output, measurement),
        Command::Build { backend, output } => build(&prepared, *backend, output, measurement),
        Command::Parse(_) | Command::Run(_) | Command::Search(_) | Command::Prove(_) => {
            exec_command(
                &prepared,
                request,
                sources,
                metadata.workspace_root.as_deref().map(Path::new),
                reuse,
                measurement,
            )
        }
    };
    if let Command::Check { backend, .. } = &request.command
        && agreement::enabled()
    {
        let checked = outcome.as_ref().map(drop).map_err(ToString::to_string);
        if let Err(disagreement) = agreement::verify(&prepared, *backend, checked) {
            outcome = Err(disagreement);
        }
    }
    measurement.timings.span("release", |_| drop(prepared));
    if let Ok(ref value) = outcome
        && request.command.kind().reuses_results()
    {
        cache.store(
            request,
            &value.outcome,
            &value.artifacts,
            &read_set,
            &measurement.counters,
        );
    }
    outcome.map(|value| value.outcome)
}

/// `krs parse`, `run`, `search`, or `prove`: compile (or restore) the stage and run the command, then attach the definition's warnings.
fn exec_command(
    prepared: &PreparedDefinition,
    request: &CommandRequest,
    sources: &crate::DiagnosticSources,
    workspace_root: Option<&Path>,
    reuse: bool,
    measurement: &mut Measurement,
) -> Result<CommandExecution, CommandError> {
    // krs-exec compiles the definition natively in the symbolic dialect.
    require_route(prepared.lowered.definition(), Route::NativeRust)?;
    let (stage_cache, refused_store) =
        match StageCache::new(prepared.lowered.definition(), workspace_root) {
            Ok(cache) => (cache, None),
            Err(refused) => (None, Some(refused)),
        };
    let mut outcome = exec::execute(
        prepared,
        &request.command,
        sources,
        exec::StageReuse {
            cache: stage_cache.as_ref(),
            restore: reuse,
        },
        measurement,
    )?;
    outcome.warnings = raw_k_warnings(prepared);
    if matches!(request.command, Command::Prove(_)) {
        push_trusted_claim_warnings(prepared, &mut outcome.warnings);
    }
    if let Some(refused) = refused_store {
        outcome.warnings.unlocated.push(crate::UnlocatedDiagnostic {
            code: krs_diagnostic::codes::exec::STAGE_CACHE.to_string(),
            severity: crate::DiagnosticSeverity::Warning,
            message: refused.message(),
            source: None,
            generated_range: None,
            notes: Vec::new(),
        });
    }
    Ok(CommandExecution::without_artifacts(outcome))
}

fn validate_request(request: &CommandRequest) -> Result<(), CommandError> {
    if request.manifest_path.file_name() != Some(OsStr::new("Cargo.toml")) {
        return Err(CommandError::InvalidRequest(format!(
            "manifest path must end in Cargo.toml: `{}`",
            request.manifest_path.display()
        )));
    }
    Ok(())
}

fn prepare(
    stdout: Vec<u8>,
    profile: Option<krs_ir::RawKProfile>,
    measurement: &mut Measurement,
) -> Result<PreparedDefinition, CommandError> {
    let bundle: DescriptorBundle = measurement
        .timings
        .try_span("protocol.decode", |_| {
            let bundle = DescriptorBundle::from_collector_protocol(&stdout)
                .map_err(CommandError::DescriptorProtocol);
            let bytes = stdout.len();
            drop(stdout);
            bundle.map(|bundle| (bundle, bytes))
        })
        .map(|(bundle, bytes)| {
            count_bundle(&mut measurement.counters, &bundle, bytes);
            bundle
        })?;
    let raw_k =
        krs_compiler::raw_k_policy(&bundle, profile).map_err(CommandError::DescriptorLowering)?;
    if !raw_k.errors.is_empty() {
        return Err(CommandError::Diagnostics(
            raw_k
                .errors
                .into_iter()
                .filter_map(|diagnostic| {
                    crate::diagnostic_envelope(diagnostic, DiagnosticStage::Analysis, None)
                })
                .collect(),
        ));
    }
    let semantic = measurement
        .timings
        .try_span("semantic.lower", |_| lower_semantic(&bundle))?;
    measurement
        .counters
        .set("semantic.modules", semantic.modules().len());
    let lowered = measurement
        .timings
        .try_span("definition.lower", |_| lower_definition(&semantic))?;
    count_definition(&mut measurement.counters, &lowered);
    Ok(PreparedDefinition {
        raw_k_warnings: raw_k.warnings,
        sort_test_warnings: krs_compiler::sort_test_warnings(lowered.definition())
            .into_iter()
            .chain(krs_compiler::cell_collection_warnings(lowered.definition()))
            .collect(),
        bundle,
        semantic,
        lowered,
        compiles: agreement::CompileMemo::new(),
    })
}

fn lower_semantic(
    bundle: &DescriptorBundle,
) -> Result<krs_ir_levels::SemanticTheory, CommandError> {
    lower_descriptor_bundle(bundle).map_err(CommandError::DescriptorLowering)
}

fn lower_definition(
    semantic: &krs_ir_levels::SemanticTheory,
) -> Result<krs_compiler::LoweredDefinition, CommandError> {
    lower_semantic_theory(semantic).map_err(CommandError::Lowering)
}

/// `krs check`: the verdict of every command behind it that needs no
/// external K toolchain, without writing artifacts.
///
/// A check stands in front of `emit-k`, `build`, and the run commands, so it is
/// useful exactly to the degree that its verdict predicts theirs; it therefore
/// runs their judgements rather than a hand-maintained subset of them: the K
/// emission of `emit-k` ([`render_emitted`], in memory), and, for each judged
/// native route, the route's capability table and `build`'s native compile
/// ([`compile_native`]). The `native-rust` route is the one `run`, `search`,
/// and `prove` share with `build --backend haskell`, so on it the check also
/// loads the compiled definition as they do ([`exec::judge`]).
///
/// Without `--backend` every native route is judged, so a pass means that
/// `emit-k`, `build` on either backend, and the run commands all accept the
/// definition, and a failure names the route and the commands that refuse it.
/// `--backend B` narrows the claim to `emit-k` and `B`'s route.
fn check(
    prepared: &PreparedDefinition,
    backend: Option<Backend>,
    partition: bool,
    measurement: &mut Measurement,
) -> Result<CommandOutcome, CommandError> {
    let backends = judged_backends(backend)?;
    let several = backend.is_none();
    render_emitted(prepared, measurement)
        .map_err(|error| error.attributed("`krs emit-k` refuses this definition".to_owned()))?;
    // Every route's capability table before any compile: a refusal costs nothing to find.
    let mut refusals = backends.iter().filter_map(|&backend| {
        route_refusal(prepared.lowered.definition(), Route::native(backend))
            .map(|refusal| (backend, refusal))
    });
    if let Some((backend, refusal)) = refusals.next() {
        let every = refusals.count() + 1 == backends.len();
        return Err(if several && every {
            every_route_refuses(refusal)
        } else {
            route_attributed(refusal, backend, several)
        });
    }
    let warnings = measurement.timings.try_span("check.routes", |timings| {
        judge_routes(prepared, &backends, several, timings)
    })?;
    let stdout = if partition {
        prepared.lowered.partition().render()
    } else {
        format!(
            "KRS check passed: {} descriptors, {} semantic modules\n",
            prepared.bundle.descriptors().len(),
            prepared.semantic.modules().len()
        )
    };
    Ok(CommandOutcome {
        stderr: Vec::new(),
        exit_code: 0,
        warnings,
        stdout: stdout.into_bytes(),
    })
}

/// Judges each of `backends`' native routes and returns their warnings, or
/// the first refusal in `backends` order.
///
/// The routes' compiles are independent, so they run concurrently, each on its
/// own thread (`check.<route>` spans, recorded below `check.routes` once every
/// compile has ended, so the children's seconds may sum to more than their
/// parent's): judging both routes costs about the wall time of the slower one.
/// What follows each compile, the error or warnings `build` reports and, on
/// the `native-rust` route, the run commands' definition load
/// ([`exec::judge`], span `check.load`), runs here in `backends` order.
fn judge_routes(
    prepared: &PreparedDefinition,
    backends: &[Backend],
    several: bool,
    timings: &mut Timings,
) -> Result<crate::DiagnosticReports, CommandError> {
    let definition = prepared.lowered.definition();
    let memo = &prepared.compiles;
    let enabled = timings.is_enabled();
    let compiled = std::thread::scope(|scope| {
        let workers = backends
            .iter()
            .map(|&backend| {
                std::thread::Builder::new()
                    .name(format!("krs-check-{}", backend.as_str()))
                    .stack_size(exec::WORKER_STACK)
                    .spawn_scoped(scope, move || {
                        let mut timings = if enabled {
                            Timings::enabled()
                        } else {
                            Timings::disabled()
                        };
                        let id = format!("check.{}", Route::native(backend).name());
                        let compiled = timings
                            .try_span(&id, |timings| memo.compile(definition, backend, timings));
                        (compiled, timings)
                    })
            })
            .collect::<Vec<_>>();
        workers
            .into_iter()
            .map(|worker| {
                worker
                    .map_err(|error| {
                        CommandError::InvalidRequest(format!(
                            "could not start a check worker: {error}"
                        ))
                    })?
                    .join()
                    .map_err(|_| CommandError::InvalidRequest("a check worker panicked".into()))
            })
            .collect::<Result<Vec<_>, _>>()
    })?;
    for (_, route_timings) in &compiled {
        timings.import(route_timings.spans().iter().cloned());
    }
    let every = compiled.iter().all(|(compiled, _)| compiled.is_err());
    let mut warnings = crate::DiagnosticReports::default();
    for (&backend, (compiled, route_timings)) in backends.iter().zip(compiled) {
        if let Some(failed) = route_timings.failed_span() {
            timings.mark_failed(failed);
        }
        let route_warnings =
            judge_route(prepared, backend, compiled, timings).map_err(|error| {
                if several && every {
                    every_route_refuses(error)
                } else {
                    route_attributed(error, backend, several)
                }
            })?;
        extend_unique(&mut warnings, route_warnings);
    }
    Ok(warnings)
}

/// `build`'s verdict on `backend`'s route from its compile; on the
/// `native-rust` route also the definition load of `run`, `search`, and `prove`.
fn judge_route(
    prepared: &PreparedDefinition,
    backend: Backend,
    compiled: Result<(CompiledArtifacts, ConfigurationContext), DefinitionCompileError>,
    timings: &mut Timings,
) -> Result<crate::DiagnosticReports, CommandError> {
    let (artifacts, context, warnings) = finish_native(prepared, backend, compiled, timings)?;
    if Route::native(backend) == Route::NativeRust {
        timings
            .try_span("check.load", |timings| {
                exec::judge(prepared, artifacts, context, timings)
            })
            .map_err(|error| {
                error.attributed(
                    "`krs run`, `krs search`, and `krs prove` refuse this definition when they load it"
                        .to_owned(),
                )
            })?;
    }
    Ok(warnings)
}

/// The native backends `check` judges: the one `--backend` selects, or every
/// backend `build` takes.
fn judged_backends(backend: Option<Backend>) -> Result<Vec<Backend>, CommandError> {
    let backends = backend.map_or_else(|| Backend::ALL.to_vec(), |backend| vec![backend]);
    for &backend in &backends {
        require_backend(backend)?;
    }
    Ok(backends)
}

/// The commands that compile for `backend`'s native route.
const fn route_commands(backend: Backend) -> &'static str {
    match backend {
        Backend::Llvm => "`krs build --backend llvm`",
        Backend::Haskell => {
            "`krs build --backend haskell`, `krs run`, `krs search`, and `krs prove`"
        }
    }
}

/// When `check` judges several routes, names the route that refused and the
/// commands that use it, and the `--backend` that judges only the other route.
fn route_attributed(error: CommandError, backend: Backend, several: bool) -> CommandError {
    if !several {
        return error;
    }
    let other = match backend {
        Backend::Llvm => Backend::Haskell,
        Backend::Haskell => Backend::Llvm,
    };
    error.attributed(format!(
        "`{}` is the route of {}; `krs check --backend {}` judges only the route of {}",
        Route::native(backend).name(),
        route_commands(backend),
        other.as_str(),
        route_commands(other),
    ))
}

/// When `check` judges every route and each refuses the definition, says so.
fn every_route_refuses(error: CommandError) -> CommandError {
    error.attributed(
        "every native route refuses this definition, so no `krs build`, `krs run`, `krs search`, or `krs prove` accepts it; `krs emit-k` still writes its K"
            .to_owned(),
    )
}

/// Appends the diagnostics of `more` that `reports` does not already hold.
fn extend_unique(reports: &mut crate::DiagnosticReports, more: crate::DiagnosticReports) {
    for envelope in more.envelopes {
        if !reports.envelopes.contains(&envelope) {
            reports.envelopes.push(envelope);
        }
    }
    for diagnostic in more.unlocated {
        if !reports.unlocated.contains(&diagnostic) {
            reports.unlocated.push(diagnostic);
        }
    }
}

/// Appends one `krs::emit::trusted-claim` warning per trusted claim (KF-042): every
/// Haskell build and every prove run names the claims it assumes without proof.
fn push_trusted_claim_warnings(
    prepared: &PreparedDefinition,
    reports: &mut crate::DiagnosticReports,
) {
    for diagnostic in krs_compiler::trusted_claim_warnings(prepared.lowered.definition()) {
        let message = diagnostic.message.clone();
        if let Some(envelope) =
            crate::diagnostic_envelope(diagnostic, DiagnosticStage::Analysis, None)
        {
            reports.envelopes.push(envelope);
        } else {
            reports.unlocated.push(crate::UnlocatedDiagnostic {
                code: krs_diagnostic::codes::emit::TRUSTED_CLAIM.to_string(),
                severity: crate::DiagnosticSeverity::Warning,
                message,
                source: None,
                generated_range: None,
                notes: Vec::new(),
            });
        }
    }
}

/// Returns the `krs::expand::raw-hook` and `krs::semantic::raw-k` warnings of
/// the package's allowed raw K, then the `krs::analysis::trivial-sort-test`
/// and `krs::analysis::collection-config-var-without-initial` warnings;
/// every command reports them.
fn raw_k_warnings(prepared: &PreparedDefinition) -> crate::DiagnosticReports {
    let mut reports = crate::DiagnosticReports::default();
    for diagnostic in prepared
        .raw_k_warnings
        .iter()
        .chain(&prepared.sort_test_warnings)
    {
        if let Some(envelope) =
            crate::diagnostic_envelope(diagnostic.clone(), DiagnosticStage::Analysis, None)
        {
            reports.envelopes.push(envelope);
        } else {
            reports.unlocated.push(crate::UnlocatedDiagnostic {
                code: diagnostic.code.to_string(),
                severity: crate::DiagnosticSeverity::Warning,
                message: diagnostic.message.clone(),
                source: None,
                generated_range: None,
                notes: Vec::new(),
            });
        }
    }
    reports
}

/// Returns the `krs::expand::raw-hook` and `krs::semantic::raw-k` warnings of
/// allowed raw K, then `warning[krs::partition::not-program-syntax]` for each
/// `program` production that lowering placed in its package's semantics module.
fn definition_warnings(prepared: &PreparedDefinition) -> crate::DiagnosticReports {
    let mut reports = raw_k_warnings(prepared);
    for warning in prepared.lowered.partition().warnings() {
        let diagnostic = warning.to_diagnostic();
        if let Some(envelope) =
            crate::diagnostic_envelope(diagnostic, DiagnosticStage::Analysis, None)
        {
            reports.envelopes.push(envelope);
        } else {
            reports.unlocated.push(crate::UnlocatedDiagnostic {
                code: krs_diagnostic::codes::partition::NOT_PROGRAM_SYNTAX.to_string(),
                severity: crate::DiagnosticSeverity::Warning,
                message: warning.message().to_owned(),
                source: None,
                generated_range: None,
                notes: Vec::new(),
            });
        }
    }
    reports
}

fn expand(
    prepared: &PreparedDefinition,
    plan: &CollectorPlan,
) -> Result<CommandOutcome, CommandError> {
    let root = plan
        .facets()
        .iter()
        .find(|facet| facet.is_root)
        .ok_or_else(|| CommandError::InvalidMetadata("collector plan has no root facet".into()))?;
    let package = PackageId::new(
        &root.k_namespace,
        &root.package_name,
        &root.package_version,
        &root.cargo_source,
    )
    .map_err(|error| {
        CommandError::InvalidMetadata(format!("root package identity is invalid: {error}"))
    })?;
    let facade = FacadeAliases::from_manifest(&root.manifest_path).map_err(CommandError::Facade)?;
    let expanded = expand_package_reference_source(
        &prepared.bundle,
        &prepared.semantic,
        &package,
        &root.manifest_path,
        &facade.scope(),
    )?;
    Ok(CommandOutcome {
        stderr: Vec::new(),
        exit_code: 0,
        warnings: crate::DiagnosticReports::default(),
        stdout: expanded.into_bytes(),
    })
}

/// The artifacts `emit-k` writes, rendered in memory, in `emit-k`'s order;
/// `check` renders them too, so an emission failure fails the check.
fn render_emitted(
    prepared: &PreparedDefinition,
    measurement: &mut Measurement,
) -> Result<Vec<(&'static str, Vec<u8>)>, CommandError> {
    measurement.timings.try_span("emit_k.render", |_| {
        let descriptor_bundle = prepared.bundle.to_canonical_json()?;
        let semantic_ir = prepared.semantic.to_canonical_json()?;
        let definition_ir = prepared.lowered.definition().to_canonical_json()?;
        let emitted = emit_k(&prepared.lowered)?;
        let symbols = emitted.symbol_map().to_canonical_json()?;
        let sources = emitted.source_map().to_canonical_json()?;
        let mut artifacts = vec![
            (DESCRIPTOR_ARTIFACT, descriptor_bundle.into_bytes()),
            (SEMANTIC_ARTIFACT, semantic_ir.into_bytes()),
            (DEFINITION_IR_ARTIFACT, definition_ir.into_bytes()),
            (DEFINITION_ARTIFACT, emitted.source().as_bytes().to_vec()),
        ];
        if let Some(spec) = emitted.spec() {
            artifacts.push((SPEC_ARTIFACT, spec.source().as_bytes().to_vec()));
        }
        artifacts.extend([
            (SYMBOLS_ARTIFACT, symbols.into_bytes()),
            (SOURCES_ARTIFACT, sources.into_bytes()),
        ]);
        Ok::<_, CommandError>(artifacts)
    })
}

fn emit(
    prepared: &PreparedDefinition,
    output: &Path,
    measurement: &mut Measurement,
) -> Result<CommandExecution, CommandError> {
    let rendered = render_emitted(prepared, measurement)?;
    let stdout = emission_stdout(&rendered);
    let mut artifacts = rendered
        .into_iter()
        .map(|(name, bytes)| (name.to_owned(), bytes))
        .collect::<Vec<_>>();
    artifacts.sort_unstable_by(|(left, _), (right, _)| left.cmp(right));
    measurement.timings.try_span("emit_k.write", |_| {
        prepare_output(output)?;
        for (name, bytes) in &artifacts {
            write_output(output, name, bytes)?;
        }
        Ok::<_, CommandError>(())
    })?;
    for (name, bytes) in &artifacts {
        measurement
            .counters
            .set(format!("emit_k.bytes.{name}"), bytes.len());
    }
    Ok(CommandExecution {
        outcome: CommandOutcome {
            stderr: Vec::new(),
            exit_code: 0,
            warnings: definition_warnings(prepared),
            stdout,
        },
        artifacts,
    })
}

fn emission_stdout<B>(artifacts: &[(&str, B)]) -> Vec<u8> {
    let names = artifacts.iter().map(|(name, _)| *name).collect::<Vec<_>>();
    format!("emitted {}\n", names.join(", ")).into_bytes()
}

/// Refuses a definition that needs a feature `route` lacks, before any compilation (V8).
fn require_route(
    definition: &krs_ir_levels::DefinitionIr,
    route: krs_k_rust::Route,
) -> Result<(), CommandError> {
    route_refusal(definition, route).map_or(Ok(()), Err)
}

/// The refusal of the first feature, in table order, that `definition` needs
/// and `route` lacks; `None` when the route can run every feature it needs.
fn route_refusal(
    definition: &krs_ir_levels::DefinitionIr,
    route: krs_k_rust::Route,
) -> Option<CommandError> {
    let requirements = krs_compiler::capability::capability_requirements(definition);
    for feature in krs_compiler::capability::CapabilityFeature::ALL {
        if !requirements
            .iter()
            .any(|requirement| requirement.feature() == *feature)
        {
            continue;
        }
        if let krs_k_rust::CapabilityAvailability::Unavailable(reason) =
            krs_k_rust::route_capability(feature.name(), route)
        {
            return Some(CommandError::CapabilityUnavailable {
                route,
                message: krs_compiler::capability::unavailable_message(
                    *feature,
                    reason,
                    &requirements,
                ),
            });
        }
    }
    None
}

/// Refuses a backend dialect this frontend was not built with.
fn require_backend(backend: Backend) -> Result<(), CommandError> {
    if FRONTEND_CAPABILITIES.supports_backend(backend) {
        Ok(())
    } else {
        Err(CommandError::UnsupportedBackend(backend))
    }
}

/// The native judgement `build` makes of a definition once its route accepts
/// it: k-rust's preparation, compilation, and KORE reparse for `backend`, and
/// every warning `build` reports with the result. `check` runs this same
/// function, so the two commands cannot disagree about a definition; the
/// configuration context is what the run commands load with the artifacts.
fn compile_native(
    prepared: &PreparedDefinition,
    backend: Backend,
    timings: &mut Timings,
) -> Result<
    (
        CompiledArtifacts,
        ConfigurationContext,
        crate::DiagnosticReports,
    ),
    CommandError,
> {
    let compiled = prepared
        .compiles
        .compile(prepared.lowered.definition(), backend, timings);
    finish_native(prepared, backend, compiled, timings)
}

/// k-rust's compile of `definition` for `backend`, as every command makes it.
fn compile_for(
    definition: &krs_ir_levels::DefinitionIr,
    backend: Backend,
    timings: &mut Timings,
) -> Result<(CompiledArtifacts, ConfigurationContext), DefinitionCompileError> {
    krs_k_rust::compile_definition_with_context_timed(
        definition,
        krs_k_rust::CompileOptions {
            backend,
            ..krs_k_rust::CompileOptions::default()
        },
        timings,
    )
}

/// [`compile_native`] after k-rust's compile: the compile error as `build`
/// reports it, or the compiled definition with every warning `build` reports.
fn finish_native(
    prepared: &PreparedDefinition,
    backend: Backend,
    compiled: Result<(CompiledArtifacts, ConfigurationContext), DefinitionCompileError>,
    timings: &mut Timings,
) -> Result<
    (
        CompiledArtifacts,
        ConfigurationContext,
        crate::DiagnosticReports,
    ),
    CommandError,
> {
    let (artifacts, context) = compiled.map_err(|error| {
        timings.span("native.diagnostics", |_| {
            native_command_error(prepared.lowered.source_map(), error)
        })
    })?;
    let mut warnings = definition_warnings(prepared);
    if backend == Backend::Haskell {
        push_trusted_claim_warnings(prepared, &mut warnings);
    }
    // Only concrete execution needs what these warnings name: `ensures`
    // conditions it does not assume, and equations for `smt_hook` functions.
    if backend == Backend::Llvm {
        let definition = prepared.lowered.definition();
        for diagnostic in krs_compiler::capability::concrete_execution_warnings(definition)
            .into_iter()
            .chain(krs_compiler::smt_only_function_warnings(definition))
        {
            let code = diagnostic.code.to_string();
            let message = diagnostic.message.clone();
            if let Some(envelope) =
                crate::diagnostic_envelope(diagnostic, DiagnosticStage::Analysis, None)
            {
                warnings.envelopes.push(envelope);
            } else {
                warnings.unlocated.push(crate::UnlocatedDiagnostic {
                    code,
                    severity: crate::DiagnosticSeverity::Warning,
                    message,
                    source: None,
                    generated_range: None,
                    notes: Vec::new(),
                });
            }
        }
    }
    let native =
        crate::DiagnosticReports::native(prepared.lowered.source_map(), &artifacts.diagnostics);
    warnings.envelopes.extend(native.envelopes);
    warnings.unlocated.extend(native.unlocated);
    Ok((artifacts, context, warnings))
}

fn build(
    prepared: &PreparedDefinition,
    backend: Backend,
    output: &Path,
    measurement: &mut Measurement,
) -> Result<CommandExecution, CommandError> {
    require_backend(backend)?;
    require_route(prepared.lowered.definition(), Route::native(backend))?;
    let (artifacts, _, warnings) = compile_native(prepared, backend, &mut measurement.timings)?;
    let files = vec![
        (
            "definition.kore".to_owned(),
            artifacts.definition_kore.into_bytes(),
        ),
        (
            "syntaxDefinition.kore".to_owned(),
            artifacts.syntax_definition_kore.into_bytes(),
        ),
        ("macros.kore".to_owned(), artifacts.macros_kore.into_bytes()),
    ];
    // Do not create the output directory until structured compilation has
    // succeeded. A native rejection therefore leaves no artifacts.
    measurement.timings.try_span("native.write", |_| {
        prepare_output(output)?;
        for (name, bytes) in &files {
            write_output(output, name, bytes)?;
        }
        Ok::<_, CommandError>(())
    })?;
    for (name, bytes) in &files {
        measurement
            .counters
            .set(format!("native.bytes.{name}"), bytes.len());
    }
    measurement
        .counters
        .set("native.omitted_claims", artifacts.omitted_claims);
    // Only a backend that does not prove omits claims.
    let omitted = match artifacts.omitted_claims {
        0 => String::new(),
        1 => "omitted 1 claim: the llvm backend executes but does not prove\n".to_owned(),
        count => format!("omitted {count} claims: the llvm backend executes but does not prove\n"),
    };
    let stdout = format!("built definition.kore, syntaxDefinition.kore, macros.kore\n{omitted}");
    Ok(CommandExecution {
        outcome: CommandOutcome {
            stderr: Vec::new(),
            exit_code: 0,
            warnings,
            stdout: stdout.into_bytes(),
        },
        artifacts: files,
    })
}

fn native_command_error(
    source_map: &krs_compiler::SourceMap,
    error: DefinitionCompileError,
) -> CommandError {
    let diagnostics = error.diagnostics();
    if diagnostics.is_empty() {
        let envelope = diagnostic_envelope(
            error.to_diagnostic(),
            DiagnosticStage::Native,
            Some(source_map),
        );
        return match envelope {
            Some(envelope) => CommandError::NativeDiagnostics {
                reports: crate::DiagnosticReports {
                    envelopes: vec![envelope],
                    unlocated: Vec::new(),
                },
                source: error,
            },
            None => CommandError::Native(error),
        };
    }
    CommandError::NativeDiagnostics {
        reports: crate::DiagnosticReports::native(source_map, diagnostics),
        source: error,
    }
}

/// Failure from a named production-command stage.
#[derive(Debug)]
pub enum CommandError {
    /// The request or its selected source cannot satisfy the command.
    InvalidRequest(String),
    /// Cargo metadata output was malformed.
    Metadata(crate::MetadataError),
    /// Cargo metadata omitted a required execution field or runtime package.
    InvalidMetadata(String),
    /// Definition-facet planning failed.
    Planning(PlanningError),
    /// Collector package generation failed.
    Generation(GenerationError),
    /// A subprocess could not be started.
    ProcessStart {
        /// Stage being executed.
        stage: &'static str,
        /// Operating-system error.
        source: io::Error,
    },
    /// A subprocess returned a nonzero status.
    ProcessFailed {
        /// Stage being executed.
        stage: &'static str,
        /// Numeric exit status, absent when terminated by a signal.
        status: Option<i32>,
        /// Captured diagnostic stream.
        stderr: String,
    },
    /// One or more renderer-independent diagnostics with exact authored ranges.
    Diagnostics(Vec<DiagnosticEnvelope>),
    /// Native diagnostics translated individually, retaining the typed failure for fallback.
    NativeDiagnostics {
        /// Located envelopes and unlocated prose diagnostics.
        reports: crate::DiagnosticReports,
        /// Structured native failure.
        source: DefinitionCompileError,
    },
    /// Collector stdout was not a current canonical descriptor protocol.
    DescriptorProtocol(serde_json::Error),
    /// Collector diagnostics were malformed or used an unsupported schema.
    DiagnosticProtocol(serde_json::Error),
    /// Descriptor-to-semantic lowering failed.
    DescriptorLowering(DescriptorLoweringError),
    /// Semantic-to-Definition lowering failed.
    Lowering(LoweringError),
    /// Canonical K emission failed.
    Emission(EmitError),
    /// The root package's facade aliases could not be read for reference projection.
    Facade(CollectionError),
    /// Readable source could not be projected to deterministic layer-2 Rust.
    ReferenceExpansion(ReferenceExpansionError),
    /// Native structured compilation failed, including typed capabilities.
    Native(DefinitionCompileError),
    /// The selected native backend is unavailable in this build.
    UnsupportedBackend(Backend),
    /// The selected route lacks a feature the definition needs (V8).
    CapabilityUnavailable {
        /// The refusing route.
        route: krs_k_rust::Route,
        /// The refusal, naming the feature, its sentences, and the alternative.
        message: String,
    },
    /// Canonical JSON serialization failed.
    Serialization(serde_json::Error),
    /// A filesystem operation failed.
    Io {
        /// Affected path.
        path: PathBuf,
        /// Operating-system error.
        source: io::Error,
    },
    /// Artifact output appears to belong to the user or another tool.
    UnsafeOutput(PathBuf),
    /// A parse, run, search, or prove operation failed.
    Exec(krs_exec::ExecError),
    /// A run-family invocation that the selected definition rules out (exit status 2).
    Usage(String),
    /// A refusal `krs check` reports for another command, with a note naming that command.
    Attributed {
        /// Names the command, or the route, that refuses the definition.
        note: String,
        /// The refusal.
        source: Box<CommandError>,
    },
    /// `KRS_CHECK_AGREEMENT=1`: the verdict of `krs check` differs from the
    /// verdicts of the commands it judges.
    CheckDisagreement(String),
}

impl fmt::Display for CommandError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRequest(message) | Self::InvalidMetadata(message) => {
                formatter.write_str(message)
            }
            Self::Metadata(error) => error.fmt(formatter),
            Self::Planning(error) => write!(formatter, "could not plan collector: {error}"),
            Self::Generation(error) => error.fmt(formatter),
            Self::ProcessStart { stage, source } => {
                write!(formatter, "could not start {stage}: {source}")
            }
            Self::ProcessFailed {
                stage,
                status,
                stderr,
            } => write!(
                formatter,
                "{stage} failed with status {}: {}",
                status.map_or_else(|| "signal".to_owned(), |status| status.to_string()),
                stderr.trim_end()
            ),
            Self::Diagnostics(diagnostics) => write!(
                formatter,
                "compilation failed with {} structured diagnostic{}",
                diagnostics.len(),
                if diagnostics.len() == 1 { "" } else { "s" }
            ),
            Self::DiagnosticProtocol(error) => write!(
                formatter,
                "collector returned invalid diagnostic protocol: {error}"
            ),
            Self::DescriptorProtocol(error) => {
                write!(
                    formatter,
                    "collector returned invalid descriptor protocol: {error}"
                )
            }
            Self::DescriptorLowering(error) => error.fmt(formatter),
            Self::Lowering(error) => error.fmt(formatter),
            Self::Emission(error) => error.fmt(formatter),
            Self::Facade(error) => write!(formatter, "cannot resolve KRS facade: {error}"),
            Self::ReferenceExpansion(error) => error.fmt(formatter),
            Self::Native(error) | Self::NativeDiagnostics { source: error, .. } => {
                error.fmt(formatter)
            }
            Self::UnsupportedBackend(backend) => {
                write!(
                    formatter,
                    "native backend `{}` is unavailable",
                    backend.as_str()
                )
            }
            Self::CapabilityUnavailable { route, message } => {
                write!(
                    formatter,
                    "route `{}` refuses this definition: {message}",
                    route.name()
                )
            }
            Self::Serialization(error) => {
                write!(
                    formatter,
                    "could not serialize deterministic output: {error}"
                )
            }
            Self::Io { path, source } => {
                write!(formatter, "could not write `{}`: {source}", path.display())
            }
            Self::UnsafeOutput(path) => write!(
                formatter,
                "refusing to replace non-KRS artifact directory `{}`",
                path.display()
            ),
            Self::Exec(error) => error.fmt(formatter),
            Self::Usage(message) | Self::CheckDisagreement(message) => formatter.write_str(message),
            Self::Attributed { note, source } => write!(formatter, "{source} ({note})"),
        }
    }
}

impl Error for CommandError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Metadata(error) => Some(error),
            Self::Planning(error) => Some(error),
            Self::Generation(error) => Some(error),
            Self::ProcessStart { source, .. } | Self::Io { source, .. } => Some(source),
            Self::DescriptorProtocol(error)
            | Self::DiagnosticProtocol(error)
            | Self::Serialization(error) => Some(error),
            Self::DescriptorLowering(error) => Some(error),
            Self::Lowering(error) => Some(error),
            Self::Emission(error) => Some(error),
            Self::Facade(error) => Some(error),
            Self::ReferenceExpansion(error) => Some(error),
            Self::Native(error) | Self::NativeDiagnostics { source: error, .. } => Some(error),
            Self::Exec(error) => Some(error),
            Self::Attributed { source, .. } => Some(source.as_ref()),
            Self::Usage(_)
            | Self::CheckDisagreement(_)
            | Self::InvalidRequest(_)
            | Self::InvalidMetadata(_)
            | Self::ProcessFailed { .. }
            | Self::Diagnostics(_)
            | Self::UnsupportedBackend(_)
            | Self::CapabilityUnavailable { .. }
            | Self::UnsafeOutput(_) => None,
        }
    }
}

impl CommandError {
    /// The process exit status for this failure: 2 for a usage error, 1 otherwise.
    #[must_use]
    pub fn exit_code(&self) -> i32 {
        match self {
            Self::Attributed { source, .. } => source.exit_code(),
            Self::Usage(_)
            | Self::Exec(krs_exec::ExecError::StrayProgram | krs_exec::ExecError::MissingProgram) => {
                2
            }
            _ => 1,
        }
    }

    fn diagnostic_model(&self) -> Option<(Diagnostic, DiagnosticStage)> {
        let (mut diagnostic, stage) = match self {
            Self::Exec(error) => (
                Diagnostic::error(
                    exec::diagnostic_code(error),
                    String::new(),
                    krs_diagnostic::Location::None,
                ),
                DiagnosticStage::Native,
            ),
            Self::Planning(error) => (error.to_diagnostic(), DiagnosticStage::Analysis),
            Self::Generation(error) => (error.to_diagnostic(), DiagnosticStage::Analysis),
            Self::DescriptorLowering(error) => (error.to_diagnostic(), DiagnosticStage::Analysis),
            Self::Lowering(error) => (error.to_diagnostic(), DiagnosticStage::Analysis),
            Self::Emission(error) => (error.to_diagnostic(), DiagnosticStage::Analysis),
            Self::Facade(error) => (error.to_diagnostic(), DiagnosticStage::Analysis),
            Self::ReferenceExpansion(error) => (error.to_diagnostic(), DiagnosticStage::Analysis),
            Self::Native(error) => (error.to_diagnostic(), DiagnosticStage::Native),
            Self::CapabilityUnavailable { .. } => (
                Diagnostic::error(
                    krs_diagnostic::codes::capability::UNAVAILABLE,
                    String::new(),
                    krs_diagnostic::Location::None,
                ),
                DiagnosticStage::Native,
            ),
            _ => return None,
        };
        diagnostic.message = self.to_string();
        if let Self::Exec(_) = self {
            // A listing (declared or missing variables) follows the first line; render it as notes.
            let mut lines = diagnostic.message.lines().map(str::trim).map(str::to_owned);
            let message = lines.next().unwrap_or_default();
            diagnostic.notes.extend(lines);
            message
                .trim_end_matches(':')
                .clone_into(&mut diagnostic.message);
        }
        Some((diagnostic, stage))
    }

    /// Returns diagnostics that have no exact authored range.
    #[must_use]
    pub fn unlocated_diagnostics(&self) -> Cow<'_, [crate::UnlocatedDiagnostic]> {
        if let Self::Attributed { note, source } = self {
            let mut diagnostics = source.unlocated_diagnostics().into_owned();
            for diagnostic in &mut diagnostics {
                diagnostic.notes.push(note.clone());
            }
            return Cow::Owned(diagnostics);
        }
        if let Self::NativeDiagnostics { reports, .. } = self {
            return Cow::Borrowed(&reports.unlocated);
        }
        let Some((diagnostic, stage)) = self.diagnostic_model() else {
            return Cow::Borrowed(&[]);
        };
        if diagnostic_envelope(diagnostic.clone(), stage, None).is_some() {
            return Cow::Borrowed(&[]);
        }
        Cow::Owned(vec![crate::UnlocatedDiagnostic {
            code: diagnostic.code.to_string(),
            severity: diagnostic.severity.into(),
            message: diagnostic.message,
            source: None,
            generated_range: None,
            notes: diagnostic.notes,
        }])
    }

    /// Returns envelopes and exposes unlocated producer diagnostics through [`Self::unlocated_diagnostics`].
    #[must_use]
    pub fn diagnostics(&self) -> Option<Cow<'_, [DiagnosticEnvelope]>> {
        match self {
            Self::Attributed { note, source } => {
                let mut diagnostics = source.diagnostics()?.into_owned();
                for diagnostic in &mut diagnostics {
                    diagnostic.notes.push(note.clone());
                }
                return Some(Cow::Owned(diagnostics));
            }
            Self::Diagnostics(diagnostics) => return Some(Cow::Borrowed(diagnostics)),
            Self::NativeDiagnostics { reports, .. } => {
                return Some(Cow::Borrowed(&reports.envelopes));
            }
            _ => {}
        }
        let (diagnostic, stage) = self.diagnostic_model()?;
        Some(Cow::Owned(
            diagnostic_envelope(diagnostic, stage, None)
                .into_iter()
                .collect(),
        ))
    }
}

impl CommandError {
    /// This refusal with `note`, which names the command that refuses.
    fn attributed(self, note: String) -> Self {
        Self::Attributed {
            note,
            source: Box::new(self),
        }
    }
}

impl From<PlanningError> for CommandError {
    fn from(value: PlanningError) -> Self {
        Self::Planning(value)
    }
}

impl From<GenerationError> for CommandError {
    fn from(value: GenerationError) -> Self {
        Self::Generation(value)
    }
}

impl From<DescriptorLoweringError> for CommandError {
    fn from(value: DescriptorLoweringError) -> Self {
        Self::DescriptorLowering(value)
    }
}

impl From<LoweringError> for CommandError {
    fn from(value: LoweringError) -> Self {
        Self::Lowering(value)
    }
}

impl From<EmitError> for CommandError {
    fn from(value: EmitError) -> Self {
        Self::Emission(value)
    }
}

impl From<ReferenceExpansionError> for CommandError {
    fn from(value: ReferenceExpansionError) -> Self {
        Self::ReferenceExpansion(value)
    }
}

impl From<DefinitionCompileError> for CommandError {
    fn from(value: DefinitionCompileError) -> Self {
        Self::Native(value)
    }
}

impl From<serde_json::Error> for CommandError {
    fn from(value: serde_json::Error) -> Self {
        Self::Serialization(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PackageSelector;
    use krs_diagnostic::{Location, codes};
    use krs_ir::{Sha256Digest, SourceFileId, SourceRange};

    #[test]
    fn emission_stdout_preserves_artifact_names_and_claims_spelling() {
        let mut artifacts: Vec<(&str, &[u8])> = vec![
            (DESCRIPTOR_ARTIFACT, b""),
            (SEMANTIC_ARTIFACT, b""),
            (DEFINITION_IR_ARTIFACT, b""),
            (DEFINITION_ARTIFACT, b""),
            (SYMBOLS_ARTIFACT, b""),
            (SOURCES_ARTIFACT, b""),
        ];
        assert_eq!(
            emission_stdout(&artifacts),
            b"emitted descriptor-bundle.json, semantic-ir.json, definition-ir.json, definition.k, symbols.json, sources.json\n"
        );
        artifacts.insert(4, (SPEC_ARTIFACT, b""));
        assert_eq!(
            emission_stdout(&artifacts),
            b"emitted descriptor-bundle.json, semantic-ir.json, definition-ir.json, definition.k, spec.k, symbols.json, sources.json\n"
        );
    }

    #[test]
    fn analysis_failures_expose_envelopes_only_with_an_exact_authored_range() {
        let package = PackageId::new("diag", "diag", "0.1.0", "workspace").unwrap();
        let file = SourceFileId::new(
            package,
            "src/lib.rs",
            Sha256Digest::new("11".repeat(32)).unwrap(),
        )
        .unwrap();
        let range = SourceRange::new(file, 7, 16).unwrap();
        let error = LoweringError::NameCollision {
            namespace: krs_compiler::CollisionNamespace::EmittedSymbol,
            value: "name".to_owned(),
            first: "first".to_owned(),
            second: "second".to_owned(),
            first_origin: Box::new(krs_ir::OriginStack::authored(range.clone())),
            second_origin: krs_ir::OriginStack::authored(range.clone()),
        };
        let message = error.to_string();
        let failure = CommandError::from(error);
        let envelopes = failure.diagnostics().unwrap();
        assert_eq!(envelopes.len(), 1);
        assert_eq!(envelopes[0].code, "krs::analysis::symbol-name-collision");
        assert_eq!(envelopes[0].message, message);
        assert_eq!(envelopes[0].authored_range, range);
        let unlocated = CommandError::Lowering(LoweringError::InvalidSidecar("detail".to_owned()));
        assert!(unlocated.diagnostics().unwrap().is_empty());
        let reports = unlocated.unlocated_diagnostics();
        assert_eq!(reports.len(), 1);
        assert_eq!(reports[0].message, "invalid lowered sidecar: detail");
        assert_eq!(unlocated.to_string(), "invalid lowered sidecar: detail");
    }

    #[test]
    fn compiler_fallbacks_render_with_codes_and_preserve_messages() {
        let planning = crate::plan::manifest_directory(Path::new("/")).unwrap_err();
        let cases = [
            (
                CommandError::Facade(
                    FacadeAliases::from_manifest(Path::new("/nonexistent-krs-facade/Cargo.toml"))
                        .unwrap_err(),
                ),
                codes::collect::HOST_IO,
            ),
            (
                CommandError::Planning(planning),
                codes::plan::INVALID_METADATA,
            ),
            (
                CommandError::Generation(GenerationError::UnsafeOutput(PathBuf::from("output"))),
                codes::generate::UNSAFE_OUTPUT,
            ),
            (
                CommandError::Emission(EmitError::InvalidReference("missing symbol".to_owned())),
                codes::emit::INVALID_REFERENCE,
            ),
            (
                CommandError::ReferenceExpansion(ReferenceExpansionError::DuplicateRule(
                    "step".to_owned(),
                )),
                codes::reference::DUPLICATE_RULE,
            ),
            (
                CommandError::Native(DefinitionCompileError::Provenance(
                    krs_k_rust::ProvenanceError::InvalidIdentity("identity".to_owned()),
                )),
                codes::native::INVALID_IDENTITY,
            ),
        ];
        for (error, code) in cases {
            assert!(error.diagnostics().unwrap().is_empty());
            let diagnostics = error.unlocated_diagnostics();
            assert_eq!(diagnostics.len(), 1);
            let diagnostic = diagnostics[0].to_diagnostic();
            assert_eq!(diagnostic.code, code);
            assert_eq!(diagnostic.message, error.to_string());
            assert!(matches!(diagnostic.primary.location, Location::None));
            let rendered =
                crate::DiagnosticSources::default().render_diagnostic(&diagnostic, false);
            assert_eq!(rendered, format!("error[{code}]: {error}"));
        }
    }

    #[test]
    fn adapter_fallback_resolves_its_definition_key_through_the_source_map() {
        let package = PackageId::new("diag", "diag", "0.1.0", "workspace").unwrap();
        let file = SourceFileId::new(
            package,
            "src/lib.rs",
            Sha256Digest::new("11".repeat(32)).unwrap(),
        )
        .unwrap();
        let range = SourceRange::new(file, 7, 16).unwrap();
        let key = krs_ir::SourceMapKey::new("definition.item").unwrap();
        let source_map = serde_json::from_value(serde_json::json!({
            "schema_version": 2,
            "entries": [{
                "key": key.as_str(),
                "node_kind": "module",
                "origin": krs_ir::OriginStack::authored(range.clone()),
            }],
        }))
        .unwrap();
        let error = DefinitionCompileError::Adapter(krs_k_rust::AdapterError::MissingReference {
            key,
            kind: "sort",
            target: "Missing".to_owned(),
        });
        let message = error.to_string();
        let routed = native_command_error(&source_map, error);
        let diagnostics = routed.diagnostics().unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(
            diagnostics[0].code,
            codes::native::ADAPTER_MISSING_REFERENCE.as_str()
        );
        assert_eq!(diagnostics[0].message, message);
        assert_eq!(diagnostics[0].authored_range, range);
        assert!(routed.unlocated_diagnostics().is_empty());
    }

    #[test]
    fn attributed_refusals_keep_the_refusal_and_add_the_note() {
        let refusal = CommandError::CapabilityUnavailable {
            route: Route::NativeLlvm,
            message: "lacks a feature".to_owned(),
        };
        let unlocated = refusal.unlocated_diagnostics().into_owned();
        let attributed = refusal.attributed("the note".to_owned());
        assert_eq!(attributed.exit_code(), 1);
        assert!(attributed.diagnostics().unwrap().is_empty());
        let diagnostics = attributed.unlocated_diagnostics();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].message, unlocated[0].message);
        assert_eq!(diagnostics[0].notes, ["the note"]);
        assert_eq!(
            attributed.to_string(),
            "route `native-llvm` refuses this definition: lacks a feature (the note)"
        );
    }

    #[test]
    fn manifest_path_must_name_cargo_toml() {
        let base = CommandRequest {
            command: Command::Check {
                backend: None,
                partition: false,
            },
            manifest_path: PathBuf::from("Cargo.toml"),
            root: FacetSelector {
                package: PackageSelector::Name("language".to_owned()),
                definition: "main".to_owned(),
            },
            dependencies: Vec::new(),
            cfg: Vec::new(),
            registration: RegistrationMode::Inventory,
            no_reuse: false,
            message_format: MessageFormat::Human,
            profile: None,
        };
        assert!(validate_request(&base).is_ok());
        let mut invalid = base;
        invalid.manifest_path = PathBuf::from("Other.toml");
        assert!(matches!(
            validate_request(&invalid),
            Err(CommandError::InvalidRequest(_))
        ));
    }
}
