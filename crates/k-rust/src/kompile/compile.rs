//! ```toml algorithm
//! id = "kompile.modules.rewrite_order"
//! name = "collection of execution rewrite order through imports"
//! sites = ["collect_execution_rewrite_order"]
//! variable = "M = modules; E = import edges; R = rewrite sentences; d = import depth; u = repeated UNIQUE_ID occurrences; s = normalized sentence size"
//! counters = []
//! no_counter = "execution rewrite-order collection has no dedicated counter"
//! constrains = [
//!   { id = "kompile.sentences.number", site = "collect_execution_rewrite_order", via = "the UNIQUE_ID attribute set by number_sentences" },
//! ]
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O((M + E) x (d + log M) + R log R + u x s)"
//! ```
//!
//! The host-independent pass driver applies 34 named stages and preserves two checked-definition checkpoints.
//! Complexity: O(sum of the named stage work).
//! `tests/phase_timings.rs` pins stage names and `tests/provenance_manifest.rs` pins the transformation source; `KompileSentencesTransformed` measures output volume.
//!
//! Host-independent orchestration of the ordered K frontend compilation pipeline.

use std::{
    collections::{BTreeMap, BTreeSet},
    convert::Infallible,
    fmt,
    str::FromStr,
};

use k_rust_kore::measure::{self, Counter};

use crate::names::{BuiltinSort, WellKnownSymbol};
use crate::{
    definition::{
        AttributeKey, CheckMode, Definition, FlatModule, ResolvedDefinition, Sentence,
        StructuralCheckBackend, StructuralCheckOptions,
        checks::{
            check_definition_with_options, check_locations_import, check_singleton_overloads,
        },
        production_kind::ProductionKind,
    },
    diagnostic::{Diagnostic, DiagnosticCode, DiagnosticPolicy, Severity},
    kast::{GeneratedLabel, Sort, Term},
    kore::printer::Printer as KorePrinter,
    outer::{InputAddressing, LoadOptions, LoadedDefinition},
    provenance::{
        GeneratingPass, InputAddress, InputSentenceKind, InputSpace, input_sentence_kinds,
        stamp_input_addresses,
    },
    timings::PhaseTimings,
};

use super::module_to_kore::module_to_kore_from_resolved_with_options_and_sources;
use super::module_to_kore::{BUILTIN_HOOK_NAMESPACES, is_real_hook};
use super::passes::number_sentence;
use super::pipeline::{DeepestTerm, StageObserver, emission_phase, prologue_phase};
use super::{ModuleToKoreOptions, rust_backend_hook_namespaces};

/// Backend whose KORE input should be generated.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CompilationBackend {
    Llvm,
    /// The in-process symbolic backend. Its KORE is the dialect `kompile --backend haskell` emits
    /// (including the map definedness axioms) plus the plugin hook namespaces the backend
    /// dispatches natively, so `haskell` names the same target.
    #[default]
    Rust,
}

impl CompilationBackend {
    /// Module attribute excluded before compilation for this backend.
    /// Plugin hook namespaces admitted as hooked symbols when `--hook-namespaces` is not given.
    ///
    /// The Rust backend dispatches its plugin hooks natively. Another backend is not known to
    /// implement a plugin hook, so a plugin hook is emitted as an ordinary symbol unless
    /// `--hook-namespaces` names its namespace.
    pub fn default_hook_namespaces(self) -> Vec<String> {
        match self {
            Self::Rust => rust_backend_hook_namespaces(),
            Self::Llvm => Vec::new(),
        }
    }

    pub fn excluded_module_attribute(self) -> &'static str {
        match self {
            Self::Llvm => "symbolic",
            Self::Rust => "concrete",
        }
    }

    /// The options a definition compiled for this backend is loaded with: the modules marked
    /// [`Self::excluded_module_attribute`] are left out, since this backend never runs them, and
    /// every other option is at its default. A host sets its own sources and diagnostics policy on
    /// top.
    pub fn load_options(self) -> LoadOptions {
        LoadOptions {
            excluded_module_attributes: vec![self.excluded_module_attribute().into()],
            ..LoadOptions::default()
        }
    }

    pub(crate) fn structural_check_options(
        self,
        mode: CheckMode,
        builtin_source_prefixes: Vec<String>,
    ) -> StructuralCheckOptions {
        match self {
            Self::Llvm => StructuralCheckOptions {
                builtin_source_prefixes,
                mode,
                symbolic: false,
                backend: StructuralCheckBackend::Other,
            },
            Self::Rust => StructuralCheckOptions {
                symbolic: true,
                backend: StructuralCheckBackend::Rust,
                builtin_source_prefixes,
                mode,
            },
        }
    }
}

impl fmt::Display for CompilationBackend {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Llvm => "llvm",
            Self::Rust => "rust",
        })
    }
}

impl FromStr for CompilationBackend {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "llvm" => Ok(Self::Llvm),
            "rust" | "haskell" => Ok(Self::Rust),
            _ => Err(format!(
                "unsupported compilation backend {value:?}; expected \"rust\" or \"llvm\""
            )),
        }
    }
}

/// Options affecting backend selection and textual KORE rendering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompileOptions {
    pub backend: CompilationBackend,
    pub kore_width: usize,
    /// Match `kprove` by treating bare claims as all-path reachability claims.
    pub default_claims_to_all_path: bool,
    /// Plugin hook namespaces to admit as hooked symbols (`kompile --hook-namespaces`); `None`
    /// uses [`CompilationBackend::default_hook_namespaces`].
    pub hook_namespaces: Option<Vec<String>>,
    /// Filtering and severity policy for diagnostics produced by compilation checks.
    pub diagnostics: DiagnosticPolicy,
    /// Definition-only or proof-module structural checks.
    pub check_mode: CheckMode,
    /// Canonical source prefixes whose declarations are supplied by the builtin catalog.
    pub builtin_source_prefixes: Vec<String>,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            backend: CompilationBackend::Rust,
            kore_width: 100,
            default_claims_to_all_path: false,
            hook_namespaces: None,
            diagnostics: DiagnosticPolicy::default(),
            check_mode: CheckMode::default(),
            builtin_source_prefixes: vec!["krust-builtin://".into()],
        }
    }
}

/// The three artifacts traditionally written by `krust kcompile`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompiledKoreArtifacts {
    pub definition_kore: String,
    pub syntax_definition_kore: String,
    pub macros_kore: String,
    pub diagnostics: Vec<Diagnostic>,
    /// Configuration variable sorts in the transformed main module.
    ///
    /// Names omit the leading `$`. Collection after the compiler passes makes variables generated
    /// for stream cells visible to execution clients.
    pub configuration_variables: BTreeMap<String, Sort>,
    /// The transformed execution definition before backend-only sort injection, unit removal,
    /// and term-construction minimization.
    ///
    /// Standalone surface patterns must use this exact context so macro expansion, cell syntax,
    /// and production identities agree with the compilation that emitted `definition_kore`.
    pub execution_definition: Definition,
    /// Executable semantic rewrite precedence from the transformed source definition.
    ///
    /// KORE emission structurally sorts rules, so source-backed execution joins this order to the
    /// emitted axioms by their final `UNIQUE_ID`. Equivalent duplicate rules occur only once.
    pub execution_rewrite_order: Vec<String>,
    /// The input sentences behind each emitted rule or claim in `definition_kore` or
    /// `macros_kore`, keyed by its backend UNIQUE_ID.
    /// Equal-content sentences with one UNIQUE_ID contribute all of their input addresses.
    pub sentence_provenance: BTreeMap<String, EmittedSentenceProvenance>,
}

impl CompiledKoreArtifacts {
    /// The execution digest of `definition_kore` (`k_rust::backend::execution_digest`, whose
    /// rustdoc states what equal digests mean). It covers `definition.kore` only: not the
    /// syntax or macros definitions, and not `execution_rewrite_order`. A `definition_kore` that
    /// does not parse has no digest (`NotCanonical`); compiler output always parses.
    pub fn execution_digest(
        &self,
    ) -> Result<
        k_rust_backend::definition::ExecutionDigest,
        k_rust_backend::definition::ExecutionDigestError,
    > {
        let definition = crate::kore::parser::parse_definition(&self.definition_kore)
            .map_err(|_| k_rust_backend::definition::ExecutionDigestError::NotCanonical)?;
        k_rust_backend::definition::execution_digest(&definition)
    }
}

/// Input provenance of one emitted rule or claim identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmittedSentenceProvenance {
    /// Distinct input addresses in emission order.
    pub input_addresses: Vec<InputAddress>,
    /// Original kind of each addressed input sentence.
    pub input_sentence_kinds: BTreeMap<InputAddress, InputSentenceKind>,
    /// Generating pass when no input sentence contributed to this identity.
    pub generated_by: Option<GeneratingPass>,
}

/// A compilation failure with its precise pipeline stage and any structured diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompileError {
    pub stage: &'static str,
    pub message: String,
    pub diagnostics: Vec<Diagnostic>,
}

impl CompileError {
    fn from_error(stage: &'static str, error: impl fmt::Display) -> Self {
        Self {
            stage,
            message: error.to_string(),
            diagnostics: Vec::new(),
        }
    }

    fn from_diagnostics(
        stage: &'static str,
        message: impl Into<String>,
        diagnostics: Vec<Diagnostic>,
    ) -> Self {
        Self {
            stage,
            message: message.into(),
            diagnostics,
        }
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "kcompile stage {:?} failed: {}",
            self.stage, self.message
        )
    }
}

impl std::error::Error for CompileError {}

/// Run one named pipeline stage inside the timer and label its failure with the stage name.
fn stage<T, E: fmt::Display>(
    timings: &mut PhaseTimings,
    name: &'static str,
    run: impl FnOnce() -> Result<T, E>,
) -> Result<T, CompileError> {
    timings
        .time(name, run)
        .map_err(|error| CompileError::from_error(name, error))
}

/// Compile an in-memory, backend-filtered definition into backend-facing textual KORE artifacts.
///
/// Hosts must load the definition with [`CompilationBackend::load_options`] (the modules of
/// [`CompilationBackend::excluded_module_attribute`] left out) before calling this function. No filesystem or external backend process is used here.
///
/// Compilation reads only its arguments and the process-wide inputs `docs/compatibility.md`
/// names, and no locale: several threads may
/// compile one shared [`LoadedDefinition`] (or distinct ones) at once, and each call returns the
/// artifacts, or the [`CompileError`], that the same call returns alone on one thread. Every
/// stage runs on a stack sized from the definition's deepest term, so the artifacts do not depend
/// on the calling thread's stack size; only whether an input deep enough to need a mapped stack
/// segment is refused also depends on the calling thread's remaining stack and on the host. Wall
/// time and peak memory under concurrency are not promised (`docs/compatibility.md`,
/// "Determinism and concurrency").
pub fn compile_loaded_definition(
    loaded: &LoadedDefinition,
    options: CompileOptions,
) -> Result<CompiledKoreArtifacts, CompileError> {
    compile_loaded_definition_timed(loaded, options).map(|(artifacts, _)| artifacts)
}

/// [`compile_loaded_definition`] that also returns the wall-clock duration of every pipeline
/// stage in execution order, with the call's wall-clock span.
///
/// The stage names are the pipeline's documented order; `crates/k-rust/tests/phase_timings.rs`
/// pins the list. A failed compile returns no timings here; use
/// [`compile_loaded_definition_with_timings`] to keep the timings of the stages that ran.
///
/// Like [`compile_loaded_definition`], it may run on several threads at once over one shared
/// [`LoadedDefinition`] and returns the same artifacts or error; the timings are wall-clock and
/// are not covered.
pub fn compile_loaded_definition_timed(
    loaded: &LoadedDefinition,
    options: CompileOptions,
) -> Result<(CompiledKoreArtifacts, PhaseTimings), CompileError> {
    let mut timings = PhaseTimings::default();
    timings
        .span(|timings| compile_loaded_definition_with_timings(loaded, options, timings))
        .map(|artifacts| (artifacts, timings))
}

/// [`compile_loaded_definition`], appending the wall-clock duration of every pipeline stage that
/// runs to `timings`, whether compilation succeeds or fails.
///
/// Phases are appended in execution order at the caller's current nesting depth: depth 0 for a
/// fresh value, one level deeper inside each enclosing [`PhaseTimings::time_nested`], so a caller
/// can nest the compile under a phase of its own. Their relative depths and names are those
/// [`compile_loaded_definition_timed`] returns.
///
/// On failure the appended phases are every stage that ran, ending with the stage that failed
/// when the failure is a timed stage's own. [`CompileError::stage`] names the failing stage in
/// every case; a failure raised between stages follows the last timed phase. Such failures are
/// `"post-compilation checks"`, `"emitted sentence provenance"`, and a refusal raised before a
/// stage runs under that stage's name, such as the `"emit KORE"` refusal when no stack holds the
/// transformed definitions' deepest term: no phase of that name is recorded then.
///
/// The entries and span `timings` already holds are kept, so one value may accumulate the
/// load and compile phases; this function sets no span. A caller that wants the call's
/// wall-clock span wraps it in [`PhaseTimings::span`].
///
/// The timings are a property of one run, not of the definition, so they are deliberately not
/// part of [`CompileError`]: two compiles that fail the same way return equal errors.
pub fn compile_loaded_definition_with_timings(
    loaded: &LoadedDefinition,
    options: CompileOptions,
    timings: &mut PhaseTimings,
) -> Result<CompiledKoreArtifacts, CompileError> {
    compile_loaded_definition_observed(loaded, options, timings, &mut |_, _, _| {})
}

/// [`compile_loaded_definition_with_timings`], reporting every transformation and emission stage
/// to `observer` as it completes or fails.
pub(crate) fn compile_loaded_definition_observed(
    loaded: &LoadedDefinition,
    options: CompileOptions,
    timings: &mut PhaseTimings,
    observer: &mut StageObserver<'_>,
) -> Result<CompiledKoreArtifacts, CompileError> {
    let (execution_definition, definition, diagnostics, resolved) =
        transform_loaded_definition(loaded, &options, timings, observer)?;
    // Emission walks the transformed definitions (KORE conversion, printing, provenance): it
    // runs on a stack that holds their deepest term.
    DeepestTerm::of_all([&execution_definition, &definition]).run(
        emission_phase::EMIT_KORE,
        || {
            emit_compiled(
                loaded,
                &options,
                timings,
                Transformed {
                    execution_definition,
                    definition,
                    diagnostics,
                    resolved,
                },
            )
        },
    )?
}

/// Run `work`, which walks the terms of `definitions` (writing a compiled definition out, for
/// instance), on a stack that holds their deepest term; refused as `stage`'s error, located at
/// that term's sentence, when no stack this build maps holds it.
pub fn on_definitions_stack<'a, T>(
    definitions: impl IntoIterator<Item = &'a Definition>,
    stage: &'static str,
    work: impl FnOnce() -> T,
) -> Result<T, CompileError> {
    DeepestTerm::of_all(definitions).run(stage, work)
}

/// What the transformation stages give emission.
struct Transformed {
    execution_definition: Definition,
    definition: Definition,
    diagnostics: Vec<Diagnostic>,
    resolved: ResolvedDefinition,
}

/// The emission half of [`compile_loaded_definition_with_timings`]: the checks of the transformed
/// definition, its KORE, and the provenance of the emitted sentences.
fn emit_compiled(
    loaded: &LoadedDefinition,
    options: &CompileOptions,
    timings: &mut PhaseTimings,
    transformed: Transformed,
) -> Result<CompiledKoreArtifacts, CompileError> {
    let Transformed {
        execution_definition,
        definition,
        mut diagnostics,
        resolved,
    } = transformed;
    measure::add(
        Counter::KompileSentencesTransformed,
        definition
            .modules
            .iter()
            .map(|module| module.local_sentences.len() as u64)
            .sum(),
    );
    let execution_rewrite_order = stage(
        timings,
        emission_phase::COLLECT_EXECUTION_REWRITE_ORDER,
        || collect_execution_rewrite_order(&execution_definition),
    )?;
    let resolved = stage(
        timings,
        emission_phase::RESOLVE_TRANSFORMED_DEFINITION,
        || Ok::<_, String>(resolved),
    )?;
    diagnostics.extend(options.diagnostics.apply(
        timings.time(emission_phase::SINGLETON_OVERLOAD_CHECKS, || {
            check_singleton_overloads(&resolved)
        }),
    ));
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err(CompileError::from_diagnostics(
            "post-compilation checks",
            "post-compilation checks failed",
            diagnostics,
        ));
    }
    let configuration_variables = stage(
        timings,
        emission_phase::COLLECT_CONFIGURATION_VARIABLES,
        || configuration_variables(&resolved),
    )?;
    let hook_namespaces = options
        .hook_namespaces
        .clone()
        .unwrap_or_else(|| options.backend.default_hook_namespaces());
    diagnostics.extend(options.diagnostics.apply(timings.time(
        emission_phase::HOOK_NAMESPACE_CHECKS,
        || {
            let mut diagnostics =
                unadmitted_hook_namespace_diagnostics(&resolved, &hook_namespaces);
            diagnostics.extend(uninterpreted_hook_diagnostics(&resolved, &hook_namespaces));
            diagnostics.extend(super::hook_signatures::collection_hook_misfit_diagnostics(
                &resolved,
                &hook_namespaces,
            ));
            diagnostics.extend(super::hook_signatures::collection_role_misfit_diagnostics(
                &resolved,
                &hook_namespaces,
            ));
            diagnostics
        },
    )));
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err(CompileError::from_diagnostics(
            "hook namespace checks",
            "hook namespace checks failed",
            diagnostics,
        ));
    }
    let (generated, emitted_sources) = stage(timings, emission_phase::EMIT_KORE, || {
        module_to_kore_from_resolved_with_options_and_sources(
            &resolved,
            &definition.main_module,
            ModuleToKoreOptions {
                backend: options.backend,
                generate_map_ceil_axioms: options.backend == CompilationBackend::Rust,
                default_claims_to_all_path: options.default_claims_to_all_path,
                hook_namespaces,
                definition_module: match &options.check_mode {
                    CheckMode::Proof { definition_module } => Some(definition_module.clone()),
                    CheckMode::Definition => None,
                },
            },
        )
    })?;

    let printer = KorePrinter::pretty(options.kore_width);
    let definition_kore = timings.time(emission_phase::PRINT_DEFINITION_KORE, || {
        with_newline(generated.print_semantics_definition(printer))
    });
    let syntax_definition_kore = timings.time(emission_phase::PRINT_SYNTAX_DEFINITION_KORE, || {
        with_newline(generated.print_syntax_definition(printer))
    });
    let macros_kore = timings.time(emission_phase::PRINT_MACROS_KORE, || {
        with_newline(
            generated
                .macros
                .iter()
                .map(|sentence| printer.print_sentence(sentence))
                .collect::<Vec<_>>()
                .join("\n"),
        )
    });
    let sentence_provenance =
        collect_sentence_provenance(&emitted_sources, &execution_definition, loaded)
            .map_err(|message| CompileError::from_error("emitted sentence provenance", message))?;
    Ok(CompiledKoreArtifacts {
        definition_kore,
        syntax_definition_kore,
        macros_kore,
        diagnostics,
        configuration_variables,
        execution_definition,
        execution_rewrite_order,
        sentence_provenance,
    })
}

fn collect_sentence_provenance(
    emitted_sources: &[crate::definition::Attributes],
    execution: &Definition,
    loaded: &LoadedDefinition,
) -> Result<BTreeMap<String, EmittedSentenceProvenance>, String> {
    let mut kinds = loaded.source_table().input_sentence_kinds().clone();
    kinds.extend(input_sentence_kinds(
        loaded.definition(),
        InputSpace::Compile,
    ));
    // Sort injection can replace a generated rule's receipt after the pass that created it.
    // Keep that generating pass from the execution definition, while emission alone selects IDs.
    let mut generating_passes = BTreeMap::new();
    for sentence in execution
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
    {
        if let Sentence::Rule { .. } | Sentence::Claim { .. } = &**sentence
            && let Some(id) = sentence.attributes().string(AttributeKey::UniqueId)
            && let Some(record) = sentence.attributes().origin_record()
        {
            generating_passes.entry(id).or_insert(record.pass);
        }
    }
    let mut relation = BTreeMap::<String, EmittedSentenceProvenance>::new();
    for (index, attributes) in emitted_sources.iter().enumerate() {
        let id = attributes
            .string(AttributeKey::UniqueId)
            .ok_or_else(|| format!("emitted rule or claim at index {index} has no UNIQUE_ID"))?;
        let entry = relation
            .entry(id.to_owned())
            .or_insert_with(|| EmittedSentenceProvenance {
                input_addresses: Vec::new(),
                input_sentence_kinds: BTreeMap::new(),
                generated_by: None,
            });
        for address in attributes.input_addresses() {
            let kind = kinds.get(address).ok_or_else(|| {
                format!("rule or claim {id} names unknown input address {address:?}")
            })?;
            if !entry.input_sentence_kinds.contains_key(address) {
                entry.input_addresses.push(address.clone());
                entry.input_sentence_kinds.insert(address.clone(), *kind);
            }
        }
        if entry.input_addresses.is_empty() {
            entry.generated_by = entry
                .generated_by
                .or(generating_passes.get(id).copied())
                .or(attributes.origin_record().map(|record| record.pass));
        } else {
            entry.generated_by = None;
        }
    }
    for (id, entry) in &relation {
        if entry.input_addresses.is_empty() && entry.generated_by.is_none() {
            return Err(format!(
                "rule or claim {id} has neither input addresses nor a generating pass"
            ));
        }
    }
    Ok(relation)
}

fn collect_execution_rewrite_order(definition: &Definition) -> Result<Vec<String>, String> {
    // stack-accepted(import-chain): one level per module of an import chain; real chains are tens deep, 4,000 modules pass on 8 MiB, and compile time is already about n^1.6. See docs/backend-port.md#stack-bounds.
    // Invariant: `visited` holds the modules whose imports are already ordered, each pushed to `ordered` after its imports, and `visiting` is the current import path, so a name on it closes a cycle; each call that does not return at once moves one module into `visited`, so the module set bounds the calls.
    fn visit<'a>(
        name: &str,
        modules: &BTreeMap<&str, &'a FlatModule>,
        visiting: &mut Vec<&'a str>,
        visited: &mut BTreeSet<&'a str>,
        ordered: &mut Vec<&'a FlatModule>,
    ) -> Result<(), String> {
        if visited.contains(name) {
            return Ok(());
        }
        if let Some(start) = visiting.iter().position(|candidate| *candidate == name) {
            let mut cycle = visiting[start..].to_vec();
            cycle.push(visiting[start]);
            return Err(format!(
                "module import cycle while ordering rewrites: {}",
                cycle.join(" -> ")
            ));
        }
        let module = modules
            .get(name)
            .copied()
            .ok_or_else(|| format!("module {name} not found while ordering rewrites"))?;
        visiting.push(module.name.as_str());
        for import in &module.imports {
            visit(&import.name, modules, visiting, visited, ordered)?;
        }
        visiting.pop();
        visited.insert(module.name.as_str());
        ordered.push(module);
        Ok(())
    }

    struct Occurrence<'a> {
        sentence: &'a Sentence,
        module: &'a str,
        index: usize,
    }

    fn computed_unique_id(sentence: &Sentence) -> String {
        let mut sentence = sentence.clone();
        sentence.attributes_mut().unset(AttributeKey::UniqueId);
        number_sentence(&mut sentence);
        sentence
            .attributes()
            .string(AttributeKey::UniqueId)
            .expect("number_sentence assigns an identifier to every rule")
            .to_owned()
    }

    let modules = definition
        .modules
        .iter()
        .map(|module| (module.name.as_str(), module))
        .collect::<BTreeMap<_, _>>();
    let mut ordered = Vec::new();
    visit(
        &definition.main_module,
        &modules,
        &mut Vec::new(),
        &mut BTreeSet::new(),
        &mut ordered,
    )?;

    let mut occurrences = BTreeMap::<String, Occurrence<'_>>::new();
    let mut rewrite_order = Vec::new();
    // Invariant: `occurrences` maps every UNIQUE_ID of the rules in the modules before `module` (in import order) to its first occurrence, and `rewrite_order` lists those ids once each in first-occurrence order; each module and each of its `local_sentences` is visited once.
    for module in ordered {
        for (index, sentence) in module.local_sentences.iter().enumerate() {
            let Sentence::Rule { attributes, .. } = &**sentence else {
                continue;
            };
            let unique_id = attributes.string(AttributeKey::UniqueId).ok_or_else(|| {
                format!(
                    "transformed rule in module {} at local sentence {index} has no UNIQUE_ID",
                    module.name
                )
            })?;
            if let Some(previous) = occurrences.get(unique_id) {
                if computed_unique_id(previous.sentence) != computed_unique_id(sentence) {
                    return Err(format!(
                        "conflicting rewrite-order UNIQUE_ID {unique_id:?} at module {} local sentence {} and module {} local sentence {index}",
                        previous.module, previous.index, module.name
                    ));
                }
                continue;
            }
            occurrences.insert(
                unique_id.to_owned(),
                Occurrence {
                    sentence,
                    module: &module.name,
                    index,
                },
            );
            rewrite_order.push(unique_id.to_owned());
        }
    }
    Ok(rewrite_order)
}

/// Match `CompiledDefinition.initializeConfigurationVariableDefaultSorts` on the transformed
/// main module, including configuration variables introduced by compiler passes.
pub fn configuration_variables(
    definition: &ResolvedDefinition,
) -> Result<BTreeMap<String, Sort>, String> {
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is not a sentence kind; only the listed variants are special here"
    )]
    fn unwrap_singleton(mut term: &Term) -> &Term {
        loop {
            term = term.unannotated();
            match term {
                Term::Apply { label, arguments }
                    if label.is(WellKnownSymbol::Inj) && arguments.len() == 1 =>
                {
                    term = &arguments[0];
                }
                Term::Sequence(items) if items.len() == 1 => {
                    term = &items[0];
                }
                _ => return term,
            }
        }
    }

    fn lookup_name(term: &Term) -> Option<&str> {
        let term = unwrap_singleton(term);
        let term = match term {
            Term::Apply { label, arguments }
                if label.name == crate::definition::configuration_value::UNBOX_LABEL
                    && label.parameters.is_empty()
                    && arguments.len() == 1 =>
            {
                unwrap_singleton(&arguments[0])
            }
            Term::InjectedLabel(_)
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Variable { .. }
            | Term::Sequence(_)
            | Term::Apply { .. }
            | Term::Token { .. }
            | Term::Annotated { .. } => term,
        };
        let Term::Apply { label, arguments } = term else {
            return None;
        };
        if label.name != "Map:lookup" {
            return None;
        }
        let [_, key] = arguments.as_slice() else {
            return None;
        };
        let Term::Token { token, sort } = unwrap_singleton(key) else {
            return None;
        };
        (sort.name == BuiltinSort::KConfigVar.k_name()).then_some(token.as_str())
    }

    fn is_generic_k(sort: &Sort) -> bool {
        sort.is_builtin(BuiltinSort::K) || sort.is_builtin(BuiltinSort::KItem)
    }

    fn insert_sort(
        sorts: &mut BTreeMap<String, Sort>,
        name: String,
        sort: Sort,
    ) -> Result<(), String> {
        let Some(existing) = sorts.get(&name) else {
            sorts.insert(name, sort);
            return Ok(());
        };
        if existing == &sort {
            return Ok(());
        }
        match (is_generic_k(existing), is_generic_k(&sort)) {
            (true, false) => {
                sorts.insert(name, sort);
                Ok(())
            }
            (false, true) => Ok(()),
            (true, true) => {
                if sort.is_builtin(BuiltinSort::KItem) {
                    sorts.insert(name, sort);
                }
                Ok(())
            }
            (false, false) => Err(format!(
                "configuration variable `${name}` is used at both sort {existing} and {sort}"
            )),
        }
    }

    // Invariant: each call visits one node of `term` and recurses only into its direct subterms, so the finite rule body bounds the calls; `sorts` holds the sort `insert_sort` settled for every configuration variable found so far.
    fn collect(term: &Term, sorts: &mut BTreeMap<String, Sort>) -> Result<(), String> {
        match term.unannotated() {
            Term::Apply { label, arguments } => {
                // The enclosing projection records the declared sort; the decoder's K result
                // only describes the transport payload. A field projection names its field sort.
                let projected = match label.generated() {
                    Some(GeneratedLabel::Projection { sort_text }) => Some(sort_text.to_owned()),
                    Some(GeneratedLabel::FieldProjection { label, field }) => {
                        Some(format!("{label}:{field}"))
                    }
                    _ => None,
                };
                if let Some(projected) = projected
                    && let [argument] = arguments.as_slice()
                    && let Some(name) = lookup_name(argument)
                {
                    insert_sort(
                        sorts,
                        name.strip_prefix('$').unwrap_or(name).to_owned(),
                        Sort::new(projected),
                    )?;
                }
                for argument in arguments {
                    collect(argument, sorts)?;
                }
            }
            Term::Rewrite { left, right } => {
                collect(left, sorts)?;
                collect(right, sorts)?;
            }
            Term::As { pattern, alias } => {
                collect(pattern, sorts)?;
                collect(alias, sorts)?;
            }
            Term::Sequence(items) => {
                for item in items {
                    collect(item, sorts)?;
                }
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!("unannotated terms are matched above"),
        }
        Ok(())
    }

    let mut sorts = BTreeMap::new();
    for sentence in definition.sentences(definition.main_module_id()) {
        if let crate::definition::Sentence::Rule { body, .. } = sentence {
            collect(body, &mut sorts)?;
        }
    }
    Ok(sorts)
}

fn unadmitted_hook_namespace_diagnostics(
    definition: &ResolvedDefinition,
    admitted: &[String],
) -> Vec<Diagnostic> {
    let mut seen = BTreeSet::new();
    let mut diagnostics = Vec::new();
    // Invariant: `diagnostics` has one warning for every (namespace, hook) pair in `seen`, taken from the hooked function productions before `sentence` whose namespace is neither builtin nor in `admitted`; each such production scans `admitted` once.
    for sentence in definition.sentences(definition.main_module_id()) {
        let crate::definition::Sentence::Production { attributes, .. } = sentence else {
            continue;
        };
        if !attributes.has(AttributeKey::Function) {
            continue;
        }
        let Some(hook) = attributes.string(AttributeKey::Hook) else {
            continue;
        };
        let Some((namespace, _)) = hook.split_once('.') else {
            continue;
        };
        if BUILTIN_HOOK_NAMESPACES.contains(&namespace)
            || admitted.iter().any(|candidate| candidate == namespace)
            || !seen.insert((namespace.to_owned(), hook.to_owned()))
        {
            continue;
        }
        diagnostics.push(Diagnostic::warning_at(
            DiagnosticCode::UnadmittedHookNamespace,
            format!(
                "hook namespace `{namespace}` of `hook({hook})` is neither builtin nor selected with --hook-namespaces; the production compiles as an unhooked function"
            ),
            attributes,
        ));
    }
    diagnostics
}

/// One error for every production of the main module that declares a symbol and carries a hook
/// emission would name (its namespace builtin or in `admitted`) without being a `function`.
///
/// A hook names the builtin implementation by which the backend evaluates a function's
/// applications. The symbol of a non-function production is not evaluated: a constructor's
/// applications are values distinct from each other's (`true ~ false` is its own value, while
/// `BOOL.and` would make it `false`), a macro's are replaced by its macro rules, and a bracket's
/// never occur in a term. A hook on such a symbol therefore contradicts the symbol's meaning, and
/// a declaration cannot be both a plain symbol and a hooked one. A production that declares no
/// symbol (a subsort, or an unlabelled token production naming its domain's lexical hook) leaves
/// nothing for the hook to contradict and is accepted, as is a hook whose namespace emission does
/// not name, which compiles as no hook at all.
fn uninterpreted_hook_diagnostics(
    definition: &ResolvedDefinition,
    admitted: &[String],
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    // Invariant: `diagnostics` has one error for every production before `sentence` that declares a symbol, is not a function, and carries a hook whose namespace is builtin or in `admitted`.
    for sentence in definition.sentences(definition.main_module_id()) {
        let Sentence::Production {
            label, attributes, ..
        } = sentence
        else {
            continue;
        };
        if attributes.has(AttributeKey::Function)
            || !is_real_hook(attributes, admitted)
            || !ProductionKind::of(sentence).declares_symbol(label.is_some())
        {
            continue;
        }
        let hook = attributes.string(AttributeKey::Hook).unwrap_or_default();
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::InvalidAttribute,
            format!(
                "hook({hook}) names the builtin implementation of a function, but this production is not a function, so the hook would never evaluate its symbol. Add `function` to the production or remove the hook."
            ),
            sentence,
        ));
    }
    diagnostics
}

fn transform_loaded_definition(
    loaded: &LoadedDefinition,
    options: &CompileOptions,
    timings: &mut PhaseTimings,
    observer: &mut StageObserver<'_>,
) -> Result<(Definition, Definition, Vec<Diagnostic>, ResolvedDefinition), CompileError> {
    let (definition, resolved, diagnostics) = DeepestTerm::of(loaded.definition())
        .run(prologue_phase::DEFINITION_CHECKS, || {
            checked_input(loaded, options, timings)
        })??;

    // Checkpoint: every later transformation receives a resolved, structurally checked definition.
    let mut state = super::pipeline::PipelineState::default();
    let (execution_definition, execution_resolved) =
        super::pipeline::run_stages_seeded_with_resolved(
            super::pipeline::TRANSFORM_STAGES,
            definition,
            &mut state,
            options,
            timings,
            resolved,
            observer,
        )?;
    // Checkpoint: search-pattern compilation and the sentence counter observe this execution
    // definition; injection, unit removal, and construction minimization apply only to emission.
    let (definition, resolved) = super::pipeline::run_stages_seeded_with_resolved(
        super::pipeline::EMISSION_STAGES,
        execution_definition.clone(),
        &mut state,
        options,
        timings,
        execution_resolved,
        observer,
    )?;
    Ok((execution_definition, definition, diagnostics, resolved))
}

/// The prologue of [`transform_loaded_definition`]: the loaded definition with every sentence
/// stamped with its input address, its resolution, and the diagnostics of loading and of the
/// structural checks, which must hold no error.
///
/// This is the input of the first transformation stage.
pub(super) fn checked_input(
    loaded: &LoadedDefinition,
    options: &CompileOptions,
    timings: &mut PhaseTimings,
) -> Result<(Definition, ResolvedDefinition, Vec<Diagnostic>), CompileError> {
    // Every constructor of `LoadedDefinition` establishes these facts; compilation is defined
    // only on values that satisfy them.
    debug_assert!(
        loaded.resolved().modules().count() == loaded.definition().modules.len()
            && loaded.definition().modules.iter().all(|module| {
                loaded.resolved().module_id(&module.name).is_some_and(|id| {
                    loaded.resolved().module(id).local_sentences.len()
                        <= module.local_sentences.len()
                })
            }),
        "LoadedDefinition::resolved is not the resolution of LoadedDefinition::definition"
    );
    debug_assert!(
        loaded.check_stage().is_ok(),
        "a LoadedDefinition is not at the loaded stage"
    );
    // Every sentence the caller handed over is an input sentence: give each one its address in
    // `loaded.definition()` before any pass moves, merges, or derives from it. Only the
    // structured addresses of an unedited `load_structured` result are kept.
    let definition = stage(timings, prologue_phase::STAMP_INPUT_ADDRESSES, || {
        let mut definition = loaded.definition().clone();
        stamp_input_addresses(
            &mut definition,
            InputSpace::Compile,
            loaded.addressing() == InputAddressing::Structured,
        );
        Ok::<_, Infallible>(definition)
    })?;
    // The stamped modules differ from the loaded ones only in their carriers; the update
    // replaces the resolved modules so passes reading sentences through the resolution see the
    // carriers too.
    let resolved = stage(timings, prologue_phase::UPDATE_RESOLUTION, || {
        loaded.resolved().update(loaded.definition(), &definition)
    })?;
    let checked =
        options
            .diagnostics
            .apply(stage(timings, prologue_phase::DEFINITION_CHECKS, || {
                let mut diagnostics = check_definition_with_options(
                    &resolved,
                    options.backend.structural_check_options(
                        options.check_mode.clone(),
                        options.builtin_source_prefixes.clone(),
                    ),
                )?;
                // The main module is the compiled definition here, which programs are read for;
                // a parse module (`kast --module`) is not, so this check is compilation's only.
                diagnostics.extend(check_locations_import(&resolved));
                diagnostics.sort();
                Ok::<_, crate::definition::CheckError>(diagnostics)
            })?);
    let mut diagnostics = loaded.diagnostics().to_vec();
    diagnostics.extend(checked);
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err(CompileError::from_diagnostics(
            "definition checks",
            "definition checks failed",
            diagnostics,
        ));
    }

    Ok((definition, resolved, diagnostics))
}

fn with_newline(mut text: String) -> String {
    if !text.ends_with('\n') {
        text.push('\n');
    }
    text
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use k_rust_backend::definition::BackendDefinition;

    #[test]
    fn configuration_variables_recover_declared_sorts_through_the_transport_decoder() {
        let parsed = crate::outer::parse(
            "configuration.k",
            r#"
            module MAIN
              syntax Val
              configuration <top> <k> $PGM:K </k> <value> $X:Val </value>
                <default> #token("$D", "KConfigVar") </default>
              </top>
            endmodule
        "#,
        )
        .unwrap();
        let lowered = crate::outer::lower(&parsed, "MAIN").unwrap();
        let resolved_bubbles = crate::inner::resolve_configuration_bubbles(&lowered).unwrap();
        let expanded = crate::definition::expand_configurations(&resolved_bubbles).unwrap();
        let resolved = crate::definition::ResolvedDefinition::resolve(&expanded).unwrap();
        assert_eq!(
            super::configuration_variables(&resolved).unwrap(),
            std::collections::BTreeMap::from([
                ("PGM".into(), crate::kast::Sort::new("K")),
                ("X".into(), crate::kast::Sort::new("Val")),
                ("D".into(), crate::kast::Sort::new("KItem")),
            ])
        );
    }

    #[test]
    fn configuration_transport_preserves_specificity_and_conflicting_declared_sorts() {
        let variables = |sorts: &[&str]| {
            let parsed = crate::outer::parse("configuration.k", "module MAIN endmodule").unwrap();
            let mut definition = crate::outer::lower(&parsed, "MAIN").unwrap();
            let truth = || Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            };
            for sort in sorts {
                let lookup = Term::apply(
                    "Map:lookup",
                    vec![
                        Term::Variable {
                            name: "Init".into(),
                            sort: Some(Sort::new("Map")),
                        },
                        Term::Token {
                            token: "$X".into(),
                            sort: Sort::new("KConfigVar"),
                        },
                    ],
                );
                definition.modules[0]
                    .local_sentences
                    .push(Arc::new(Sentence::Rule {
                        body: Term::apply(
                            format!("project:{sort}"),
                            vec![Term::apply(
                                crate::definition::configuration_value::UNBOX_LABEL,
                                vec![lookup],
                            )],
                        ),
                        requires: truth(),
                        ensures: truth(),
                        attributes: Attributes::default(),
                    }));
            }
            let resolved = crate::definition::ResolvedDefinition::resolve(&definition).unwrap();
            super::configuration_variables(&resolved)
        };
        // Imported readers may project one key at several sorts; their order must not change
        // the concrete declaration recovered through the named decoder.
        for sorts in [["K", "KItem", "Val"], ["Val", "KItem", "K"]] {
            assert_eq!(
                variables(&sorts).unwrap(),
                std::collections::BTreeMap::from([("X".into(), crate::kast::Sort::new("Val"))]),
            );
        }
        let error = variables(&["Val", "Other"]).unwrap_err();
        assert!(
            error.contains("configuration variable `$X` is used at both sort"),
            "{error}"
        );
        assert!(error.contains("Val") && error.contains("Other"), "{error}");
    }

    #[test]
    fn configuration_variables_only_unwrap_the_named_transport_decoder() {
        let token = Term::Token {
            token: "$X".into(),
            sort: crate::kast::Sort::new("KConfigVar"),
        };
        let lookup = Term::apply("Map:lookup", vec![Term::variable("Init"), token]);
        let read = Term::apply(
            "project:K",
            vec![Term::apply("foreignDecoder", vec![lookup])],
        );
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: vec![],
                attributes: Attributes::default(),
                local_sentences: vec![Arc::new(Sentence::Rule {
                    body: read,
                    requires: Term::Token {
                        token: "true".into(),
                        sort: crate::kast::Sort::new("Bool"),
                    },
                    ensures: Term::Token {
                        token: "true".into(),
                        sort: crate::kast::Sort::new("Bool"),
                    },
                    attributes: Attributes::default(),
                })],
            }],
            attributes: Attributes::default(),
        };
        let resolved = crate::definition::ResolvedDefinition::resolve(&definition).unwrap();
        assert!(
            super::configuration_variables(&resolved)
                .unwrap()
                .is_empty()
        );
    }

    #[cfg(feature = "z3-inference")]
    use crate::{
        builtin::embedded,
        outer::{LoadOptions, load_with_options},
    };
    use crate::{
        definition::{Attributes, Definition, FlatImport, FlatModule, Sentence},
        kast::Term,
        kore::parser::parse_definition,
        outer::{ResolvedSource, load},
    };
    #[cfg(feature = "z3-inference")]
    use sha3::{Digest, Sha3_256};

    use super::*;

    fn ranked_rule(unique_id: Option<&str>, body_label: &str) -> Sentence {
        let mut attributes = Attributes::default();
        if let Some(unique_id) = unique_id {
            attributes.insert("UNIQUE_ID", serde_json::json!(unique_id));
        }
        Sentence::Rule {
            body: Term::apply(body_label, Vec::new()),
            requires: Term::apply("#Top", Vec::new()),
            ensures: Term::apply("#Top", Vec::new()),
            attributes,
        }
    }

    fn ranked_module(name: &str, imports: &[&str], rules: &[(Option<&str>, &str)]) -> FlatModule {
        FlatModule {
            name: name.into(),
            imports: imports
                .iter()
                .map(|name| FlatImport {
                    name: (*name).into(),
                    public: false,
                })
                .collect(),
            local_sentences: rules
                .iter()
                .map(|(unique_id, body)| Arc::new(ranked_rule(*unique_id, body)))
                .collect(),
            attributes: Attributes::default(),
        }
    }

    #[test]
    fn execution_rewrite_order_follows_import_and_local_sentence_order() {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![
                ranked_module(
                    "MAIN",
                    &["LEFT", "RIGHT"],
                    &[
                        (Some("main-first"), "mainFirst"),
                        (Some("main-second"), "mainSecond"),
                    ],
                ),
                ranked_module(
                    "RIGHT",
                    &["BASE"],
                    &[(Some("base"), "base"), (Some("right"), "right")],
                ),
                ranked_module(
                    "LEFT",
                    &["BASE"],
                    &[
                        (Some("left-first"), "leftFirst"),
                        (Some("left-second"), "leftSecond"),
                    ],
                ),
                ranked_module("BASE", &[], &[(Some("base"), "base")]),
            ],
            attributes: Attributes::default(),
        };

        assert_eq!(
            collect_execution_rewrite_order(&definition).unwrap(),
            [
                "base",
                "left-first",
                "left-second",
                "right",
                "main-first",
                "main-second",
            ]
        );
    }

    #[test]
    fn execution_rewrite_order_rejects_conflicting_duplicate_ids() {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![ranked_module(
                "MAIN",
                &[],
                &[(Some("duplicate"), "first"), (Some("duplicate"), "second")],
            )],
            attributes: Attributes::default(),
        };

        let error = collect_execution_rewrite_order(&definition).unwrap_err();
        assert!(
            error.contains("module MAIN local sentence 0 and module MAIN local sentence 1"),
            "{error}"
        );
    }

    #[test]
    fn execution_rewrite_order_reports_missing_ids_at_their_source_position() {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![ranked_module("MAIN", &[], &[(None, "missing")])],
            attributes: Attributes::default(),
        };

        assert_eq!(
            collect_execution_rewrite_order(&definition).unwrap_err(),
            "transformed rule in module MAIN at local sentence 0 has no UNIQUE_ID"
        );
    }

    #[test]
    fn standalone_compilation_emits_verifiable_sort_predicates() {
        for bool_syntax in ["", "syntax Bool", "syntax Bool [token]"] {
            let source = format!(
                r#"module MAIN
                  {bool_syntax}
                  syntax State ::= "a" [function, symbol(a)] | "b" [symbol(b)]
                  rule a => b
                endmodule"#
            );
            let loaded = load(
                ResolvedSource::new("standalone.k", source),
                "MAIN",
                &mut |_: &str, required: &str| Err(format!("unexpected require {required}")),
            )
            .unwrap();
            let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
            for text in [
                &artifacts.definition_kore,
                &artifacts.syntax_definition_kore,
            ] {
                let kore = parse_definition(text).unwrap();
                BackendDefinition::internalize(&kore, "MAIN")
                    .expect("standalone KORE must satisfy the backend's definition contract");
            }
        }
    }

    /// The fresh counter cell holds an `Int`; a definition whose main module sees no `Int`
    /// (none declared, or declared only in a module the main module does not import) has no
    /// counter cell, so its KORE declares no symbol over an undeclared sort and the backend
    /// accepts it. A claim over its configuration gets no counter cell either.
    #[test]
    fn a_configuration_without_int_compiles_without_a_counter_cell() {
        for (int_module, check_mode, sentence) in [
            ("", CheckMode::Definition, "rule <mem> a => b </mem>"),
            (
                r#"module INT syntax Int ::= r"[0-9]+" [token] endmodule"#,
                CheckMode::Definition,
                "rule <mem> a => b </mem>",
            ),
            (
                "",
                CheckMode::Proof {
                    definition_module: "MAIN".into(),
                },
                "claim <mem> a => b </mem>",
            ),
        ] {
            let source = format!(
                r#"{int_module}
                module MAIN
                  syntax K
                  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)]
                  configuration <t> <k> .K </k> <mem> a </mem> </t>
                  {sentence}
                endmodule"#
            );
            let loaded = load(
                ResolvedSource::new("no-int.k", source),
                "MAIN",
                &mut |_: &str, required: &str| Err(format!("unexpected require {required}")),
            )
            .unwrap();
            let artifacts = compile_loaded_definition(
                &loaded,
                CompileOptions {
                    check_mode: check_mode.clone(),
                    ..CompileOptions::default()
                },
            )
            .unwrap();
            assert!(
                !artifacts.definition_kore.contains("generatedCounter"),
                "{int_module} {sentence}\n{}",
                artifacts.definition_kore
            );
            assert!(
                artifacts
                    .definition_kore
                    .contains("symbol Lbl'-LT-'generatedTop'-GT-'{}(SortTCell{})"),
                "{}",
                artifacts.definition_kore
            );
            let kore = parse_definition(&artifacts.definition_kore).unwrap();
            BackendDefinition::internalize(&kore, "MAIN")
                .expect("KORE without a counter cell must satisfy the backend's contract");
        }
    }

    #[cfg(feature = "z3-inference")]
    fn artifact_digest(text: &str) -> String {
        Sha3_256::digest(text.as_bytes())
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn provenance_plumbing_leaves_emitted_kore_unchanged() {
        let source = r#"
            module MAIN
              imports MAP
              syntax Int ::= r"[0-9]+" [token]
              syntax Exp ::= Int
              syntax Exp ::= Exp "+" Exp [symbol(_+_)]
              configuration <k> $PGM:Exp </k> <n> 0:KItem </n>
              rule <k> X:Exp + 0 => X:Exp </k> [label(right-zero)]
              claim <k> X:Exp => X:Exp </k> [one-path, label(reflexive)]
            endmodule
        "#;
        let prelude = embedded("prelude.md").unwrap();
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("provenance.k", source),
            "MAIN",
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![prelude],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .unwrap();

        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                check_mode: CheckMode::Proof {
                    definition_module: "MAIN".into(),
                },
                ..CompileOptions::default()
            },
        )
        .unwrap();

        assert_eq!(
            [
                artifact_digest(&artifacts.definition_kore),
                artifact_digest(&artifacts.syntax_definition_kore),
                artifact_digest(&artifacts.macros_kore),
            ],
            [
                String::from("87b64f6846b14b122a51ca14dad17337b98dafe78b01bcf83bc63c77e2c4b6a0",),
                String::from("aee6149a0ece4bad3ea72d9e254b795eb378eed7aa7d304bcd1b7d9b6f76c847",),
                String::from("a78f2c566b2439463a2e7ca515bbfa3f92948506583cbadaebdd507f277542bd",),
            ],
        );
    }

    fn origin_receipts(definition: &Definition) -> Vec<serde_json::Value> {
        fn collect_term(term: &Term, receipts: &mut Vec<serde_json::Value>) {
            if let Some(origin) = term
                .metadata()
                .and_then(|metadata| metadata.origin.as_deref())
            {
                receipts.push(origin.to_value());
            }
            match term.unannotated() {
                Term::Rewrite { left, right } => {
                    collect_term(left, receipts);
                    collect_term(right, receipts);
                }
                Term::As { pattern, alias } => {
                    collect_term(pattern, receipts);
                    collect_term(alias, receipts);
                }
                Term::Sequence(items)
                | Term::Apply {
                    arguments: items, ..
                } => {
                    for item in items {
                        collect_term(item, receipts);
                    }
                }
                Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
                Term::Annotated { .. } => unreachable!(),
            }
        }

        let mut receipts = Vec::new();
        for sentence in definition
            .modules
            .iter()
            .flat_map(|module| &module.local_sentences)
        {
            if let Some(receipt) = sentence
                .attributes()
                .get(crate::provenance::ORIGIN_ATTRIBUTE)
            {
                receipts.push(receipt.clone());
            }
            for (_, term) in sentence.terms() {
                collect_term(term, &mut receipts);
            }
        }
        receipts
    }

    #[test]
    fn origin_records_are_deterministic_across_compiles() {
        let source = r#"
            module MAIN
              syntax Exp ::= "a" [symbol(a)]
                           | "b" [symbol(b)]
                           | "m(" Exp ")" [macro, symbol(m)]
              rule m(_X:Exp) => b
              rule m(a) => a [label(subject)]
            endmodule
        "#;
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
        let loaded = load(
            ResolvedSource::new("determinism.k", source),
            "MAIN",
            &mut resolver,
        )
        .unwrap();
        let options = CompileOptions::default();

        let (_, first, _, _) = transform_loaded_definition(
            &loaded,
            &options,
            &mut PhaseTimings::default(),
            &mut |_, _, _| {},
        )
        .unwrap();
        let (_, second, _, _) = transform_loaded_definition(
            &loaded,
            &options,
            &mut PhaseTimings::default(),
            &mut |_, _, _| {},
        )
        .unwrap();
        let first = origin_receipts(&first);
        let second = origin_receipts(&second);

        assert!(!first.is_empty());
        assert_eq!(first, second);
    }

    #[test]
    fn compiles_an_in_memory_definition_into_three_artifacts() {
        let source = r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax Exp ::= Int
            endmodule
        "#;
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
        let loaded = load(
            ResolvedSource::new("definition.k", source),
            "MAIN",
            &mut resolver,
        )
        .unwrap();

        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
        assert!(parse_definition(&artifacts.definition_kore).is_ok());
        assert!(parse_definition(&artifacts.syntax_definition_kore).is_ok());
        assert_eq!(artifacts.macros_kore, "\n");
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn configuration_variables_include_stream_variables() {
        let source = include_str!("../../tests/fixtures/reference/cli/io/io.k");
        let prelude = embedded("prelude.md").unwrap();
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("io.k", source),
            "IO",
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![prelude],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .unwrap();

        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
        assert_eq!(
            artifacts.configuration_variables,
            BTreeMap::from([
                ("IO".into(), crate::kast::Sort::new("String")),
                ("PGM".into(), crate::kast::Sort::new("Int")),
                ("STDIN".into(), crate::kast::Sort::new("String")),
            ])
        );
    }

    #[test]
    fn parses_backend_names() {
        assert_eq!("llvm".parse(), Ok(CompilationBackend::Llvm));
        assert_eq!("rust".parse(), Ok(CompilationBackend::Rust));
        assert_eq!("haskell".parse(), Ok(CompilationBackend::Rust));
        assert!("nope".parse::<CompilationBackend>().is_err());
        for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
            assert_eq!(backend.to_string().parse(), Ok(backend));
        }
    }

    #[test]
    fn rust_backend_emits_its_extension_hooks_as_hooked_symbols() {
        let source = r#"
            module MAIN
              syntax Value
              syntax Value ::= "krypto" [function, hook(KRYPTO.keccak256), symbol(krypto)]
                             | "hash" [function, hook(HASH.sha256), symbol(hash)]
                             | "secp256k1" [function, hook(SECP256K1.ecdsaRecover), symbol(secp256k1)]
            endmodule
        "#;
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
        let loaded = load(
            ResolvedSource::new("definition.k", source),
            "MAIN",
            &mut resolver,
        )
        .unwrap();

        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();

        for (symbol, hook) in [
            ("krypto", "KRYPTO.keccak256"),
            ("hash", "HASH.sha256"),
            ("secp256k1", "SECP256K1.ecdsaRecover"),
        ] {
            let symbol = crate::kompile::encode_kore_label(&crate::kast::Label::new(symbol)).name;
            assert!(
                artifacts
                    .definition_kore
                    .contains(&format!("hooked-symbol {symbol}")),
                "{symbol} was not emitted as a hooked symbol:\n{}",
                artifacts.definition_kore,
            );
            assert!(
                artifacts
                    .definition_kore
                    .contains(&format!(r#"hook{{}}("{hook}")"#)),
                "{symbol} did not retain its {hook} attribute",
            );
        }
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn emitted_symbolic_kore_internalizes_in_process() {
        let source = r#"
            module MAIN
              imports MAP
              syntax Int ::= r"[0-9]+" [token]
              syntax Exp ::= Int
              syntax Exp ::= Exp "+" Exp [symbol(_+_)]
              configuration <k> $PGM:Exp </k> <n> 0:KItem </n>
              rule <k> X:Exp + 0 => X:Exp </k> [label(right-zero)]
              claim <k> X:Exp => X:Exp </k> [one-path, label(reflexive)]
            endmodule
        "#;
        let prelude = embedded("prelude.md").unwrap();
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("definition.k", source),
            "MAIN",
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![prelude],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .unwrap();
        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                backend: CompilationBackend::Rust,
                check_mode: CheckMode::Proof {
                    definition_module: "MAIN".into(),
                },
                ..CompileOptions::default()
            },
        )
        .unwrap();
        let kore = parse_definition(&artifacts.definition_kore).unwrap();

        let backend = BackendDefinition::internalize(&kore, "MAIN")
            .expect("frontend KORE should internalize into the in-process backend");
        assert!(!backend.rewrite_theory().is_empty());
        assert_eq!(backend.reachability_claims().len(), 1);
        let input_claim = loaded
            .definition()
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .position(|sentence| matches!(**sentence, Sentence::Claim { .. }))
            .unwrap();
        let claim = artifacts
            .execution_definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find(|sentence| matches!(***sentence, Sentence::Claim { .. }))
            .unwrap();
        let id = claim.attributes().string(AttributeKey::UniqueId).unwrap();
        let address = InputAddress::new(
            InputSpace::Compile,
            "MAIN",
            u32::try_from(input_claim).unwrap(),
        );
        let provenance = &artifacts.sentence_provenance[id];
        assert_eq!(provenance.input_addresses, std::slice::from_ref(&address));
        assert_eq!(
            provenance.input_sentence_kinds[&address],
            InputSentenceKind::Claim
        );
    }
}
