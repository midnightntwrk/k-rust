//! Table-driven execution support for definition transformation passes.
//!
//! ```toml algorithm-contract
//! id = "contract.kompile.resolved_cache"
//! name = "lazy resolution shared by kompile stages"
//! sites = ["PassInput::resolved_raw"]
//! constrains = [{ id = "definition.resolve.imports", site = "PassInput::resolved_raw", via = "Current.resolved is forced once and ResolvedDefinition::update propagates the cached resolution between stages" }]
//! ```

use std::{convert::Infallible, fmt};

use k_rust_kore::measure;

use crate::{
    definition::{Definition, ProductionCatalog, ResolveError, ResolvedDefinition, Sentence},
    diagnostic::Diagnostic,
    kast::Term,
    provenance::{GeneratingPass, record_generated_origins},
    timings::PhaseTimings,
};

use super::{CompileError, CompileOptions};
use super::{passes, sort_injections};

/// Names recorded while loading a definition for `kcompile`, in execution order.
///
/// The first two entries are alternative entry phases: source compilation records
/// [`load_phase::RESOLVE_ENTRY_SOURCE`], while compilation against a prepared definition records
/// [`load_phase::READ_PREPARED_DEFINITION`].
pub static LOAD_PHASES: &[&str] = &[
    load_phase::RESOLVE_ENTRY_SOURCE,
    load_phase::READ_PREPARED_DEFINITION,
    load_phase::PARSE_SOURCES,
    load_phase::SELECT_SOURCE_FILES,
    load_phase::LOWER_FILES,
    load_phase::APPLY_SORT_SYNONYMS,
    load_phase::CHECK_OUTER_MODULES,
    load_phase::SELECT_MODULES,
    load_phase::RESOLVE_CONFIGURATION_BUBBLES,
    load_phase::EXPAND_CONFIGURATIONS,
    load_phase::RESOLVE_AND_CHECK_SORTS,
    load_phase::RESOLVE_RULE_BUBBLES,
    load_phase::RESOLVE_RULE_BUBBLES_GRAMMARS,
    load_phase::RESOLVE_RULE_BUBBLES_PARSE,
];

/// Named entries of [`LOAD_PHASES`] for timing sites.
pub mod load_phase {
    pub const RESOLVE_ENTRY_SOURCE: &str = "resolve entry source";
    pub const READ_PREPARED_DEFINITION: &str = "read prepared definition";
    pub const PARSE_SOURCES: &str = "parse sources";
    pub const SELECT_SOURCE_FILES: &str = "select source files";
    pub const LOWER_FILES: &str = "lower files";
    pub const APPLY_SORT_SYNONYMS: &str = "apply sort synonyms";
    pub const CHECK_OUTER_MODULES: &str = "check outer modules";
    pub const SELECT_MODULES: &str = "select modules";
    pub const RESOLVE_CONFIGURATION_BUBBLES: &str = "resolve configuration bubbles";
    pub const EXPAND_CONFIGURATIONS: &str = "expand configurations";
    pub const RESOLVE_AND_CHECK_SORTS: &str = "resolve and check sorts";
    pub const RESOLVE_RULE_BUBBLES: &str = "resolve rule bubbles";
    pub const RESOLVE_RULE_BUBBLES_GRAMMARS: &str = "resolve rule bubbles / grammars";
    pub const RESOLVE_RULE_BUBBLES_PARSE: &str = "resolve rule bubbles / parse";
}

/// Names recorded after the table-driven transformation stages, in execution order.
///
/// [`emission_phase::GENERATE_BISON_PARSER`] is optional and is recorded immediately before the
/// final artifact-write phase when requested.
pub static EMISSION_PHASES: &[&str] = &[
    emission_phase::COLLECT_EXECUTION_REWRITE_ORDER,
    emission_phase::RESOLVE_TRANSFORMED_DEFINITION,
    emission_phase::SINGLETON_OVERLOAD_CHECKS,
    emission_phase::COLLECT_CONFIGURATION_VARIABLES,
    emission_phase::HOOK_NAMESPACE_CHECKS,
    emission_phase::EMIT_KORE,
    emission_phase::PRINT_DEFINITION_KORE,
    emission_phase::PRINT_SYNTAX_DEFINITION_KORE,
    emission_phase::PRINT_MACROS_KORE,
    emission_phase::GENERATE_BISON_PARSER,
    emission_phase::WRITE_ARTIFACTS,
];

/// Named entries of [`EMISSION_PHASES`] for timing sites.
pub mod emission_phase {
    pub const COLLECT_EXECUTION_REWRITE_ORDER: &str = "collect execution rewrite order";
    pub const RESOLVE_TRANSFORMED_DEFINITION: &str = "resolve transformed definition";
    pub const SINGLETON_OVERLOAD_CHECKS: &str = "singleton overload checks";
    pub const COLLECT_CONFIGURATION_VARIABLES: &str = "collect configuration variables";
    pub const HOOK_NAMESPACE_CHECKS: &str = "hook namespace checks";
    pub const EMIT_KORE: &str = "emit KORE";
    pub const PRINT_DEFINITION_KORE: &str = "print definition.kore";
    pub const PRINT_SYNTAX_DEFINITION_KORE: &str = "print syntaxDefinition.kore";
    pub const PRINT_MACROS_KORE: &str = "print macros.kore";
    pub const GENERATE_BISON_PARSER: &str = "generate bison parser";
    pub const WRITE_ARTIFACTS: &str = "write artifacts";
}

/// Names recorded before the table-driven transformation stages.
pub mod prologue_phase {
    pub const EXPAND_STRUCTURED_CONFIGURATIONS: &str = "expand structured configurations";
    pub const RESOLVE_STRUCTURED_CONFIGURATIONS: &str = "resolve structured configurations";
    pub const DEFINITION_CHECKS: &str = "definition checks";
}

/// The common error carried across a pipeline stage boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PassError {
    pub message: String,
    pub diagnostics: Vec<Diagnostic>,
}

impl PassError {
    pub(crate) fn message(error: impl fmt::Display) -> Self {
        Self {
            message: error.to_string(),
            diagnostics: Vec::new(),
        }
    }
}

impl From<String> for PassError {
    fn from(message: String) -> Self {
        Self {
            message,
            diagnostics: Vec::new(),
        }
    }
}

impl From<ResolveError> for PassError {
    fn from(error: ResolveError) -> Self {
        Self::message(error)
    }
}

impl From<Infallible> for PassError {
    fn from(error: Infallible) -> Self {
        match error {}
    }
}

macro_rules! diagnostics_error {
    ($($error:path),+ $(,)?) => {$ (
        impl From<$error> for PassError {
            fn from(error: $error) -> Self {
                Self {
                    message: error.to_string(),
                    diagnostics: error.diagnostics,
                }
            }
        }
    )+ };
}

diagnostics_error!(
    super::ResolveCommError,
    super::ResolveIoError,
    super::ResolveFunError,
    super::ResolveFunctionWithConfigError,
    super::ResolveStrictError,
    super::ResolveContextsError,
    super::ResolveHeatCoolError,
    super::ResolveSemanticCastsError,
    super::ConstantFoldingError,
    super::ResolveFreshConfigConstantsError,
    super::ResolveFreshConstantsError,
    super::ExpandMacrosError,
    super::AddImplicitComputationCellError,
    super::RemoveUnitError,
    super::GuardOrPatternsError,
    super::CheckSimplificationError,
    super::ConcretizeCellsError,
);

macro_rules! display_error {
    ($($error:path),+ $(,)?) => {$ (
        impl From<$error> for PassError {
            fn from(error: $error) -> Self {
                Self::message(error)
            }
        }
    )+ };
}

display_error!(
    super::SubsortKItemError,
    super::SortInjectionError,
    super::TermConversionError,
);

/// Data produced by one stage for a later stage.
#[derive(Default)]
pub(crate) struct PipelineState {
    pub fresh_config_count: Option<usize>,
}

struct Current {
    definition: Definition,
    resolved: std::sync::OnceLock<Result<ResolvedDefinition, ResolveError>>,
}

impl Current {
    fn new(definition: Definition) -> Self {
        Self {
            definition,
            resolved: std::sync::OnceLock::new(),
        }
    }

    #[cfg(test)]
    fn into_definition(self) -> Definition {
        self.definition
    }

    fn into_definition_and_resolved(
        self,
        stage: &'static str,
    ) -> Result<(Definition, ResolvedDefinition), CompileError> {
        let Current {
            definition,
            resolved,
        } = self;
        let resolved = resolved
            .into_inner()
            .expect("pipeline current should have a resolution slot")
            .map_err(|error| CompileError {
                stage,
                message: error.to_string(),
                diagnostics: Vec::new(),
            })?;
        Ok((definition, resolved))
    }

    fn with_resolved(definition: Definition, resolved: ResolvedDefinition) -> Self {
        let current = Self::new(definition);
        let _ = current.resolved.set(Ok(resolved));
        current
    }
}

/// The immutable input and lazily resolved views for one stage.
pub(crate) struct PassInput<'a> {
    pub definition: &'a Definition,
    current: &'a Current,
}

impl<'a> PassInput<'a> {
    fn new(current: &'a Current) -> Self {
        Self {
            definition: &current.definition,
            current,
        }
    }

    pub(crate) fn resolved_raw(&self) -> Result<&ResolvedDefinition, &ResolveError> {
        self.current
            .resolved
            .get_or_init(|| ResolvedDefinition::resolve(self.definition))
            .as_ref()
    }
}

pub(crate) type PassFn = fn(&PassInput<'_>, &mut PipelineState) -> Result<Definition, PassError>;

#[derive(Clone, Copy)]
pub(crate) enum Provenance {
    None,
    Driver(GeneratingPass),
    Internal(&'static [GeneratingPass]),
}

pub(crate) struct Stage {
    pub name: &'static str,
    pub call: &'static str,
    pub run: PassFn,
    pub provenance: Provenance,
    pub behavior: &'static str,
}

macro_rules! stage_adapter {
    ($name:ident, $pass:path) => {
        fn $name(
            input: &PassInput<'_>,
            state: &mut PipelineState,
        ) -> Result<Definition, PassError> {
            $pass(input, state).map_err(Into::into)
        }
    };
}

stage_adapter!(resolve_comm_stage, passes::resolve_comm_pass);
stage_adapter!(resolve_io_stage, passes::resolve_io_pass);
stage_adapter!(resolve_fun_stage, passes::resolve_fun_pass);
stage_adapter!(
    generate_sort_predicate_syntax_stage,
    passes::generate_sort_predicate_syntax_pass
);
stage_adapter!(
    resolve_function_with_config_stage,
    passes::resolve_function_with_config_pass
);
stage_adapter!(resolve_strict_stage, passes::resolve_strict_pass);
stage_adapter!(resolve_anon_vars_stage, passes::resolve_anon_vars_pass);
stage_adapter!(resolve_contexts_stage, passes::resolve_contexts_pass);
stage_adapter!(number_sentences_stage, passes::number_sentences_pass);
stage_adapter!(
    resolve_heat_cool_attributes_stage,
    passes::resolve_heat_cool_attributes_pass
);
stage_adapter!(
    resolve_semantic_casts_stage,
    passes::resolve_semantic_casts_pass
);
stage_adapter!(subsort_kitem_stage, passes::subsort_kitem_pass);
stage_adapter!(constant_fold_stage, passes::constant_fold_pass);
stage_adapter!(
    propagate_macro_attributes_stage,
    passes::propagate_macro_attributes_pass
);
stage_adapter!(guard_or_patterns_stage, passes::guard_or_patterns_pass);
stage_adapter!(
    generate_sort_projections_stage,
    passes::generate_sort_projections_pass
);
stage_adapter!(expand_macros_stage, passes::expand_macros_pass);
stage_adapter!(
    add_implicit_computation_cell_stage,
    passes::add_implicit_computation_cell_pass
);
stage_adapter!(
    resolve_fresh_constants_stage,
    passes::resolve_fresh_constants_pass
);
stage_adapter!(
    regenerate_sort_predicate_syntax_stage,
    passes::regenerate_sort_predicate_syntax_pass
);
stage_adapter!(
    check_simplification_rules_stage,
    passes::check_simplification_rules_pass
);
stage_adapter!(concretize_cells_stage, passes::concretize_cells_pass);
stage_adapter!(
    add_semantics_module_stage,
    passes::add_semantics_module_pass
);
stage_adapter!(resolve_config_var_stage, passes::resolve_config_var_pass);
stage_adapter!(
    add_cool_like_attributes_stage,
    passes::add_cool_like_attributes_pass
);
stage_adapter!(
    generate_sort_predicate_rules_stage,
    passes::generate_sort_predicate_rules_pass
);
stage_adapter!(
    add_sort_injections_to_definition_stage,
    sort_injections::add_sort_injections_to_definition_pass
);
stage_adapter!(remove_unit_stage, passes::remove_unit_pass);
stage_adapter!(
    minimize_term_construction_stage,
    passes::minimize_term_construction_pass
);

fn resolve_fresh_config_constants_stage(
    input: &PassInput<'_>,
    state: &mut PipelineState,
) -> Result<Definition, PassError> {
    passes::resolve_fresh_config_constants_pass(input, state)
        .map(|(definition, _)| definition)
        .map_err(Into::into)
}

const PREDICATE_SYNTAX_INTERNAL: &[GeneratingPass] = &[GeneratingPass::GenerateSortPredicateSyntax];

macro_rules! stage {
    ($name:literal, $call:literal, $run:ident, $provenance:expr, $behavior:literal) => {
        Stage {
            name: $name,
            call: $call,
            run: $run,
            provenance: $provenance,
            behavior: $behavior,
        }
    };
}

pub(crate) static TRANSFORM_STAGES: &[Stage] = &[
    stage!(
        "resolve commutative rules",
        "resolve_comm",
        resolve_comm_stage,
        Provenance::Driver(GeneratingPass::ResolveComm),
        "generating"
    ),
    stage!(
        "resolve I/O streams",
        "resolve_io",
        resolve_io_stage,
        Provenance::Driver(GeneratingPass::ResolveIo),
        "generating"
    ),
    stage!(
        "resolve local functions",
        "resolve_fun",
        resolve_fun_stage,
        Provenance::Driver(GeneratingPass::ResolveFun),
        "generating"
    ),
    stage!(
        "seed sort predicate syntax",
        "generate_sort_predicate_syntax",
        generate_sort_predicate_syntax_stage,
        Provenance::Driver(GeneratingPass::GenerateSortPredicateSyntax),
        "generating"
    ),
    stage!(
        "resolve function configuration",
        "resolve_function_with_config",
        resolve_function_with_config_stage,
        Provenance::Driver(GeneratingPass::ResolveFunctionWithConfig),
        "generating"
    ),
    stage!(
        "resolve strictness",
        "resolve_strict",
        resolve_strict_stage,
        Provenance::Driver(GeneratingPass::ResolveStrict),
        "generating"
    ),
    stage!(
        "resolve anonymous variables",
        "resolve_anon_vars",
        resolve_anon_vars_stage,
        Provenance::Driver(GeneratingPass::ResolveAnonymousVariables),
        "generating"
    ),
    stage!(
        "resolve contexts",
        "resolve_contexts",
        resolve_contexts_stage,
        Provenance::Driver(GeneratingPass::ResolveContexts),
        "generating"
    ),
    stage!(
        "number sentences",
        "number_sentences",
        number_sentences_stage,
        Provenance::None,
        "metadata-only"
    ),
    stage!(
        "resolve heat/cool attributes",
        "resolve_heat_cool_attributes",
        resolve_heat_cool_attributes_stage,
        Provenance::Driver(GeneratingPass::ResolveHeatCool),
        "generating"
    ),
    stage!(
        "resolve semantic casts",
        "resolve_semantic_casts",
        resolve_semantic_casts_stage,
        Provenance::Driver(GeneratingPass::SemanticCasts),
        "generating"
    ),
    stage!(
        "add KItem subsorts",
        "subsort_kitem",
        subsort_kitem_stage,
        Provenance::Driver(GeneratingPass::SubsortKItem),
        "generating"
    ),
    stage!(
        "constant folding",
        "constant_fold",
        constant_fold_stage,
        Provenance::Driver(GeneratingPass::ConstantFolding),
        "generating"
    ),
    stage!(
        "propagate macro attributes",
        "propagate_macro_attributes",
        propagate_macro_attributes_stage,
        Provenance::None,
        "metadata-only"
    ),
    stage!(
        "guard or-patterns",
        "guard_or_patterns",
        guard_or_patterns_stage,
        Provenance::Driver(GeneratingPass::GuardOrPatterns),
        "generating"
    ),
    stage!(
        "resolve fresh configuration constants",
        "resolve_fresh_config_constants",
        resolve_fresh_config_constants_stage,
        Provenance::Driver(GeneratingPass::ResolveFreshConfigConstants),
        "generating"
    ),
    stage!(
        "generate sort predicate syntax",
        "generate_sort_predicate_syntax",
        generate_sort_predicate_syntax_stage,
        Provenance::Driver(GeneratingPass::GenerateSortPredicateSyntax),
        "generating"
    ),
    stage!(
        "generate sort projections",
        "generate_sort_projections",
        generate_sort_projections_stage,
        Provenance::Driver(GeneratingPass::GenerateSortProjections),
        "generating"
    ),
    stage!(
        "expand macros",
        "expand_macros",
        expand_macros_stage,
        Provenance::Driver(GeneratingPass::MacroExpansion),
        "generating"
    ),
    stage!(
        "add implicit computation cell",
        "add_implicit_computation_cell",
        add_implicit_computation_cell_stage,
        Provenance::Driver(GeneratingPass::AddImplicitComputationCell),
        "generating"
    ),
    stage!(
        "resolve fresh constants",
        "resolve_fresh_constants",
        resolve_fresh_constants_stage,
        Provenance::Driver(GeneratingPass::ResolveFreshConstants),
        "generating"
    ),
    stage!(
        "regenerate sort predicate syntax",
        "regenerate_sort_predicate_syntax",
        regenerate_sort_predicate_syntax_stage,
        Provenance::Internal(PREDICATE_SYNTAX_INTERNAL),
        "metadata-only"
    ),
    stage!(
        "regenerate sort projections",
        "generate_sort_projections",
        generate_sort_projections_stage,
        Provenance::Driver(GeneratingPass::GenerateSortProjections),
        "generating"
    ),
    stage!(
        "check simplification rules",
        "check_simplification_rules",
        check_simplification_rules_stage,
        Provenance::None,
        "validation"
    ),
    stage!(
        "finalize KItem subsorts",
        "subsort_kitem",
        subsort_kitem_stage,
        Provenance::Driver(GeneratingPass::SubsortKItem),
        "generating"
    ),
    stage!(
        "concretize cells",
        "concretize_cells",
        concretize_cells_stage,
        Provenance::Driver(GeneratingPass::ConcretizeCells),
        "generating"
    ),
    stage!(
        "add semantics module",
        "add_semantics_module",
        add_semantics_module_stage,
        Provenance::None,
        "structural-origin-free"
    ),
    stage!(
        "resolve configuration variables",
        "resolve_config_var",
        resolve_config_var_stage,
        Provenance::Driver(GeneratingPass::ResolveFunctionWithConfig),
        "generating"
    ),
    stage!(
        "add cool-like attributes",
        "add_cool_like_attributes",
        add_cool_like_attributes_stage,
        Provenance::None,
        "metadata-only"
    ),
    stage!(
        "generate sort predicate rules",
        "generate_sort_predicate_rules",
        generate_sort_predicate_rules_stage,
        Provenance::Driver(GeneratingPass::GenerateSortPredicateRules),
        "generating"
    ),
    stage!(
        "number sentences (final)",
        "number_sentences",
        number_sentences_stage,
        Provenance::None,
        "metadata-only"
    ),
];

pub(crate) static EMISSION_STAGES: &[Stage] = &[
    stage!(
        "add sort injections",
        "add_sort_injections_to_definition",
        add_sort_injections_to_definition_stage,
        Provenance::Driver(GeneratingPass::AddSortInjections),
        "generating"
    ),
    stage!(
        "remove units",
        "remove_unit",
        remove_unit_stage,
        Provenance::Driver(GeneratingPass::RemoveUnit),
        "generating"
    ),
    stage!(
        "minimize term construction",
        "minimize_term_construction",
        minimize_term_construction_stage,
        Provenance::Driver(GeneratingPass::MinimizeTermConstruction),
        "generating"
    ),
];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StageDescription {
    pub name: &'static str,
    /// Source table of this phase: `prologue_descriptions`, `TRANSFORM_STAGES`, or
    /// `EMISSION_STAGES`.
    pub table: &'static str,
    pub call: &'static str,
    pub behavior: &'static str,
    pub generating_passes: Vec<&'static str>,
}

fn description(stage: &Stage, table: &'static str) -> StageDescription {
    let generating_passes = match stage.provenance {
        Provenance::Driver(pass) => vec![pass.as_str()],
        // Internal provenance describes receipt placement. The manifest keeps the externally
        // visible classification of metadata-only composite stages.
        Provenance::Internal(passes) if stage.behavior == "generating" => {
            passes.iter().map(|pass| pass.as_str()).collect()
        }
        Provenance::None | Provenance::Internal(_) => Vec::new(),
    };
    StageDescription {
        name: stage.name,
        table,
        call: stage.call,
        behavior: stage.behavior,
        generating_passes,
    }
}

pub fn stage_descriptions() -> Vec<StageDescription> {
    TRANSFORM_STAGES
        .iter()
        .map(|stage| description(stage, "TRANSFORM_STAGES"))
        .chain(
            EMISSION_STAGES
                .iter()
                .map(|stage| description(stage, "EMISSION_STAGES")),
        )
        .collect()
}

pub fn prologue_descriptions() -> Vec<StageDescription> {
    vec![
        StageDescription {
            name: prologue_phase::EXPAND_STRUCTURED_CONFIGURATIONS,
            table: "prologue_descriptions",
            call: "expand_configurations_with_diagnostics",
            behavior: "generating",
            generating_passes: vec![GeneratingPass::ConfigurationExpansion.as_str()],
        },
        StageDescription {
            name: prologue_phase::RESOLVE_STRUCTURED_CONFIGURATIONS,
            table: "prologue_descriptions",
            call: "resolve",
            behavior: "validation",
            generating_passes: Vec::new(),
        },
        StageDescription {
            name: prologue_phase::DEFINITION_CHECKS,
            table: "prologue_descriptions",
            call: "check_definition_with_options",
            behavior: "validation",
            generating_passes: Vec::new(),
        },
    ]
}

pub fn pipeline_checkpoint() -> (&'static str, &'static str) {
    ("execution_definition", "definition")
}

#[cfg(test)]
pub(crate) fn run_stages(
    stages: &[Stage],
    start: Definition,
    state: &mut PipelineState,
    options: &CompileOptions,
    timings: &mut PhaseTimings,
) -> Result<Definition, CompileError> {
    run_stages_seeded(stages, start, state, options, timings, None)
}

#[cfg(test)]
pub(crate) fn run_stages_seeded(
    stages: &[Stage],
    start: Definition,
    state: &mut PipelineState,
    options: &CompileOptions,
    timings: &mut PhaseTimings,
    seed: Option<ResolvedDefinition>,
) -> Result<Definition, CompileError> {
    run_stages_seeded_current(stages, start, state, options, timings, seed)
        .map(Current::into_definition)
}

pub(crate) fn run_stages_seeded_with_resolved(
    stages: &[Stage],
    start: Definition,
    state: &mut PipelineState,
    options: &CompileOptions,
    timings: &mut PhaseTimings,
    seed: ResolvedDefinition,
) -> Result<(Definition, ResolvedDefinition), CompileError> {
    run_stages_seeded_current(stages, start, state, options, timings, Some(seed))
        .and_then(|current| current.into_definition_and_resolved("resolve pipeline output"))
}

fn run_stages_seeded_current(
    stages: &[Stage],
    start: Definition,
    state: &mut PipelineState,
    options: &CompileOptions,
    timings: &mut PhaseTimings,
    seed: Option<ResolvedDefinition>,
) -> Result<Current, CompileError> {
    let mut current = seed.map_or_else(
        || Current::new(start.clone()),
        |resolved| Current::with_resolved(start.clone(), resolved),
    );
    for stage in stages {
        let (output, next_resolved) = timings.time(stage.name, || {
            let input = PassInput::new(&current);
            let output = (stage.run)(&input, state).map_err(|error| CompileError {
                stage: stage.name,
                message: error.message,
                diagnostics: options.diagnostics.apply(error.diagnostics),
            })?;
            let output = match stage.provenance {
                Provenance::Driver(pass) => {
                    record_generated_origins(&current.definition, output, pass)
                }
                Provenance::None | Provenance::Internal(_) => output,
            };
            #[cfg(debug_assertions)]
            assert_no_dangling_application_identities(&output);
            let next_resolved = match current.resolved.get() {
                Some(Ok(previous)) => Some(previous.update(&current.definition, &output)),
                Some(Err(error)) => Some(Err(error.clone())),
                None => None,
            };
            Ok((output, next_resolved))
        })?;
        current = Current::new(output);
        if let Some(resolved) = next_resolved {
            let _ = current.resolved.set(resolved);
        }
    }
    Ok(current)
}

#[cfg(debug_assertions)]
fn assert_no_dangling_application_identities(definition: &Definition) {
    measure::without_counting(|| {
        let resolved = ResolvedDefinition::resolve(definition)
            .expect("a pipeline stage produced a definition that cannot be resolved");
        for (module_id, module) in resolved.modules() {
            let catalog = resolved.production_catalog(module_id);
            for sentence in &module.local_sentences {
                assert_sentence_identities(sentence, &catalog, &module.name);
            }
        }
    });
}

#[cfg(debug_assertions)]
fn assert_sentence_identities(
    sentence: &Sentence,
    catalog: &ProductionCatalog<'_>,
    module_name: &str,
) {
    let check = |term: &Term| assert_term_identities(term, catalog, module_name);
    match sentence {
        Sentence::ContextAlias { body, requires, .. }
        | Sentence::Context { body, requires, .. } => {
            check(body);
            check(requires);
        }
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => {
            check(body);
            check(requires);
            check(ensures);
        }
        Sentence::Configuration { body, ensures, .. } => {
            check(body);
            check(ensures);
        }
        _ => {}
    }
}

#[cfg(debug_assertions)]
fn assert_term_identities(term: &Term, catalog: &ProductionCatalog<'_>, module_name: &str) {
    if let (Some(metadata), Term::Apply { label, .. }) = (term.metadata(), term.unannotated())
        && let Some(identity) = metadata.production
    {
        assert!(
            catalog.lookup(&identity).is_some(),
            "dangling production identity {identity} on application {label} in module {module_name}"
        );
    }
    match term {
        Term::Annotated { term, .. } => assert_term_identities(term, catalog, module_name),
        Term::Rewrite { left, right } => {
            assert_term_identities(left, catalog, module_name);
            assert_term_identities(right, catalog, module_name);
        }
        Term::As { pattern, alias } => {
            assert_term_identities(pattern, catalog, module_name);
            assert_term_identities(alias, catalog, module_name);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                assert_term_identities(item, catalog, module_name);
            }
        }
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
    }
}

pub(crate) fn run_standalone<E>(
    definition: &Definition,
    run: impl FnOnce(&PassInput<'_>, &mut PipelineState) -> Result<Definition, E>,
    provenance: Option<GeneratingPass>,
) -> Result<Definition, E> {
    let output = run_standalone_raw(definition, run)?;
    Ok(match provenance {
        Some(pass) => record_generated_origins(definition, output, pass),
        None => output,
    })
}

pub(crate) fn run_standalone_raw<T, E>(
    definition: &Definition,
    run: impl FnOnce(&PassInput<'_>, &mut PipelineState) -> Result<T, E>,
) -> Result<T, E> {
    let current = Current::new(definition.clone());
    let input = PassInput::new(&current);
    let mut state = PipelineState::default();
    run(&input, &mut state)
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use crate::{
        definition::{Definition, FlatModule},
        diagnostic::{Diagnostic, DiagnosticCode},
    };

    use super::*;

    fn definition() -> Definition {
        Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: Vec::new(),
                attributes: Default::default(),
            }],
            attributes: Default::default(),
        }
    }

    #[test]
    fn pass_input_resolves_once() {
        let current = Current::new(definition());
        let input = PassInput::new(&current);
        assert!(std::ptr::eq(
            input.resolved_raw().unwrap(),
            input.resolved_raw().unwrap()
        ));
    }

    #[test]
    fn pass_error_preserves_message_and_diagnostics() {
        let diagnostic = Diagnostic {
            severity: crate::diagnostic::Severity::Error,
            code: DiagnosticCode::InvalidAttribute,
            message: "bad attribute".into(),
            source: None,
            location: None,
            input_addresses: Vec::new(),
        };
        let error = super::super::ResolveCommError {
            diagnostics: vec![diagnostic.clone()],
        };
        let converted = PassError::from(error);
        assert_eq!(
            converted.message,
            "commutative simplification resolution produced 1 errors"
        );
        assert_eq!(converted.diagnostics, vec![diagnostic]);
    }

    #[test]
    fn run_stages_names_the_failing_stage() {
        fn fail(_: &PassInput<'_>, _: &mut PipelineState) -> Result<Definition, PassError> {
            Err(PassError::from("failure".to_owned()))
        }
        let stages = [Stage {
            name: "named stage",
            call: "fail",
            run: fail,
            provenance: Provenance::None,
            behavior: "validation",
        }];
        let error = run_stages(
            &stages,
            definition(),
            &mut PipelineState::default(),
            &CompileOptions::default(),
            &mut PhaseTimings::default(),
        )
        .unwrap_err();
        assert_eq!(error.stage, "named stage");
        assert_eq!(error.message, "failure");
    }

    #[test]
    fn run_standalone_runs_one_pass() {
        static CALLS: AtomicUsize = AtomicUsize::new(0);
        let definition = definition();
        let output = run_standalone(
            &definition,
            |input, _| {
                CALLS.fetch_add(1, Ordering::Relaxed);
                Ok::<_, Infallible>(input.definition.clone())
            },
            None,
        )
        .unwrap();
        assert_eq!(CALLS.swap(0, Ordering::Relaxed), 1);
        assert_eq!(output, definition);
    }
}
