//! Kompile layers definition resolution, ordered transformation passes, sort injection, and KORE emission.
//! `compile::transform_loaded_definition` owns the timed stage list; shared equivalence, retargeting, and label-graph algorithms have one home.
//! Kompile and provenance counters measure the variable work named by those algorithms.
//!
//! Pure compilation passes and KORE emission.

mod compile;
mod fresh_names;
pub mod initial_configuration;
mod label_graph;
mod module_to_kore;
mod passes;
pub mod pipeline;
mod retarget;
mod search_pattern;
mod sort_injections;
mod term_to_kore;
mod view;

pub use compile::{
    CompilationBackend, CompileError, CompileOptions, CompiledKoreArtifacts,
    EmittedSentenceProvenance, REJECT_LABEL_PARAMETERS, compile_loaded_definition,
    compile_loaded_definition_timed,
};
pub use fresh_names::GeneratedVariableIdentity;
pub use module_to_kore::{
    DeclarationError, DeclarationModules, ModuleToKoreError, ModuleToKoreOptions,
    declaration_modules, declaration_modules_from_resolved,
    declaration_modules_from_resolved_with_options, encode_kore_label, encode_kore_sort,
    module_to_kore, module_to_kore_from_resolved, module_to_kore_from_resolved_with_options,
    rust_backend_hook_namespaces, standard_kore_prelude,
};
pub use passes::{
    AddImplicitComputationCellError, CheckSimplificationError, ConcretizeCellsError,
    ConstantFoldingError, ExpandMacrosError, GuardOrPatternsError, MacroExpansionDefinition,
    RemoveUnitError, ResolveCommError, ResolveContextsError, ResolveFreshConfigConstantsError,
    ResolveFreshConstantsError, ResolveFunError, ResolveFunctionWithConfigError,
    ResolveHeatCoolError, ResolveIoError, ResolveSemanticCastsError, ResolveStrictError,
    SubsortKItemError, add_cool_like_attributes, add_implicit_computation_cell,
    add_semantics_module, check_simplification_rules, concretize_cells,
    concretize_cells_in_sentence, constant_fold, expand_macros, expand_macros_in_term,
    expand_macros_in_term_with_scope, generate_sort_predicate_rules,
    generate_sort_predicate_syntax, generate_sort_projections, guard_or_patterns,
    minimize_term_construction, number_sentences, propagate_macro_attributes,
    regenerate_sort_predicate_syntax, remove_unit, resolve_anon_vars,
    resolve_anon_vars_in_sentence, resolve_comm, resolve_config_var, resolve_contexts,
    resolve_fresh_config_constants, resolve_fresh_constants, resolve_fun,
    resolve_function_with_config, resolve_heat_cool_attributes, resolve_io, resolve_semantic_casts,
    resolve_semantic_casts_in_sentence, resolve_semantic_casts_with_predicates_in_sentence,
    resolve_strict, subsort_kitem,
};
pub use search_pattern::{
    CompileSearchPatternError, CompiledSearchPattern, KoreVariableIdentity, compile_search_pattern,
};
pub use sort_injections::{
    AmbiguousInstance, BranchTyping, PositionTyping, SentenceTyper, SentenceTyping,
    SentenceTypingError, SortInjectionError, SortInjector, SortMismatch, add_sort_injections,
    add_sort_injections_from_resolved, add_sort_injections_to_definition, sentence_typing,
};
pub use term_to_kore::{
    TermConversionError, TermConverter, term_to_kore, term_to_kore_from_resolved,
    term_to_kore_from_resolved_with_token_module,
};
