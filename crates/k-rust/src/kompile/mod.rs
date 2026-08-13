//! Pure compilation passes and KORE emission.

mod module_to_kore;
mod passes;
mod sort_injections;
mod term_to_kore;

pub use module_to_kore::{
    DeclarationError, DeclarationModules, ModuleToKoreError, ModuleToKoreOptions,
    declaration_modules, declaration_modules_from_resolved, encode_kore_identifier,
    encode_kore_label, encode_kore_sort, module_to_kore, module_to_kore_from_resolved,
    module_to_kore_from_resolved_with_options, standard_kore_prelude,
};
pub use passes::{
    CheckSimplificationError, ConcretizeCellsError, ConstantFoldingError, ExpandMacrosError,
    ResolveCommError, ResolveContextsError, ResolveFreshConfigConstantsError,
    ResolveFreshConstantsError, ResolveFunError, ResolveFunctionWithConfigError,
    ResolveHeatCoolError, ResolveIoError, ResolveStrictError, SubsortKItemError,
    add_cool_like_attributes, add_implicit_computation_cell, add_semantics_module,
    check_simplification_rules, concretize_cells, constant_fold, expand_macros,
    generate_sort_predicate_rules, generate_sort_predicate_syntax, generate_sort_projections,
    guard_or_patterns, minimize_term_construction, number_sentences, propagate_macro_attributes,
    remove_unit, resolve_anon_vars, resolve_comm, resolve_config_var, resolve_contexts,
    resolve_fresh_config_constants, resolve_fresh_constants, resolve_fun,
    resolve_function_with_config, resolve_heat_cool_attributes, resolve_io, resolve_semantic_casts,
    resolve_strict, subsort_kitem,
};
pub use sort_injections::{
    SortInjectionError, SortInjector, add_sort_injections, add_sort_injections_from_resolved,
    add_sort_injections_to_definition,
};
pub use term_to_kore::{
    TermConversionError, TermConverter, term_to_kore, term_to_kore_from_resolved,
};
