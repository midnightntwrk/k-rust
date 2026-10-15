//! Integration tests of the public API of `k_rust_backend`: one target, so that shared support
//! is never dead code in another target. The modules live under `tests/backend/`.

#[path = "backend/anywhere_matching.rs"]
mod anywhere_matching;
#[path = "backend/collection_item_sorts.rs"]
mod collection_item_sorts;
#[path = "backend/collection_roles.rs"]
mod collection_roles;
#[path = "backend/confluence_budget.rs"]
mod confluence_budget;
#[path = "backend/deferred_definedness.rs"]
mod deferred_definedness;
#[path = "backend/definedness_classes.rs"]
mod definedness_classes;
#[path = "backend/evaluation_mode.rs"]
mod evaluation_mode;
#[path = "backend/hook_result_sorts.rs"]
mod hook_result_sorts;
#[path = "backend/issue_4114_overload.rs"]
mod issue_4114_overload;
#[path = "backend/matching.rs"]
mod matching;
#[path = "backend/mixed_float_formats.rs"]
mod mixed_float_formats;
#[path = "backend/names.rs"]
mod names;
#[path = "backend/nan_sign.rs"]
mod nan_sign;
#[path = "backend/overloaded_list_owise.rs"]
mod overloaded_list_owise;
#[path = "backend/parametric_collection_elements.rs"]
mod parametric_collection_elements;
#[path = "backend/partial_equation_heads.rs"]
mod partial_equation_heads;
#[path = "backend/properties.rs"]
mod properties;
#[path = "backend/rewrite.rs"]
mod rewrite;
#[path = "backend/rule_index.rs"]
mod rule_index;
#[path = "backend/search.rs"]
mod search;
#[path = "backend/set_aside_equations.rs"]
mod set_aside_equations;
#[path = "backend/simplify.rs"]
mod simplify;
#[path = "backend/structural_distinctness.rs"]
mod structural_distinctness;
#[path = "backend/stuck_instances.rs"]
mod stuck_instances;
#[path = "backend/subject_key_equalities.rs"]
mod subject_key_equalities;
#[path = "backend/support.rs"]
mod support;
#[path = "backend/tentative_bindings.rs"]
mod tentative_bindings;
#[path = "backend/term_order.rs"]
mod term_order;
#[path = "backend/unification.rs"]
mod unification;
#[path = "backend/unspecified_oracle.rs"]
mod unspecified_oracle;
#[path = "backend/value_contract.rs"]
mod value_contract;
#[path = "backend/variables_api.rs"]
mod variables_api;
#[path = "backend/work_budget.rs"]
mod work_budget;
