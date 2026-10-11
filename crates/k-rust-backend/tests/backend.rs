//! Integration tests of the public API of `k_rust_backend`: one target, so that shared support
//! is never dead code in another target. The modules live under `tests/backend/`.

#[path = "backend/anywhere_matching.rs"]
mod anywhere_matching;
#[path = "backend/definedness_classes.rs"]
mod definedness_classes;
#[path = "backend/hook_result_sorts.rs"]
mod hook_result_sorts;
#[path = "backend/issue_4114_overload.rs"]
mod issue_4114_overload;
#[path = "backend/matching.rs"]
mod matching;
#[path = "backend/names.rs"]
mod names;
#[path = "backend/overloaded_list_owise.rs"]
mod overloaded_list_owise;
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
#[path = "backend/simplify.rs"]
mod simplify;
#[path = "backend/structural_distinctness.rs"]
mod structural_distinctness;
#[path = "backend/stuck_instances.rs"]
mod stuck_instances;
#[path = "backend/support.rs"]
mod support;
#[path = "backend/term_order.rs"]
mod term_order;
#[path = "backend/unification.rs"]
mod unification;
#[path = "backend/unspecified_oracle.rs"]
mod unspecified_oracle;
#[path = "backend/value_contract.rs"]
mod value_contract;
