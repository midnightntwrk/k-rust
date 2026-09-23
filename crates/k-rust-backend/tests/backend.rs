//! Integration tests of the public API of `k_rust_backend`: one target, so that shared support
//! is never dead code in another target. The modules live under `tests/backend/`.

#[path = "backend/matching.rs"]
mod matching;
#[path = "backend/overloaded_list_owise.rs"]
mod overloaded_list_owise;
#[path = "backend/properties.rs"]
mod properties;
#[path = "backend/rewrite.rs"]
mod rewrite;
#[path = "backend/rule_index.rs"]
mod rule_index;
#[path = "backend/simplify.rs"]
mod simplify;
#[path = "backend/support.rs"]
mod support;
#[path = "backend/term_order.rs"]
mod term_order;
