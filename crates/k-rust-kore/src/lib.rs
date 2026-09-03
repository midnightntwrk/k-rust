//! Shared KORE syntax and serialization used by the k-rust frontend and backend.
//!
//! KORE pattern parsing, printing, serialization, normalization, comparison, cloning, and
//! destruction use explicit heap-backed work stacks and impose no nesting-depth limit. Memory is
//! the only intended bound. Sort parsing is likewise iterative, but the public [`kore::ast::Sort`]
//! type retains its recursively derived clone, comparison, debug, and drop implementations: real
//! KORE producers keep sort nesting shallow, and those trait operations are the documented
//! exception to the pattern stack-safety policy.

pub mod json_tree;
pub mod kore;
