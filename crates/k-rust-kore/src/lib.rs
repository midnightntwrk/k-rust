//! Shared KORE syntax and serialization used by the k-rust frontend and backend.
//!
//! KORE pattern and sort parsing, printing, serialization, normalization, comparison, cloning,
//! debug formatting, and destruction use explicit heap-backed work stacks and impose no
//! nesting-depth limit. Memory is the only intended bound.

pub mod json_tree;
pub mod kore;
pub mod measure;
pub mod names;
pub mod trace_aggregate;
