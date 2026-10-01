//! Collector transport: the host and stable descriptor payloads that carry
//! authored declarations from macro expansion to semantic lowering.
//!
//! These are transport types, not semantic IR. Nested nodes carry
//! parser-owned [`crate::ProvenanceKey`] values which the compiler resolves
//! through the enclosing descriptor's provenance table.

#[doc(hidden)]
pub mod collector;
pub mod configuration;
pub mod detail;
pub mod grammar;
pub mod head_rule;
pub mod rule;
mod validation;
