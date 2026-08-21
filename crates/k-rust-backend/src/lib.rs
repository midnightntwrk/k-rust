//! In-process concrete and symbolic execution for KORE definitions.

mod alias;

pub mod binary;
pub mod builtin;
pub mod claim;
pub mod definedness;
pub mod definition;
pub mod externalize;
pub mod implication;
pub mod matching;
pub mod proof;
pub mod rewrite;
pub mod rule;
pub mod search;
pub mod session;
pub mod simplify;
pub mod smt;
pub mod substitution;
pub mod term;
pub mod timeout;
pub mod unification;
