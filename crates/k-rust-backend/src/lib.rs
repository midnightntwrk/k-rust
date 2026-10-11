//! In-process concrete and symbolic execution for KORE definitions.

mod alias;
mod instance_normal;
mod ite;
pub mod nesting;
mod priority_conjunct;
mod verify;

pub mod allowance;
pub mod builtin;
pub mod claim;
pub mod condition;
pub mod confluence;
pub mod definedness;
pub mod definition;
pub mod diagnostic;
pub mod externalize;
pub mod fresh;
pub mod implication;
pub mod matching;
pub mod model;
pub mod proof;
pub mod rewrite;
pub mod rule;
pub mod search;
pub mod session;
pub mod simplify;
pub mod smt;
pub mod stop;
pub mod substitution;
pub mod term;
pub mod timeout;
pub mod transition;
pub mod unification;

#[cfg(test)]
mod counted;
#[cfg(test)]
mod peak_memory;
#[cfg(test)]
mod tests;
