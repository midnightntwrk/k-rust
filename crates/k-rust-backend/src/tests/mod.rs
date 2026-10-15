//! Tests of `pub(crate)` entry points: the compiler stops them from naming a private item.

mod constructor_schemas;
mod coverage;
mod definedness;
mod definedness_oracle;
mod domain_values;
mod externalize;
pub(crate) mod lean_bridge;
mod matching;
mod matching_oracle;
mod parametric_subsorts;
mod rewrite;
mod several_matchings;
mod unread_frames;
mod walk_flags;

pub(crate) mod alpha;
mod capture;
mod cascade;
pub(crate) mod priority_conjunct;

mod proof_boundary;
mod recover_boundary;
mod search_boundary;
#[cfg(feature = "z3")]
mod smt_boundary;
mod sort_injections;
mod stack_stop_sites;
mod term_comparison;
