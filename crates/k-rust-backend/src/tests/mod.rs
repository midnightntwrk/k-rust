//! Tests of `pub(crate)` entry points: the compiler stops them from naming a private item.

mod associate;
mod bindings;
mod constructor_schemas;
mod coverage;
mod definedness;
mod definedness_oracle;
mod domain_values;
mod externalize;
pub(crate) mod generators;
mod guards;
mod matching;
mod matching_oracle;
mod parametric_subsorts;
mod predicate_reading;
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
mod recursion_stack;
mod search_boundary;
#[cfg(feature = "z3")]
mod smt_boundary;
mod sort_injections;
mod stack_stop_sites;
mod term_comparison;
