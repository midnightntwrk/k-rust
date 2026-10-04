//! Tests of `pub(crate)` entry points: the compiler stops them from naming a private item.

mod constructor_schemas;
mod definedness;
mod externalize;
pub(crate) mod lean_bridge;
mod matching;
mod matching_oracle;
mod parametric_subsorts;
mod rewrite;
mod walk_flags;

pub(crate) mod alpha;
mod capture;
mod cascade;

mod sort_injections;
