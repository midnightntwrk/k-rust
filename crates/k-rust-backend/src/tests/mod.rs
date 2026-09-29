//! Tests of `pub(crate)` entry points: the compiler stops them from naming a private item.

mod definedness;
mod externalize;
mod lean_bridge;
mod matching;
mod matching_oracle;
mod rewrite;
mod walk_flags;

pub(crate) mod alpha;
mod cascade;
