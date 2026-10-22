//! The guidance proposers (ARCHITECTURE 8.3-8.6), beside the explicit and blind proposers of
//! the engine (`engine::proposer`). Each implements the engine's internal `Proposer` interface,
//! and every choice it makes derives from the campaign seed.
//!
//! - [`dictionary`]: guard harvesting (ARCHITECTURE 8.3; FZ-11).
//! - [`climb`]: targeted hill climbing over typed holes (ARCHITECTURE 8.4; FZ-12).
//! - `solve`: symbolic execution to a blocked rule and a model query (ARCHITECTURE 8.6; FZ-15),
//!   in builds with the `z3` feature.

pub(crate) mod climb;
pub(crate) mod dictionary;
#[cfg(feature = "z3")]
pub(crate) mod solve;
#[cfg(test)]
mod tests;
