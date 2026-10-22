//! The guidance proposers (ARCHITECTURE 8.3-8.6), beside the explicit and blind proposers of
//! the engine (`engine::proposer`). Each implements the engine's internal `Proposer` interface,
//! and every choice it makes derives from the campaign seed.
//!
//! - [`dictionary`]: guard harvesting (ARCHITECTURE 8.3; FZ-11).
//! - [`climb`]: targeted hill climbing over typed holes (ARCHITECTURE 8.4; FZ-12).
//! - [`corpus`]: coverage-guided mutation of kept cases (ARCHITECTURE 8.5; FZ-14).

pub(crate) mod climb;
pub(crate) mod corpus;
pub(crate) mod dictionary;
#[cfg(test)]
mod tests;
