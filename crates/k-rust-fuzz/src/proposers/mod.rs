//! The guidance proposers (ARCHITECTURE 8.3-8.6), beside the explicit and blind proposers of
//! the engine (`engine::proposer`). Each implements the engine's internal `Proposer` interface,
//! and every choice it makes derives from the campaign seed.
//!
//! - [`dictionary`]: guard harvesting (ARCHITECTURE 8.3; FZ-11).

pub(crate) mod dictionary;
#[cfg(test)]
mod tests;
