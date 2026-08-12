//! A Rust implementation of the K Framework frontend.

pub mod definition;
pub mod diagnostic;
pub mod inner;
pub mod kast;
pub mod kompile;
pub mod kore;
#[cfg(feature = "cli")]
pub mod native;
pub mod outer;
