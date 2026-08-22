//! A Rust implementation of the K Framework frontend.

pub mod backend;
pub mod builtin;
pub mod definition;
pub mod diagnostic;
pub mod inner;
pub mod kast;
pub mod kompile;
pub use k_rust_kore::kore;
#[cfg(feature = "cli")]
pub mod native;
pub mod outer;
