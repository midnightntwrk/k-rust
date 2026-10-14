//! A Rust implementation of the K Framework frontend.

pub mod backend;
#[cfg(feature = "cli")]
pub mod bison;
pub mod builtin;
pub mod definition;
pub mod diagnostic;
pub mod inner;
pub mod kast;
pub mod kompile;
mod lines;
pub use k_rust_kore::kore;
pub use k_rust_kore::names;
#[cfg(feature = "cli")]
pub mod native;
pub mod outer;
pub mod provenance;
mod stack;
pub mod timings;

/// Whether this build folds ground `FLOAT` applications at compile time with MPFR (the
/// `mpfr-folding` feature); without it, the constant fold leaves them for execution to evaluate.
/// Cargo unifies features across a workspace, so a dependent reads this rather than assuming the
/// features it requested.
pub const MPFR_FOLDING: bool = cfg!(feature = "mpfr-folding");

/// Whether this build infers ambiguity resolutions with Z3 (the `z3-inference` feature).
pub const Z3_INFERENCE: bool = cfg!(feature = "z3-inference");
