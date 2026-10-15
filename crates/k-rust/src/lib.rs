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
/// The backend crate the facade [`backend`] is built on, with the features this build of
/// `k_rust` enables.
///
/// [`backend`] is the supported embedding surface: its own items and the items it re-exports by
/// name (the cancellation surface and [`backend::VARIABLE_IDENTITY`]).
/// This re-export exists so that a host can name every type the facade's signatures carry
/// (`BackendDefinition` and `SmtSolver` in [`backend::Backend::with_solver`], the definition
/// [`backend::Backend::internalize_definition`] returns, and the types their methods return)
/// without a second dependency on `k-rust-backend`.
///
/// Items reached only through `k_rust::k_rust_backend` carry no stability promise: they change
/// between releases without a version bump, and `k_rust`'s own version does not signal those
/// changes either.
/// A host pinned to a commit audits a re-pin by diffing the output of `cargo public-api` for both
/// `k-rust` and `k-rust-backend` between its old and new commits.
/// See the module docs of [`backend`].
pub use k_rust_backend;
pub use k_rust_kore::kore;
pub use k_rust_kore::names;
#[cfg(feature = "cli")]
pub mod native;
pub mod outer;
pub mod provenance;
mod stack;
pub mod timings;

/// Whether this build infers ambiguity resolutions with Z3 (the `z3-inference` feature).
pub const Z3_INFERENCE: bool = cfg!(feature = "z3-inference");
