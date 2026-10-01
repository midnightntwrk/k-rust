//! Kompile invariant checkers.
//!
//! A checker states a well-formedness condition of what kompile builds that no type enforces,
//! and panics when a compiled artifact violates it. A violation is a compiler defect, never a
//! user error: every condition checked here holds of the output of a correct compile of any
//! input, so the panic names the condition and what the violating sentence was built from.
//!
//! - [`emitted`] checks every sentence of the emitted KORE theory (the semantics and syntax
//!   modules and the macro sentences) against the facts of that theory which give its
//!   injections, domain values and generated binders a meaning:
//!   K1, every `inj{A, B}` has `A != B` and a path from `A` to `B` along the theory's
//!   `subsort{..}` axioms;
//!   K2, every `\dv{S}` has a sort head declared with `hasDomainValues`;
//!   K3, every `\exists` or `\forall` over a compiler-generated variable binds a variable that
//!   occurs free in its body.
//!
//! - [`stage`] checks the output of every stage of the table-driven pipeline: R3, every
//!   right-hand-side variable of a rule-like sentence stays bound by its left-hand side or
//!   covered by an exemption once the pipeline input has that property.
//!
//! Gating: this module and every call site of a checker are compiled under
//! `cfg(any(debug_assertions, feature = "kompile-invariant-checks"))`, so every debug build and
//! `cargo test` run the checkers, a release build with the `kompile-invariant-checks` feature
//! runs them on whatever it compiles, and a release build without the feature contains none of
//! their code.
//!
//! The checkers are read-only and only panic: they take shared references to what they check,
//! return nothing, run under `measure::without_counting` so that the kompile counters measure
//! only the compile itself, and change no value that kompile returns.

pub(crate) mod emitted;
pub(crate) mod stage;
