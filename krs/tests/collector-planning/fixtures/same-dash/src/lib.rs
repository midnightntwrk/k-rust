//! First same-named dependency fixture.

#[cfg(not(feature = "verification"))]
compile_error!("generated collector did not preserve resolved Cargo features");

/// Distinguishes this package at runtime.
pub const MARKER: &str = "same-a";

/// Proves that the resolved feature set reaches this crate.
#[cfg(feature = "verification")]
pub const VERIFICATION: bool = true;

