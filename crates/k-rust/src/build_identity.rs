//! The identity of this build of k-rust, which `krust fuzz`, `krust-fuzz` and the bindings
//! record and compare.

/// The suffix of a [`build_identity`] that names no source digest.
pub const UNVERIFIED_BUILD: &str = "+unverified";

/// This build of k-rust: its package version, then `+src.` and the digest of the sources it was
/// built from (the build script's `K_RUST_SOURCE_DIGEST`; `build/source_digest.rs` lists the
/// files: the non-test Rust sources of k-rust and of its workspace path dependencies, and the
/// files they embed). Builds whose sources differ, committed or not, have different identities;
/// crates.io dependency versions, features and the profile are not part of it.
///
/// Outside the workspace layout the build script cannot read those sources, and the identity
/// is the version followed by [`UNVERIFIED_BUILD`]: two such builds of one version cannot be
/// told apart, which [`is_verified_build`] lets a comparison say.
///
/// `krust fuzz` passes it to the `krust-fuzz` executable it runs, which refuses to run for a
/// `krust` of another build, and `krust-fuzz` records it as the k-rust revision of its reports.
/// It needs no feature, so the bindings can record it too.
#[must_use]
pub fn build_identity() -> String {
    let digest = env!("K_RUST_SOURCE_DIGEST");
    if digest.is_empty() {
        format!("{}{UNVERIFIED_BUILD}", env!("CARGO_PKG_VERSION"))
    } else {
        format!("{}+src.{digest}", env!("CARGO_PKG_VERSION"))
    }
}

/// Whether `identity` (a [`build_identity`]) names a source digest.
#[must_use]
pub fn is_verified_build(identity: &str) -> bool {
    !identity.ends_with(UNVERIFIED_BUILD)
}
