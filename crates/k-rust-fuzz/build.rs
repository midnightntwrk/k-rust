//! Exposes the digest of the sources this build of k-rust-fuzz is made from as
//! `K_RUST_FUZZ_SOURCE_DIGEST`, for `k_rust_fuzz::build_identity`, which every report records as
//! `identity.fuzz-revision` (FZ-REPLAY-WHOLE S4).
//!
//! A report is computed by k-rust's runs and by this crate's code (the classification, the
//! judgements, the statements and the report itself), so its identity must name both builds:
//! k-rust's identity (`k_rust::build_identity`) covers k-rust and its path dependencies, and this
//! digest covers the rest of what reaches a report, this crate and `krs-unparse`, which prints
//! hole values as program text. The rule is k-rust's (`../k-rust/build/source_digest.rs`, which
//! says which files it hashes and why its rerun triggers add no rebuild). An empty digest (the
//! sources are not in this workspace's layout) makes the identity unverified.

#[path = "../k-rust/build/source_digest.rs"]
#[allow(
    dead_code,
    reason = "k-rust's build script uses the rest; this one digests its own members"
)]
mod source_digest;

/// The crates whose sources make up this build beside k-rust's: this crate and its normal path
/// dependencies outside k-rust's digest (`tests/formats.rs` checks the list against the
/// manifests).
const MEMBERS: [&str; 2] = ["crates/k-rust-fuzz", "krs/crates/krs-unparse"];

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    let manifest = std::path::PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"),
    );
    let members = MEMBERS.map(str::to_owned);
    let digest = source_digest::source_digest_of(&manifest, &members);
    for trigger in &digest.triggers {
        println!("cargo::rerun-if-changed={}", trigger.display());
    }
    println!(
        "cargo::rustc-env=K_RUST_FUZZ_SOURCE_DIGEST={}",
        digest.digest.unwrap_or_default()
    );
}
