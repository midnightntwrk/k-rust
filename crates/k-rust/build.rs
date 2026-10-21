//! Exposes the optimization level this crate is compiled at as `cfg(k_rust_opt_level = "N")`,
//! and the digest of the sources this build of k-rust is made from as `K_RUST_SOURCE_DIGEST`.
//!
//! The native stack a recursion takes per level is a property of the generated code: the
//! optimization level decides how large each frame is and how many frames a level takes, and
//! debug assertions add checks and the data they read. The stack the compile passes are given
//! per level of a term (`stack::STACK_PER_LEVEL`) needs that level, and Cargo tells it only to
//! build scripts.
//!
//! The source digest identifies the build (`k_rust::build_identity`); `build/source_digest.rs`
//! says which files it covers and why its rerun triggers add no rebuild. An empty digest (the
//! sources are not in this workspace's layout) makes the identity unverified.

#[path = "build/source_digest.rs"]
mod source_digest;

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!(
        "cargo::rustc-check-cfg=cfg(k_rust_opt_level, values(\"0\", \"1\", \"2\", \"3\", \"s\", \"z\"))"
    );
    let level = std::env::var("OPT_LEVEL").expect("Cargo sets OPT_LEVEL for build scripts");
    println!("cargo::rustc-cfg=k_rust_opt_level=\"{level}\"");
    let manifest = std::path::PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"),
    );
    let digest = source_digest::source_digest(&manifest);
    for trigger in &digest.triggers {
        println!("cargo::rerun-if-changed={}", trigger.display());
    }
    println!(
        "cargo::rustc-env=K_RUST_SOURCE_DIGEST={}",
        digest.digest.unwrap_or_default()
    );
}
