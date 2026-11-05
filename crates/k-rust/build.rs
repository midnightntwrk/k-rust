//! Exposes the optimization level this crate is compiled at as `cfg(k_rust_opt_level = "N")`,
//! the digest of the sources this build of k-rust is made from as `K_RUST_SOURCE_DIGEST`, and the
//! digest and release of the Z3 archive a static link takes Z3 from as `K_RUST_Z3_ARCHIVE_SHA256`
//! and `K_RUST_Z3_ARCHIVE_RELEASE`.
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
//!
//! The Z3 archive names the Z3 build of a static link (`k_rust::backend::z3_build`);
//! `build/z3_archive.rs` says how it is found. Its triggers are the variables that choose the
//! archive and, on the environment route, the archive itself.

#[path = "build/source_digest.rs"]
mod source_digest;
#[path = "build/z3_archive.rs"]
mod z3_archive;

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
    let (archive_sha256, archive_release) = z3_archive::z3_archive().unwrap_or_default();
    println!("cargo::rustc-env=K_RUST_Z3_ARCHIVE_SHA256={archive_sha256}");
    println!("cargo::rustc-env=K_RUST_Z3_ARCHIVE_RELEASE={archive_release}");
}
