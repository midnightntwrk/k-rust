//! Exposes the version of the k-rust package kink builds against as the compile-time variable
//! `KINK_K_RUST_VERSION`, which `K_RUST_REVISION` (src/lib.rs) reads.
//!
//! kink is built inside k-rust's workspace against the k-rust beside it, so the k-rust it links is
//! the package of `crates/k-rust` at the workspace root, and its version is the `version` of that
//! manifest's `[package]` table. Cargo tells a build script only its own package's version, so the
//! script reads the manifest; it reruns when the manifest changes.

use std::{env, fs, path::Path};

fn main() {
    let directory = env::var("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR");
    let manifest = Path::new(&directory).join("../../../crates/k-rust/Cargo.toml");
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rerun-if-changed={}", manifest.display());
    let text = fs::read_to_string(&manifest)
        .unwrap_or_else(|e| panic!("k-rust's manifest {}: {e}", manifest.display()));
    let version = package_version(&text)
        .unwrap_or_else(|| panic!("{} has no [package] version", manifest.display()));
    println!("cargo::rustc-env=KINK_K_RUST_VERSION={version}");
}

/// The `version = "..."` of the `[package]` table of a Cargo manifest.
fn package_version(text: &str) -> Option<&str> {
    let mut in_package = false;
    for line in text.lines().map(str::trim) {
        if line.starts_with('[') {
            in_package = line == "[package]";
        } else if in_package {
            let Some(rest) = line.strip_prefix("version") else {
                continue;
            };
            let value = rest.trim_start().strip_prefix('=')?.trim();
            return value.strip_prefix('"')?.split('"').next();
        }
    }
    None
}
