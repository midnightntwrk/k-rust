//! Exposes the optimization level this crate is compiled at as `cfg(k_rust_opt_level = "N")`,
//! and the digest of the sources this build of k-rust is made from as `K_RUST_SOURCE_DIGEST`.
//!
//! The native stack a recursion takes per level is a property of the generated code: the
//! optimization level decides how large each frame is and how many frames a level takes, and
//! debug assertions add checks and the data they read. The stack the compile passes are given
//! per level of a term (`stack::STACK_PER_LEVEL`) needs that level, and Cargo tells it only to
//! build scripts.
//!
//! The source digest identifies the build (`native::build_identity`): two builds whose k-rust
//! inputs differ get different digests, whether or not the difference is committed, and builds
//! from different commits with the same inputs get the same one, since they are the same
//! program. The inputs are the files of this crate and of the workspace crates it is built
//! from (`k-rust-kore`, `k-rust-backend`, `k-rust-regex`) that the compiler reads: their
//! sources, embedded builtins and C parser, manifests and build scripts, and the workspace
//! manifest and lockfile. Test files and insta snapshots are left out, so editing a test does
//! not rebuild the library. Each hashed file is a `rerun-if-changed` trigger; a change to any of them
//! but the workspace manifest and lockfile rebuilds this crate anyway, so the digest costs
//! almost no extra rebuild. A file added to a source directory becomes part of the digest the
//! next time one of the triggers changes, which is when it can first be part of the program. Outside this
//! workspace's layout (a dependency crate missing beside this one) the digest is empty and the
//! identity says it is unverified.

use std::{
    fs,
    path::{Path, PathBuf},
};

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!(
        "cargo::rustc-check-cfg=cfg(k_rust_opt_level, values(\"0\", \"1\", \"2\", \"3\", \"s\", \"z\"))"
    );
    let level = std::env::var("OPT_LEVEL").expect("Cargo sets OPT_LEVEL for build scripts");
    println!("cargo::rustc-cfg=k_rust_opt_level=\"{level}\"");
    let manifest = PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"),
    );
    let digest =
        source_files(&manifest).map_or_else(String::new, |files| digest(&manifest, &files));
    println!("cargo::rustc-env=K_RUST_SOURCE_DIGEST={digest}");
}

/// The input files, sorted, or `None` outside this workspace's layout.
fn source_files(manifest: &Path) -> Option<Vec<PathBuf>> {
    let crates = manifest.parent()?;
    let workspace = crates.parent()?;
    let mut files = vec![workspace.join("Cargo.toml"), workspace.join("Cargo.lock")];
    let members = [
        ("k-rust", &["src", "builtin", "cparser"][..]),
        ("k-rust-kore", &["src"][..]),
        ("k-rust-backend", &["src"][..]),
        ("k-rust-regex", &["src"][..]),
    ];
    for (name, directories) in members {
        let member = crates.join(name);
        let cargo = fs::read_to_string(member.join("Cargo.toml")).ok()?;
        if !cargo.contains(&format!("name = \"{name}\"")) {
            return None;
        }
        files.push(member.join("Cargo.toml"));
        if member.join("build.rs").is_file() {
            files.push(member.join("build.rs"));
        }
        for directory in directories {
            collect(&member.join(directory), &mut files);
        }
    }
    if files.iter().any(|file| !file.is_file()) {
        return None;
    }
    files.sort();
    Some(files)
}

/// Every file under `directory`, except insta snapshots.
fn collect(directory: &Path, files: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(directory) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if path.is_dir() {
            if name != "snapshots" {
                collect(&path, files);
            }
        } else if !(name.ends_with(".snap")
            || name.ends_with(".snap.new")
            || name.ends_with(".pending-snap"))
        {
            files.push(path);
        }
    }
}

/// A 128-bit FNV-1a digest of each file's path relative to the workspace and its bytes, in
/// hexadecimal; every file becomes a rerun trigger. The digest only needs to tell different
/// sources apart, not resist an adversary.
fn digest(manifest: &Path, files: &[PathBuf]) -> String {
    const OFFSET: u128 = 0x6c62_272e_07bb_0142_62b8_2175_6295_c58d;
    const PRIME: u128 = 0x0000_0000_0100_0000_0000_0000_0000_013b;
    let workspace = manifest.parent().and_then(Path::parent).unwrap_or(manifest);
    let mut hash = OFFSET;
    let mut feed = |bytes: &[u8]| {
        for &byte in bytes {
            hash ^= u128::from(byte);
            hash = hash.wrapping_mul(PRIME);
        }
    };
    for file in files {
        println!("cargo::rerun-if-changed={}", file.display());
        let relative = file.strip_prefix(workspace).unwrap_or(file);
        let bytes = fs::read(file).unwrap_or_default();
        feed(relative.to_string_lossy().as_bytes());
        feed(&[0]);
        feed(&(bytes.len() as u64).to_le_bytes());
        feed(&bytes);
    }
    format!("{hash:032x}")
}
