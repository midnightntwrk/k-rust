//! The digest of the sources a build of k-rust is made from, for `k_rust::build_identity`.
//!
//! k-rust's build script includes this file, and so does `tests/build_identity.rs`.
//!
//! **What is hashed.** Exactly the files the compiler reads for k-rust's library and binary,
//! and for the workspace crates they are built from ([`MEMBERS`]):
//! - every `.rs` file under each member's `src`, except the modules declared test-only;
//! - every file such a source embeds with `include_str!`, `include_bytes!` or `include!`
//!   (k-rust's `builtin/*.md`, `cparser/*`, `prelude.kore`).
//!
//! A module is test-only when its declaration sits at the start of a line of a hashed file
//! (outside any inline module) under an attribute line that is exactly `#[cfg(test)]`, with
//! only other attribute or comment lines in between. That excludes its file (`#[path]` honoured),
//! and for a module without `#[path]` also its directory of submodules.
//! An exclusion is withdrawn when a hashed file names the same file in a `#[path]` attribute or
//! an include macro, so a file the compiler reads for a non-test build is never left out.
//!
//! Embedded files outside the members' directories, or under a member's `tests` directory, are
//! test fixtures and are not hashed: only test code embeds them (the inline `#[cfg(test)]`
//! modules of `backend/wire.rs`, `rpc.rs` and others, which this scan does not delimit). A
//! non-test embed of such a file would be missed; keep embedded inputs inside a member's
//! `src`, `builtin` or `cparser`.
//!
//! Left out: names starting with `.` (editor swap and lock files), anything that is not a
//! regular file (symlinks, such as Emacs's dangling `.#name` locks), other files in the source
//! directories, tests, manifests and `Cargo.lock`.
//!
//! **Triggers.** Every hashed file is a `rerun-if-changed` trigger, and nothing else is. Each of
//! them already recompiles the library when it changes, so the build script adds no rebuild:
//! a rerun recompiles k-rust and its dependents even when the digest comes out unchanged, which
//! is why the manifests and the lockfile are neither hashed nor triggers.
//!
//! **Remaining lag.** An unreferenced `.rs` file added to a source directory joins the digest
//! at the next trigger. It is not part of the program until some hashed file declares it, and
//! that edit is such a trigger. A deleted or renamed trigger reruns the script.
//!
//! **What the identity does not cover.** The versions of crates.io dependencies (the lockfile),
//! features, and the profile (`opt-level`, `debug-assertions`). Paths are hashed relative to the
//! workspace with `/` separators. File bytes are hashed as they are, so a checkout with other
//! line endings is another identity.

use std::{
    collections::BTreeSet,
    fs,
    path::{Component, Path, PathBuf},
};

/// The crates whose sources make up k-rust: k-rust and its normal path dependencies,
/// transitively. `tests/build_identity.rs` checks the list against the manifests.
pub const MEMBERS: &[&str] = &["k-rust", "k-rust-kore", "k-rust-backend", "k-rust-regex"];

/// A digest and its rerun triggers.
#[derive(Debug)]
pub struct SourceDigest {
    /// The digest in hexadecimal, or `None` outside the workspace layout (a member missing
    /// beside `k-rust`, as in a crates.io package, whose sources are immutable anyway).
    pub digest: Option<String>,
    /// The hashed files, sorted: the build script's `rerun-if-changed` triggers.
    pub triggers: Vec<PathBuf>,
}

/// The digest of the sources of the k-rust whose manifest directory is `manifest`.
pub fn source_digest(manifest: &Path) -> SourceDigest {
    let unverified = SourceDigest {
        digest: None,
        triggers: Vec::new(),
    };
    let Some(crates) = manifest.parent() else {
        return unverified;
    };
    let Some(workspace) = crates.parent() else {
        return unverified;
    };
    let mut sources = Vec::new();
    for member in MEMBERS {
        let directory = crates.join(member);
        let named = fs::read_to_string(directory.join("Cargo.toml"))
            .is_ok_and(|text| text.contains(&format!("name = \"{member}\"")));
        if !named {
            return unverified;
        }
        rust_files(&directory.join("src"), &mut sources);
    }
    let texts: Vec<(PathBuf, String)> = sources
        .into_iter()
        .filter_map(|path| fs::read_to_string(&path).ok().map(|text| (path, text)))
        .collect();
    let mut excluded = BTreeSet::new();
    let mut path_targets = Vec::new();
    for (path, text) in &texts {
        path_targets.push(scan_modules(path, text, &mut excluded));
    }
    let is_excluded = |path: &Path| {
        excluded
            .iter()
            .any(|excluded: &PathBuf| path == excluded || path.starts_with(excluded))
    };
    let mut hashed: BTreeSet<PathBuf> = BTreeSet::new();
    let mut named_elsewhere = Vec::new();
    for ((path, text), path_targets) in texts.iter().zip(path_targets) {
        if is_excluded(path) {
            continue;
        }
        hashed.insert(path.clone());
        named_elsewhere.extend(path_targets);
        named_elsewhere.extend(included_files(manifest, path, text));
    }
    for target in named_elsewhere {
        let Some(target) = normalize(&target) else {
            continue;
        };
        let in_member = MEMBERS.iter().any(|member| {
            let member = crates.join(member);
            target.starts_with(&member) && !target.starts_with(member.join("tests"))
        });
        let regular = fs::symlink_metadata(&target).is_ok_and(|metadata| metadata.is_file());
        if regular && in_member {
            hashed.insert(target);
        }
    }
    let triggers: Vec<PathBuf> = hashed.into_iter().collect();
    SourceDigest {
        digest: Some(digest(workspace, &triggers)),
        triggers,
    }
}

/// Every regular, non-dot `.rs` file under `directory`.
fn rust_files(directory: &Path, files: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(directory) else {
        return;
    };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name.starts_with('.') {
            continue;
        }
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        let path = entry.path();
        if kind.is_dir() {
            rust_files(&path, files);
        } else if kind.is_file() && name.ends_with(".rs") {
            files.push(path);
        }
    }
}

/// The directory a file's `mod NAME;` declarations resolve against.
fn module_directory(file: &Path) -> PathBuf {
    let parent = file.parent().unwrap_or(Path::new("")).to_path_buf();
    match file.file_stem().and_then(|stem| stem.to_str()) {
        Some("lib" | "main" | "mod") | None => parent,
        Some(stem) => parent.join(stem),
    }
}

/// The name declared by a file-level `mod NAME;` line (any visibility), if `line` is one.
fn module_declaration(line: &str) -> Option<&str> {
    let rest = line.strip_prefix("pub ").unwrap_or(line);
    let rest = if rest.starts_with("pub(") {
        rest.split_once(") ")?.1
    } else {
        rest
    };
    let name = rest.strip_prefix("mod ")?.strip_suffix(';')?;
    name.chars()
        .all(|character| character.is_ascii_alphanumeric() || character == '_')
        .then_some(name)
}

/// The string of a `#[path = "..."]` attribute line.
fn path_attribute(line: &str) -> Option<&str> {
    line.trim().strip_prefix("#[path = \"")?.strip_suffix("\"]")
}

/// Add to `excluded` the files and directories of the test-only modules `file` declares, and
/// return the files its other `#[path]` attributes name (resolved against its directory).
fn scan_modules(file: &Path, text: &str, excluded: &mut BTreeSet<PathBuf>) -> Vec<PathBuf> {
    let directory = file.parent().unwrap_or(Path::new(""));
    let mut other_paths = Vec::new();
    let mut gated = false;
    let mut path = None;
    for line in text.lines() {
        if line == "#[cfg(test)]" {
            gated = true;
            path = None;
            continue;
        }
        let target = path_attribute(line);
        if !gated {
            if let Some(target) = target {
                other_paths.push(directory.join(target));
            }
            continue;
        }
        if let Some(target) = target.filter(|_| line.starts_with('#')) {
            path = Some(target.to_owned());
            continue;
        }
        if (line.starts_with("#[") && line.ends_with(']')) || line.starts_with("//") {
            continue;
        }
        match (module_declaration(line), path.take()) {
            (Some(_), Some(target)) => {
                excluded.insert(directory.join(target));
            }
            (Some(name), None) => {
                let modules = module_directory(file);
                excluded.insert(modules.join(format!("{name}.rs")));
                excluded.insert(modules.join(name));
            }
            // The gate applied to something else: a `#[path]` it carried names a file the
            // compiler may read.
            (None, Some(target)) => other_paths.push(directory.join(target)),
            (None, None) => {}
        }
        gated = false;
    }
    other_paths
}

/// The files `file` embeds with `include_str!`, `include_bytes!` or `include!`: string literals
/// joined, against `CARGO_MANIFEST_DIR` when the argument names it, else against the file's
/// directory, as the compiler resolves them.
fn included_files(manifest: &Path, file: &Path, text: &str) -> Vec<PathBuf> {
    let directory = file.parent().unwrap_or(Path::new(""));
    let mut files = Vec::new();
    for macro_name in ["include_str!(", "include_bytes!(", "include!("] {
        let mut rest = text;
        while let Some(start) = rest.find(macro_name) {
            rest = &rest[start + macro_name.len()..];
            let mut depth = 1;
            let mut end = rest.len();
            for (index, character) in rest.char_indices() {
                match character {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            end = index;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let argument = &rest[..end];
            let literals: String = argument
                .split('"')
                .skip(1)
                .step_by(2)
                .filter(|literal| *literal != "CARGO_MANIFEST_DIR")
                .collect();
            if literals.is_empty() {
                continue;
            }
            if argument.contains("env!(\"CARGO_MANIFEST_DIR\")") {
                files.push(manifest.join(literals.trim_start_matches('/')));
            } else {
                files.push(directory.join(literals));
            }
        }
    }
    files
}

/// `path` without `.` and `..` components, when it has a root to resolve them against.
fn normalize(path: &Path) -> Option<PathBuf> {
    let mut normal = PathBuf::new();
    for component in path.components() {
        match component {
            Component::ParentDir => {
                if !normal.pop() {
                    return None;
                }
            }
            Component::CurDir => {}
            other => normal.push(other),
        }
    }
    Some(normal)
}

/// A 128-bit FNV-1a digest of each file's path relative to `workspace` (with `/` separators)
/// and its bytes, in hexadecimal. It only needs to tell different sources apart, not to resist
/// an adversary.
fn digest(workspace: &Path, files: &[PathBuf]) -> String {
    const OFFSET: u128 = 0x6c62_272e_07bb_0142_62b8_2175_6295_c58d;
    const PRIME: u128 = 0x0000_0000_0100_0000_0000_0000_0000_013b;
    let mut hash = OFFSET;
    let mut feed = |bytes: &[u8]| {
        for &byte in bytes {
            hash ^= u128::from(byte);
            hash = hash.wrapping_mul(PRIME);
        }
    };
    for file in files {
        let relative = file.strip_prefix(workspace).unwrap_or(file);
        let relative = relative
            .components()
            .map(|component| component.as_os_str().to_string_lossy())
            .collect::<Vec<_>>()
            .join("/");
        let bytes = fs::read(file).unwrap_or_default();
        feed(relative.as_bytes());
        feed(&[0]);
        feed(&(bytes.len() as u64).to_le_bytes());
        feed(&bytes);
    }
    format!("{hash:032x}")
}
