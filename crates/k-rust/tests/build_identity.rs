//! The build identity (`k_rust::build_identity`) and the source digest k-rust's build script
//! computes for it (`build/source_digest.rs`, included here as the build script includes it).
//!
//! The digest must name exactly the files the compiler reads for k-rust's library and binary:
//! a test-only module, a stray file, a dotfile or a dangling editor lock never changes it or
//! makes it unavailable, and every hashed file is a rerun trigger.

#[path = "../build/source_digest.rs"]
#[allow(
    dead_code,
    reason = "the build script uses every item; this test a subset"
)]
mod source_digest;

use std::{
    fs,
    path::{Path, PathBuf},
};

use source_digest::{MEMBERS, SourceDigest, source_digest};

/// A workspace in the layout the build script expects, with one file of each kind.
fn layout(test: &str) -> PathBuf {
    let root = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("build-identity")
        .join(test);
    let _ = fs::remove_dir_all(&root);
    let write = |path: &str, text: &str| {
        let path = root.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    };
    for member in MEMBERS {
        write(
            &format!("crates/{member}/Cargo.toml"),
            &format!("[package]\nname = \"{member}\"\n"),
        );
        write(&format!("crates/{member}/src/lib.rs"), "pub fn f() {}\n");
    }
    write(
        "crates/k-rust/src/lib.rs",
        concat!(
            "mod a;\n",
            "#[cfg(test)]\n",
            "mod tests;\n",
            "#[cfg(test)]\n",
            "#[path = \"props_impl.rs\"]\n",
            "mod props;\n",
            "pub const B: &str = include_str!(\"../builtin/b.md\");\n",
            "#[cfg(test)]\n",
            "mod fixtures {\n",
            "    const F: &str = include_str!(\"../tests/fixture.txt\");\n",
            "}\n",
        ),
    );
    write("crates/k-rust/src/a.rs", "pub fn a() {}\n");
    write("crates/k-rust/src/tests.rs", "#[test]\nfn t() {}\n");
    write("crates/k-rust/src/tests/deep.rs", "fn d() {}\n");
    write("crates/k-rust/src/props_impl.rs", "fn p() {}\n");
    write("crates/k-rust/builtin/b.md", "builtin\n");
    write("crates/k-rust/builtin/unused.md", "not included\n");
    write("crates/k-rust/tests/fixture.txt", "fixture\n");
    write("Cargo.lock", "# lock\n");
    root
}

fn digest_of(root: &Path) -> SourceDigest {
    source_digest(&root.join("crates/k-rust"))
}

fn relative(root: &Path, digest: &SourceDigest) -> Vec<String> {
    digest
        .triggers
        .iter()
        .map(|path| {
            path.strip_prefix(root)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/")
        })
        .collect()
}

#[test]
fn the_digest_names_exactly_the_files_the_compiler_reads() {
    let root = layout("exact");
    let digest = digest_of(&root);
    assert!(digest.digest.is_some());
    assert_eq!(
        relative(&root, &digest),
        // Sorted by path component, so `k-rust/…` precedes `k-rust-backend/…`.
        [
            "crates/k-rust/builtin/b.md",
            "crates/k-rust/src/a.rs",
            "crates/k-rust/src/lib.rs",
            "crates/k-rust-backend/src/lib.rs",
            "crates/k-rust-kore/src/lib.rs",
            "crates/k-rust-regex/src/lib.rs",
        ]
    );
}

#[test]
fn files_the_compiler_does_not_read_leave_the_digest_unchanged() {
    let root = layout("stray");
    let before = digest_of(&root).digest.expect("verified");
    let edits: [(&str, &str); 6] = [
        ("crates/k-rust/src/tests.rs", "#[test]\nfn changed() {}\n"),
        ("crates/k-rust/src/tests/deep.rs", "fn changed() {}\n"),
        ("crates/k-rust/src/props_impl.rs", "fn changed() {}\n"),
        ("crates/k-rust/src/notes.txt", "notes\n"),
        ("crates/k-rust/builtin/unused.md", "changed\n"),
        ("crates/k-rust/tests/fixture.txt", "changed\n"),
    ];
    for (path, text) in edits {
        fs::write(root.join(path), text).unwrap();
    }
    fs::write(root.join("crates/k-rust/src/.a.rs.swp"), "swap").unwrap();
    fs::write(root.join("Cargo.lock"), "# another lock\n").unwrap();
    #[cfg(unix)]
    std::os::unix::fs::symlink(
        "user@host.1234:1700000000",
        root.join("crates/k-rust/src/.#a.rs"),
    )
    .unwrap();
    let after = digest_of(&root);
    assert_eq!(after.digest.as_deref(), Some(before.as_str()));
    assert!(
        !relative(&root, &after)
            .iter()
            .any(|path| path.contains("notes") || path.contains(".#") || path.contains("swp")),
        "{:?}",
        after.triggers
    );
}

#[test]
fn an_edit_of_a_compiled_file_changes_the_digest_and_its_revert_restores_it() {
    let root = layout("edit");
    let before = digest_of(&root).digest.expect("verified");
    for path in ["crates/k-rust/src/a.rs", "crates/k-rust/builtin/b.md"] {
        let original = fs::read_to_string(root.join(path)).unwrap();
        fs::write(root.join(path), format!("{original}// edited\n")).unwrap();
        let edited = digest_of(&root).digest.expect("verified");
        assert_ne!(edited, before, "{path}");
        fs::write(root.join(path), original).unwrap();
        assert_eq!(digest_of(&root).digest.as_deref(), Some(before.as_str()));
    }
}

#[test]
fn a_missing_member_makes_the_build_unverified() {
    let root = layout("missing");
    fs::remove_dir_all(root.join("crates/k-rust-regex")).unwrap();
    assert_eq!(digest_of(&root).digest, None);
}

/// The hashed members are k-rust's normal path dependencies, transitively: a new path
/// dependency must join `MEMBERS`, or its sources would be left out of the identity.
#[test]
fn the_members_are_k_rusts_path_dependency_closure() {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let workspace: toml::Table =
        toml::from_str(&fs::read_to_string(crates.join("../Cargo.toml")).unwrap()).unwrap();
    let workspace_paths = workspace["workspace"]["dependencies"]
        .as_table()
        .unwrap()
        .iter()
        .filter(|(_, value)| value.get("path").is_some())
        .map(|(name, _)| name.clone())
        .collect::<Vec<_>>();
    let mut closure = vec!["k-rust".to_owned()];
    let mut index = 0;
    while index < closure.len() {
        let manifest: toml::Table = toml::from_str(
            &fs::read_to_string(crates.join(&closure[index]).join("Cargo.toml")).unwrap(),
        )
        .unwrap();
        for table in ["dependencies", "build-dependencies"] {
            let Some(dependencies) = manifest.get(table).and_then(toml::Value::as_table) else {
                continue;
            };
            for (name, value) in dependencies {
                let is_path = value.get("path").is_some()
                    || (value.get("workspace").is_some() && workspace_paths.contains(name));
                if is_path && !closure.contains(name) {
                    closure.push(name.clone());
                }
            }
        }
        index += 1;
    }
    closure.sort();
    let mut members = MEMBERS
        .iter()
        .map(|name| (*name).to_owned())
        .collect::<Vec<_>>();
    members.sort();
    assert_eq!(closure, members);
}

#[test]
fn this_build_is_verified_and_names_its_digest() {
    let identity = k_rust::build_identity();
    assert!(k_rust::is_verified_build(&identity), "{identity}");
    assert!(
        identity.starts_with(&format!("{}+src.", env!("CARGO_PKG_VERSION"))),
        "{identity}"
    );
    let actual = source_digest(Path::new(env!("CARGO_MANIFEST_DIR")))
        .digest
        .expect("this workspace has the layout");
    assert!(identity.ends_with(&actual), "{identity} vs {actual}");
}
