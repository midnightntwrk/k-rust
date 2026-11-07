//! The guard families of a package lowered in process as `krs emit-k` lowers it
//! (`krs_compiler::guard_families` on the pre-derivation theory): the bit atoms of `k::bits!`
//! templates as the desugaring renders them, where every token of a sentence's template guards
//! takes one span that other templates and the condition's first authored node share; and, over
//! the patterns-functions definitions, that the families' reading of equation pairs contains every
//! pair the overlap check of equations finds may both apply.

use std::fs;
use std::path::{Path, PathBuf};

use krs_compiler::testing::equation_pairs_outside_guard_family_unifications;
use krs_compiler::{AtomKind, FlipOperator, GuardFamily, guard_families};
use krs_test_support::{shared_fixture_target, temp_dir};

const LIBRARY: &str = include_str!("fixtures/guard-families/src/lib.rs");

fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"GUARDS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            serde_json::to_string(krs.to_str().unwrap()).unwrap(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// The guard families of the `main` definition of a package holding `library`.
fn families(name: &str, library: &str) -> Vec<GuardFamily> {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), name, library);
    let retained = lowered(manifest, name, target.path()).unwrap();
    guard_families(retained.pre_derivation())
}

/// The `main` definition of package `name` at `manifest`, collected and lowered as `krs emit-k`
/// lowers it, or why collection or lowering refused it.
fn lowered(
    manifest: PathBuf,
    name: &str,
    target: &Path,
) -> Result<krs_compiler::RetainedLowering, String> {
    let request = krs_cli::CommandRequest {
        command: krs_cli::Command::Check {
            backend: None,
            partition: false,
        },
        manifest_path: manifest,
        root: krs_cli::FacetSelector {
            package: krs_cli::PackageSelector::Name(name.into()),
            definition: "main".into(),
        },
        dependencies: Vec::new(),
        cfg: Vec::new(),
        registration: krs_cli::RegistrationMode::Inventory,
        no_reuse: true,
        message_format: krs_cli::MessageFormat::Human,
        profile: None,
    };
    let collected =
        krs_cli::collect_descriptors(&request, Some(target)).map_err(|error| error.to_string())?;
    collected
        .emit_k_retained(collected.bundle.clone())
        .map(|emission| emission.retained)
        .map_err(|error| error.to_string())
}

/// The family whose first sentence is `first`.
fn family<'f>(families: &'f [GuardFamily], first: &str) -> &'f GuardFamily {
    families
        .iter()
        .find(|family| family.sentences[0].rule.item_name() == first)
        .unwrap_or_else(|| panic!("no family starting at {first}: {families:#?}"))
}

/// The flipped sentences of each obligation on the atom `kind`.
fn obligations(family: &GuardFamily, kind: &AtomKind) -> Vec<Vec<String>> {
    family
        .obligations
        .iter()
        .filter(|flip| family.atoms[flip.atom].kind == *kind)
        .map(|flip| {
            flip.sentences
                .iter()
                .map(|sentence| family.sentences[*sentence].rule.item_name().to_owned())
                .collect()
        })
        .collect()
}

fn names(groups: &[&[&str]]) -> Vec<Vec<String>> {
    groups
        .iter()
        .map(|group| group.iter().map(|name| (*name).to_owned()).collect())
        .collect()
}

#[test]
fn bit_atoms_of_lowered_templates() {
    let families = families("krs-cli-guard-families", LIBRARY);

    // The decode table: every template is one bit argument's condition, and the hole moves with
    // halt's literal.
    let decode = family(&families, "decode_dec_r");
    assert!(
        decode.not_generated.is_empty(),
        "{:#?}",
        decode.not_generated
    );
    assert!(
        decode
            .atoms
            .iter()
            .all(|atom| matches!(atom.kind, AtomKind::Bit { column: 0, .. })),
        "{:#?}",
        decode.atoms
    );
    assert_eq!(
        obligations(decode, &AtomKind::Bit { column: 0, bit: 0 }),
        names(&[
            &["decode_dec_r", "decode_inc_r"],
            &["decode_halt", "decode_ld_r_r"],
            &["decode_nop"],
        ])
    );

    // Two templates sharing one span are two bit arguments, and the flag that shares the span of
    // `pick_c`'s templates is a Boolean atom of its own.
    let pick = family(&families, "pick_a");
    assert!(pick.not_generated.is_empty(), "{:#?}", pick.not_generated);
    assert_eq!(
        obligations(pick, &AtomKind::Bit { column: 0, bit: 3 }),
        names(&[&["pick_a", "pick_b", "pick_c", "pick_d"]])
    );
    assert_eq!(
        obligations(pick, &AtomKind::Bit { column: 1, bit: 3 }),
        names(&[&["pick_a", "pick_b"]])
    );
    let flags = pick
        .obligations
        .iter()
        .filter(|flip| flip.operator == FlipOperator::Flip)
        .map(|flip| (&pick.atoms[flip.atom].kind, flip.sentences.clone()))
        .collect::<Vec<_>>();
    assert_eq!(
        flags,
        [(
            &AtomKind::Boolean {
                head: "flag".to_owned()
            },
            vec![2, 3]
        )]
    );
}

/// Copies `source` into `destination`, a manifest template `Cargo.toml.in` becoming `Cargo.toml`
/// with the facade's path filled in, and a workspace member's relative facade path made absolute.
fn materialize(source: &Path, destination: &Path, facade: &str) {
    fs::create_dir_all(destination).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        let name = entry.file_name();
        if name == "target" {
            continue;
        }
        if entry.file_type().unwrap().is_dir() {
            materialize(&path, &destination.join(&name), facade);
        } else if name == "Cargo.toml.in" || name == "Cargo.toml" {
            let manifest = fs::read_to_string(&path)
                .unwrap()
                .replace("@KRS_CRATE_PATH@", facade)
                .replace("\"../../../../crates/krs\"", facade);
            fs::write(destination.join("Cargo.toml"), manifest).unwrap();
        } else {
            fs::copy(&path, destination.join(&name)).unwrap();
        }
    }
}

/// The package name a manifest declares.
fn package_name(manifest: &Path) -> String {
    let text = fs::read_to_string(manifest).unwrap();
    let line = text
        .lines()
        .find(|line| line.trim_start().starts_with("name = "))
        .unwrap_or_else(|| panic!("{} names no package", manifest.display()));
    line.split('"').nth(1).unwrap().to_owned()
}

/// The guard families read two equations' heads with their own unifier, and that reading must
/// contain every pair the overlap check of equations finds may both apply (a pair it missed
/// would let a flip make two equations overlap that no family kept apart). Lowering asserts it in
/// test builds before it decides the equation check, so a refused fixture is checked as far as
/// lowering reached; an admitted definition is checked again here, counting its pairs.
#[test]
fn the_patterns_functions_equation_pairs_are_guard_family_pairs() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let krs = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let source = krs.join("tests/patterns-functions");
    let facade = serde_json::to_string(
        krs.join("crates/krs")
            .canonicalize()
            .unwrap()
            .to_str()
            .unwrap(),
    )
    .unwrap();
    let workspace = temporary.path().join("patterns-functions");
    fs::create_dir_all(&workspace).unwrap();
    for file in ["Cargo.toml", "Cargo.lock"] {
        fs::copy(source.join(file), workspace.join(file)).unwrap();
    }
    let mut manifests = Vec::new();
    for group in ["packages", "fixtures"] {
        let mut entries = fs::read_dir(source.join(group))
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.is_dir())
            .collect::<Vec<_>>();
        entries.sort();
        for entry in entries {
            let destination = workspace.join(group).join(entry.file_name().unwrap());
            materialize(&entry, &destination, &facade);
            manifests.push(destination.join("Cargo.toml"));
        }
    }
    let mut checked = 0;
    let mut admitted = 0;
    let mut equation_refusals = 0;
    let mut missing = Vec::new();
    for manifest in manifests {
        let name = package_name(&manifest);
        match lowered(manifest, &name, target.path()) {
            Ok(retained) => {
                let (pairs, outside) =
                    equation_pairs_outside_guard_family_unifications(retained.pre_derivation());
                admitted += 1;
                checked += pairs;
                missing.extend(outside.into_iter().map(|pair| format!("{name}: {pair}")));
            }
            // The equation check refused it, so lowering's assertion ran on its equations.
            Err(error) if error.starts_with("equations `") => equation_refusals += 1,
            Err(_) => {}
        }
    }
    assert!(missing.is_empty(), "{missing:#?}");
    // Every package lowers, the bit tables' equations give pairs to check, and the fixtures whose
    // equations overlap reach the assertion before the check refuses them.
    assert!(admitted >= 9, "{admitted} definitions lowered");
    assert!(checked > 0);
    assert!(
        equation_refusals >= 4,
        "{equation_refusals} equation refusals"
    );
}
