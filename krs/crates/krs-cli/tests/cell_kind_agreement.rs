//! Every declared cell has one kind, whichever view of its declaration a reader asks (S5.1).
//!
//! The collector's resolved declaration, which every compile-path reader asks for a cell's kind
//! (`krs_ir::cell_kind::DescriptorCell`), and the parsed source, which the macros and the class
//! oracle read (`krs_syntax::ConfigurationCell`), must give each cell the same `CellKind`. This
//! compares them over the class matrix's bases and the configuration-cells fixture packages,
//! whose cells hold every kind: plain, Map, List and cons-list leaves, computations, groups,
//! optional leaves and groups, and List, Set and Map collections. The ports are compared by
//! `krs-ports-emit` (`krs-gate cell-kinds`).

use std::fs;
use std::path::{Path, PathBuf};

use krs_ir::{DescriptorBundle, DescriptorIndex};
use krs_test_support::class_matrix::Base;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// Emits the `main` definition of the package at `manifest` and returns its descriptor bundle.
fn emitted_bundle(
    target: &Path,
    manifest: &Path,
    package: &str,
    output: &Path,
) -> DescriptorBundle {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let emitted = process
        .args(["emit-k", "--ir", "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main", "--output"])
        .arg(output)
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    assert!(
        emitted.status.success(),
        "{package}: {}",
        String::from_utf8_lossy(&emitted.stderr)
    );
    serde_json::from_slice(&fs::read(output.join("descriptor-bundle.json")).unwrap()).unwrap()
}

/// Compares the kinds of the cells `bundle` declares with those `sources` declare, and returns
/// how many cells were compared.
fn agree(name: &str, bundle: &DescriptorBundle, sources: &[String]) -> usize {
    let files = sources
        .iter()
        .map(|source| syn::parse_file(source).unwrap())
        .collect::<Vec<_>>();
    krs_syntax::cell_kind_agreement::agreement(&DescriptorIndex::new(bundle), &files)
        .unwrap_or_else(|failures| panic!("{name}: {failures:#?}"))
}

fn write_package(directory: &Path, name: &str, source: &str) -> PathBuf {
    let facade = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    let manifest = directory.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n\
             [dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n\
             [package.metadata.krs]\nk-namespace = \"ORG-KRS-CLASS\"\n\n\
             [package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            serde_json::to_string(facade.to_str().unwrap()).unwrap(),
        ),
    )
    .unwrap();
    manifest
}

#[test]
fn every_class_base_cell_has_one_kind_collected_and_parsed() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let mut compared = 0;
    for base in Base::ALL {
        let name = format!("cell-kinds-{}", format!("{base:?}").to_lowercase());
        let source = base.preamble();
        let manifest = write_package(&temporary.path().join(&name), &name, &source);
        let bundle = emitted_bundle(
            target.path(),
            &manifest,
            &name,
            &temporary.path().join(format!("{name}-emitted")),
        );
        let cells = agree(&name, &bundle, &[source]);
        println!("{base:?}: {cells} cells agree");
        compared += cells;
    }
    assert!(compared > 0, "the bases declare cells");
}

#[test]
fn every_configuration_cells_fixture_cell_has_one_kind_collected_and_parsed() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let packages = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/configuration-cells/packages")
        .canonicalize()
        .unwrap();
    let mut names = fs::read_dir(&packages)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect::<Vec<_>>();
    names.sort();
    assert!(!names.is_empty());
    for name in names {
        let directory = packages.join(&name);
        let package = format!("krs-configuration-cells-{name}");
        let bundle = emitted_bundle(
            target.path(),
            &directory.join("Cargo.toml"),
            &package,
            &temporary.path().join(&name),
        );
        let mut sources = Vec::new();
        let mut paths = vec![directory.join("src")];
        while let Some(path) = paths.pop() {
            for entry in fs::read_dir(path).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    paths.push(path);
                } else if path.extension().is_some_and(|extension| extension == "rs") {
                    sources.push(fs::read_to_string(path).unwrap());
                }
            }
        }
        let cells = agree(&name, &bundle, &sources);
        assert!(cells > 0, "{name} declares cells");
        println!("{name}: {cells} cells agree");
    }
}

/// A configuration whose `saved` cell is an explicit `Cell<KSequence>`: a leaf of sort `K`,
/// which a `Cell(..)` entry reads as one term. Both views read the computation as a `KCell`'s
/// content, so both give `saved` a plain leaf's kind and `k` a computation's.
const EXPLICIT_WRAPPERS: &str = r#"
use k::KResult;
use k::builtin::{Int, KSequence, List};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("bump")]
    Bump(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: k::configuration::KCell<KSequence>,
    #[k::cell]
    pub stack: k::configuration::Cell<List>,
    #[k::cell]
    pub saved: k::configuration::Cell<KSequence>,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "SAVED")] saved: KSequence,
    ) -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![pgm]),
            stack: k::configuration::Cell::new(k::builtin::list::empty()),
            saved: k::configuration::Cell::new(saved),
        }
    }
}
"#;

#[test]
fn an_explicit_cell_of_ksequence_is_a_leaf_in_both_views() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let name = "cell-kinds-explicit-wrappers";
    let manifest = write_package(&temporary.path().join(name), name, EXPLICIT_WRAPPERS);
    let bundle = emitted_bundle(
        target.path(),
        &manifest,
        name,
        &temporary.path().join("emitted"),
    );
    assert_eq!(agree(name, &bundle, &[EXPLICIT_WRAPPERS.to_owned()]), 3);
    let index = DescriptorIndex::new(&bundle);
    let saved = bundle
        .descriptors()
        .iter()
        .find_map(|descriptor| match descriptor.payload() {
            krs_ir::DescriptorPayload::FixedConfiguration(configuration) => configuration
                .declaration
                .fields
                .iter()
                .find(|field| field.rust_field == "saved"),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        krs_ir::cell_kind::DescriptorCell::new(saved, &index)
            .kind()
            .layers,
        vec![krs_ir::cell_kind::Layer::Leaf(
            krs_ir::cell_kind::Notation::Plain
        )]
    );
}
