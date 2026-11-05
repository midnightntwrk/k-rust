//! Every declared cell has one kind, whichever view of its declaration a reader asks (S5.1).
//!
//! The collector's resolved declaration, which every compile-path reader asks for a cell's kind
//! (`krs_ir::cell_kind::DescriptorCell`), and the parsed source, which the macros and the class
//! oracle read (`krs_syntax::ConfigurationCell`), must give each cell the same `CellKind`. This
//! compares them over the class matrix's bases and the configuration-cells fixture packages,
//! whose cells hold every kind: plain, Map, List and cons-list leaves, computations, groups,
//! optional leaves and groups, and List, Set and Map collections. A fixture library another
//! fixture package depends on, such as a cell group with no configuration, is compared in the
//! definitions that hold it. The ports are compared by `krs-ports-emit` (`krs-gate cell-kinds`).

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use krs_ir::{DescriptorBundle, DescriptorIndex};
use krs_test_support::class_matrix::Base;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// Emits the `main` definition of the package at `manifest`, composed with the `main` definition
/// of each package of `dependencies`, and returns its descriptor bundle.
fn emitted_bundle(
    target: &Path,
    manifest: &Path,
    package: &str,
    dependencies: &[String],
    output: &Path,
) -> DescriptorBundle {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    process
        .args(["emit-k", "--ir", "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main", "--output"])
        .arg(output);
    for dependency in dependencies {
        process.args(["--dependency", &format!("{dependency}:main")]);
    }
    let emitted = process
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
            &[],
            &temporary.path().join(format!("{name}-emitted")),
        );
        let cells = agree(&name, &bundle, &[source]);
        println!("{base:?}: {cells} cells agree");
        compared += cells;
    }
    assert!(compared > 0, "the bases declare cells");
}

/// A fixture package: a member of the configuration-cells gate's workspace.
struct Fixture {
    /// The member's path below `packages/`, such as `group-harts/smp`.
    key: String,
    /// The member's directory.
    directory: PathBuf,
    /// The package name its manifest declares.
    package: String,
}

fn manifest(directory: &Path) -> toml_edit::DocumentMut {
    fs::read_to_string(directory.join("Cargo.toml"))
        .unwrap()
        .parse::<toml_edit::DocumentMut>()
        .unwrap()
}

/// The fixture packages: the members the gate's workspace manifest lists, which is what makes a
/// directory a fixture package, whatever its depth below `packages/`.
fn fixtures(workspace: &Path) -> Vec<Fixture> {
    let packages = workspace.join("packages");
    let root = manifest(workspace);
    let mut fixtures = root["workspace"]["members"]
        .as_array()
        .unwrap()
        .iter()
        .map(|member| {
            let directory = workspace
                .join(member.as_str().unwrap())
                .canonicalize()
                .unwrap();
            let key = directory
                .strip_prefix(&packages)
                .unwrap()
                .to_str()
                .unwrap()
                .to_owned();
            let package = manifest(&directory)["package"]["name"]
                .as_str()
                .unwrap()
                .to_owned();
            Fixture {
                key,
                directory,
                package,
            }
        })
        .collect::<Vec<_>>();
    fixtures.sort_by(|left, right| left.key.cmp(&right.key));
    fixtures
}

/// The fixture packages, by key, that the fixture package in `directory` depends on by path:
/// each dependency whose path is another fixture's directory.
fn fixture_dependencies(keys: &BTreeMap<PathBuf, String>, directory: &Path) -> Vec<String> {
    let manifest = manifest(directory);
    let Some(dependencies) = manifest
        .get("dependencies")
        .and_then(toml_edit::Item::as_table_like)
    else {
        return Vec::new();
    };
    let mut names = dependencies
        .iter()
        .filter_map(|(_, dependency)| {
            let path = directory.join(dependency.get("path")?.as_str()?);
            keys.get(&path.canonicalize().ok()?).cloned()
        })
        .collect::<Vec<_>>();
    names.sort();
    names
}

/// The Rust sources under `directory`'s `src`.
fn package_sources(directory: &Path) -> Vec<String> {
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
    sources
}

/// Every fixture package's cells, each compared in the definition of a package that is no other
/// fixture package's dependency. A library another package depends on is compared in each such
/// definition that holds it, with the library's sources beside the package's own, and is not
/// emitted on its own: a library of rules for a cell group declares no configuration.
#[test]
fn every_configuration_cells_fixture_cell_has_one_kind_collected_and_parsed() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/configuration-cells")
        .canonicalize()
        .unwrap();
    let fixtures = fixtures(&workspace);
    assert!(!fixtures.is_empty());
    let keys = fixtures
        .iter()
        .map(|fixture| (fixture.directory.clone(), fixture.key.clone()))
        .collect::<BTreeMap<_, _>>();
    let by_key = fixtures
        .iter()
        .map(|fixture| (fixture.key.as_str(), fixture))
        .collect::<BTreeMap<_, _>>();
    let dependencies = fixtures
        .iter()
        .map(|fixture| {
            (
                fixture.key.clone(),
                fixture_dependencies(&keys, &fixture.directory),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let libraries = dependencies.values().flatten().collect::<BTreeSet<_>>();
    let mut held = BTreeSet::new();
    for fixture in &fixtures {
        let name = &fixture.key;
        if libraries.contains(name) {
            continue;
        }
        let bundle = emitted_bundle(
            target.path(),
            &fixture.directory.join("Cargo.toml"),
            &fixture.package,
            &dependencies[name]
                .iter()
                .map(|dependency| by_key[dependency.as_str()].package.clone())
                .collect::<Vec<_>>(),
            &temporary.path().join(name.replace('/', "-")),
        );
        let mut sources = package_sources(&fixture.directory);
        for dependency in &dependencies[name] {
            sources.extend(package_sources(&by_key[dependency.as_str()].directory));
            held.insert(dependency);
        }
        let cells = agree(name, &bundle, &sources);
        assert!(cells > 0, "{name} declares cells");
        println!("{name}: {cells} cells agree");
    }
    assert_eq!(
        held, libraries,
        "every library is compared in a definition that holds it"
    );
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
        &[],
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
