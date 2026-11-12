//! COMPOSITION-DECLARED: a definition facet declares the dependency facets and the cfg values it
//! is composed with (`[package.metadata.krs.definitions.<facet>]` `dependencies` and `cfg`), and
//! every command reads them for each kind its command line does not give.
//!
//! The composition is part of what the definition is: its rules and its configuration differ by
//! it. Stated with the definition, two commands without `--dependency` or `--cfg` select one
//! definition, and a composition given by declaration is the one the same flags give.
//!
//! The workspace is the composition tour's two packages (`krs/tests/tour-composition`) and
//! `extra-semantics`, a third package the root depends on and no source names, so that whether
//! its facet is composed shows in the emitted K alone; `observe-semantics`, an observer of the
//! root, and `helper-semantics`, a package outside the root's closure that the observer depends
//! on and whose facet the observer's own table declares (OBSERVER-COMPOSITION).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};

const BASE: &str =
    include_str!("../../../tests/tour-composition/packages/base-semantics/src/lib.rs");
const ROOT: &str =
    include_str!("../../../tests/tour-composition/packages/root-semantics/src/lib.rs");
const EXTRA: &str = r#"//! A dependency semantics package that no source of the root names.

use language_host as k;

#[k::sort(alias = ExtraItem)]
pub trait ExtraItemSort {}
pub type ExtraItem = k::Term<dyn ExtraItemSort>;

#[k::constructor(sort = ExtraItem, syntax = "extra-unit")]
pub struct ExtraUnit;
"#;

/// A package of functions outside the root's dependency closure, which the observer depends on.
const HELPER: &str = r"//! A function no semantics depends on.

use k::Term;
use k::builtin::Int;

/// The successor.
#[k::function(total, internal)]
pub fn Bump(value: Term<Int>) -> Term<Int> {
    value + 1
}
";

/// An observer of the root definition: a view of its `k` cell built from the helper's function,
/// in a package no semantics imports.
const OBSERVE: &str = r"//! A view of the root definition's `k` cell.

use k::Term;
use k::builtin::{Int, KSequence};

/// One, whatever the cell holds.
#[k::function(total, internal)]
pub fn Seen(_cell: Term<KSequence>) -> Term<Int> {
    helper::Bump(0)
}
";

/// The module of `helper-semantics`, in the K of a definition that composes its facet.
const HELPER_MODULE: &str = "ORG-KRS-DECLARED-HELPER";
/// What the observer's facet `views` declares in [`Workspace::new`]: the helper's facet, which
/// is outside the root's closure.
const OBSERVER_DECLARATION: &str = "dependencies = [\"helper-semantics:helper\"]\n";
const OBSERVER_KEY: &str =
    "`package.metadata.krs.definitions.views.dependencies` of package `observe-semantics`";
const OBSERVER: [&str; 2] = ["--observer", "observe-semantics:views"];

/// The module of `extra-semantics`, in the K of a definition that composes its facet.
const EXTRA_MODULE: &str = "ORG-KRS-DECLARED-EXTRA";
/// The production the root declares under `cfg(tour_mode = "extended")`.
const EXTENDED: &str = "[symbol(extended)]";
/// The composition the workspace of [`Workspace::declared`] declares, as flags.
const AS_FLAGS: [&str; 6] = [
    "--dependency",
    "extra-semantics:extra",
    "--dependency",
    "base-semantics:base",
    "--cfg",
    "tour_mode=extended",
];
const SELECTION: [&str; 4] = ["--package", "root-semantics", "--definition", "main"];
const KEY: &str =
    "`package.metadata.krs.definitions.main.dependencies` of package `root-semantics`";

/// The tour's two packages and `extra-semantics`, the root's facet `main` declaring
/// `declaration` (the lines of its table), with `helper-semantics`, outside the root's closure,
/// and `observe-semantics`, an observer of the root that depends on it and whose facet `views`
/// declares [`OBSERVER_DECLARATION`].
struct Workspace {
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Workspace {
    fn new(declaration: &str) -> Self {
        let workspace = Self {
            directory: temp_dir(),
            target: shared_fixture_target(),
        };
        workspace.write(
            "Cargo.toml",
            "[workspace]\nmembers = [\"base\", \"extra\", \"root\", \"helper\", \"observe\"]\nresolver = \"3\"\n\n[workspace.lints.rust]\nunexpected_cfgs = { level = \"warn\", check-cfg = ['cfg(tour_mode, values(\"extended\"))'] }\n",
        );
        workspace.write(
            "base/Cargo.toml",
            &manifest(
                "base-semantics",
                "base_language_api",
                "BASE",
                "",
                "base",
                "",
            ),
        );
        workspace.write("base/src/lib.rs", BASE);
        workspace.write(
            "extra/Cargo.toml",
            &manifest(
                "extra-semantics",
                "extra_language_api",
                "EXTRA",
                "",
                "extra",
                "",
            ),
        );
        workspace.write("extra/src/lib.rs", EXTRA);
        workspace.write("root/src/lib.rs", ROOT);
        workspace.write(
            "helper/Cargo.toml",
            &format!(
                "[package]\nname = \"helper-semantics\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"{HELPER_MODULE}\"\n\n[package.metadata.krs.definitions.helper]\n",
                krs_path()
            ),
        );
        workspace.write("helper/src/lib.rs", HELPER);
        workspace.write("observe/src/lib.rs", OBSERVE);
        workspace.declare_observer(OBSERVER_DECLARATION);
        workspace.declare(declaration);
        workspace
    }

    /// Rewrites the observer's manifest so that its facet `views` declares `declaration`.
    fn declare_observer(&self, declaration: &str) {
        self.write(
            "observe/Cargo.toml",
            &format!(
                "[package]\nname = \"observe-semantics\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\nroot = {{ package = \"root-semantics\", path = \"../root\" }}\nhelper = {{ package = \"helper-semantics\", path = \"../helper\" }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-DECLARED-OBSERVE\"\n\n[package.metadata.krs.definitions.views]\n{declaration}",
                krs_path()
            ),
        );
    }

    /// The workspace whose root declares both dependency facets and the tour's cfg value.
    fn declared() -> Self {
        Self::new(
            "dependencies = [\"base-semantics:base\", \"extra-semantics:extra\"]\ncfg = [\"tour_mode=extended\"]\n",
        )
    }

    /// Rewrites the root's manifest so that its facet `main` declares `declaration`.
    fn declare(&self, declaration: &str) {
        self.write(
            "root/Cargo.toml",
            &manifest(
                "root-semantics",
                "root_language_api",
                "ROOT",
                "semantic-base = { package = \"base-semantics\", path = \"../base\" }\nsemantic-extra = { package = \"extra-semantics\", path = \"../extra\" }\n",
                "main",
                declaration,
            ),
        );
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.directory.path().join(relative)
    }

    fn write(&self, relative: &str, contents: &str) {
        let path = self.path(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    /// `krs ARGUMENTS` from the workspace root.
    fn krs(&self, arguments: &[&str]) -> Output {
        self.krs_with(arguments, &[])
    }

    /// [`Self::krs`] with the environment variables `environment` set.
    fn krs_with(&self, arguments: &[&str], environment: &[(&str, &Path)]) -> Output {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        for (name, value) in environment {
            process.env(name, value);
        }
        process
            .current_dir(self.directory.path())
            .args(arguments)
            .env("NO_COLOR", "1")
            .output()
            .unwrap()
    }

    /// The root definition's end, written to `end.json`.
    #[track_caller]
    fn write_end(&self) {
        let end = self.krs(&[&["run"][..], &SELECTION, &["--output", "end"]].concat());
        assert!(end.status.success(), "{}", stderr(&end));
        self.write("end.json", &stdout(&end));
    }

    /// `krs compare end.json end.json` under the observer's view, with the flags `composition`.
    fn observe(&self, composition: &[&str]) -> Output {
        self.krs(
            &[
                &["compare"][..],
                &SELECTION,
                &["end.json", "end.json", "--compare", "k", "--view", "k=Seen"],
                &OBSERVER,
                composition,
            ]
            .concat(),
        )
    }

    /// The composition each prepared definition's record in the fixture target names in its
    /// key, for the records of the commands given this workspace's manifest by its absolute
    /// path: the root facet's name, and the dependency facets as `PACKAGE:FACET`.
    fn recorded_compositions(&self) -> Vec<(String, Vec<String>)> {
        let manifest = self.path("Cargo.toml");
        let collectors = self.target.path().join("krs/collectors");
        let mut compositions = Vec::new();
        for collector in fs::read_dir(collectors).unwrap().flatten() {
            let Ok(record) = fs::read(collector.path().join("krs-definition.bin")) else {
                continue;
            };
            // A record is the length of its header, then the header, whose `composition` is the
            // key's JSON.
            let length =
                usize::try_from(u64::from_le_bytes(record[..8].try_into().unwrap())).unwrap();
            let header: serde_json::Value = serde_json::from_slice(&record[8..8 + length]).unwrap();
            let key: serde_json::Value =
                serde_json::from_str(header["composition"].as_str().unwrap()).unwrap();
            let path = key["manifest_path"]
                .as_array()
                .unwrap()
                .iter()
                .map(|byte| u8::try_from(byte.as_u64().unwrap()).unwrap())
                .collect::<Vec<_>>();
            if path != manifest.to_str().unwrap().as_bytes() {
                continue;
            }
            let facet = |facet: &serde_json::Value| {
                format!(
                    "{}:{}",
                    facet["package"]["Name"].as_str().unwrap(),
                    facet["definition"].as_str().unwrap()
                )
            };
            compositions.push((
                facet(&key["root"]),
                key["dependencies"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(facet)
                    .collect(),
            ));
        }
        compositions.sort();
        compositions
    }

    /// The K `krs emit-k` writes for the root's definition with the flags `composition`.
    #[track_caller]
    fn emitted(&self, name: &str, composition: &[&str]) -> String {
        let output = self.path(name);
        let emit = self.krs(
            &[
                &["emit-k"][..],
                &SELECTION,
                composition,
                &["--output", output.to_str().unwrap()],
            ]
            .concat(),
        );
        assert!(emit.status.success(), "{}", stderr(&emit));
        fs::read_to_string(output.join("definition.k")).unwrap()
    }
}

/// The number of compiled stages under the stage store `directory`.
fn stored_stages(directory: &Path) -> usize {
    fs::read_dir(directory).map_or(0, |entries| {
        entries
            .flatten()
            .map(|entry| {
                let path = entry.path();
                if path.is_dir() {
                    stored_stages(&path)
                } else {
                    usize::from(path.extension().is_some_and(|stage| stage == "stage"))
                }
            })
            .sum()
    })
}

/// The `krs` crate's directory, as a TOML string.
fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

fn manifest(
    name: &str,
    library: &str,
    namespace: &str,
    dependencies: &str,
    facet: &str,
    declaration: &str,
) -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let krs = serde_json::to_string(krs.to_str().unwrap()).unwrap();
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n\n[lib]\nname = \"{library}\"\n\n[dependencies]\nlanguage-host = {{ package = \"krs\", path = {krs} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-DECLARED-{namespace}\"\n\n[package.metadata.krs.definitions.{facet}]\n{declaration}\n[lints]\nworkspace = true\n"
    )
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// The checked-in composition tour declares its dependency facet, so its root checks and runs
/// with no `--dependency`, and a `--cfg` beside it leaves the declared dependencies in place:
/// the command line replaces only the kind it gives.
#[test]
fn the_composition_tour_checks_and_runs_on_its_declaration() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/tour-composition/Cargo.toml")
        .canonicalize()
        .unwrap();
    // Built outside the checked-in fixture, whose directory holds its sources only.
    let target = shared_fixture_target();
    let krs = |arguments: &[&str]| {
        let mut process = krs_command!();
        fixture_build_env(&mut process, target.path());
        process
            .arg(arguments[0])
            .arg("--manifest-path")
            .arg(&manifest)
            .args(SELECTION)
            .args(&arguments[1..])
            .env("NO_COLOR", "1")
            .output()
            .unwrap()
    };
    let check = krs(&["check"]);
    assert!(check.status.success(), "{}", stderr(&check));
    let configured = krs(&["check", "--cfg", "tour_mode=extended"]);
    assert!(configured.status.success(), "{}", stderr(&configured));
    let run = krs(&["run", "--output", "pretty"]);
    assert!(run.status.success(), "{}", stderr(&run));
    assert!(stdout(&run).contains("same - root"), "{}", stdout(&run));
}

/// A composition given by declaration is the definition the same flags give: `krs emit-k` writes
/// the same files for both, so everything that records what definition it is of (the emitted K,
/// its symbol and source maps, and a digest of them) is one for the two spellings.
/// The command line replaces a declared kind whole and leaves the other kind as declared.
#[test]
fn flags_replace_a_declared_kind_and_the_same_composition_is_the_same_definition() {
    let workspace = Workspace::declared();
    let declared = workspace.emitted("declared", &[]);
    assert!(declared.contains(EXTRA_MODULE), "{declared}");
    assert!(declared.contains(EXTENDED), "{declared}");

    workspace.emitted("flags", &AS_FLAGS);
    for file in ["definition.k", "symbols.json", "sources.json"] {
        assert_eq!(
            fs::read(workspace.path("declared").join(file)).unwrap(),
            fs::read(workspace.path("flags").join(file)).unwrap(),
            "{file} differs between the declared composition and the same one given by flags"
        );
    }

    // `--dependency` replaces the declared dependency facets; the declared cfg values stay.
    let one_dependency =
        workspace.emitted("one-dependency", &["--dependency", "base-semantics:base"]);
    assert!(!one_dependency.contains(EXTRA_MODULE), "{one_dependency}");
    assert!(one_dependency.contains(EXTENDED), "{one_dependency}");

    // `--cfg` replaces the declared cfg values; the declared dependency facets stay.
    let other_cfg = workspace.emitted("other-cfg", &["--cfg", "another"]);
    assert!(other_cfg.contains(EXTRA_MODULE), "{other_cfg}");
    assert!(!other_cfg.contains(EXTENDED), "{other_cfg}");
}

/// RUN-WARM-START: the prepared definition a run restores is its own composition's. A run
/// restores the record an earlier run of the same composition stored; another cfg value or
/// another dependency facet, given by a flag or by the facet's declaration, is another
/// definition, which is lowered: its record is not the first composition's, whose runs go on
/// restoring their own.
#[test]
fn a_run_restores_the_prepared_definition_of_its_own_composition_only() {
    let workspace = Workspace::declared();
    let counters = workspace.path("counters.json");
    let run = |composition: &[&str]| {
        let run = workspace.krs(
            &[
                &["run"][..],
                &SELECTION,
                composition,
                &["--output", "end", "--counters", counters.to_str().unwrap()],
            ]
            .concat(),
        );
        assert!(run.status.success(), "{}", stderr(&run));
        let document: serde_json::Value =
            serde_json::from_slice(&fs::read(&counters).unwrap()).unwrap();
        let counted = |name: &str| document["counters"][name].as_u64().unwrap();
        (
            stdout(&run),
            counted("definition.reused"),
            counted("definition.modules"),
        )
    };

    let (declared, reused, declared_modules) = run(&[]);
    assert_eq!(reused, 0);
    assert_eq!(run(&[]), (declared.clone(), 1, declared_modules));

    // Another cfg value, then another dependency selection, by flags: each is lowered, and
    // then restored by its own next run.
    let (_, reused, _) = run(&["--cfg", "another"]);
    assert_eq!(reused, 0);
    assert_eq!(run(&["--cfg", "another"]).1, 1);
    let (_, reused, one_dependency_modules) = run(&["--dependency", "base-semantics:base"]);
    assert_eq!(reused, 0);
    // The definition without the facet of `extra-semantics` is without its modules.
    assert!(
        one_dependency_modules < declared_modules,
        "{one_dependency_modules} modules without the facet, {declared_modules} with it"
    );
    assert_eq!(run(&[]), (declared.clone(), 1, declared_modules));

    // Another declaration, with the same command line: the definition the manifest now
    // declares is lowered, not restored from the record of the one it declared.
    workspace.declare("dependencies = [\"base-semantics:base\"]\n");
    let (_, reused, modules) = run(&[]);
    assert_eq!(reused, 0);
    assert_eq!(modules, one_dependency_modules);
    assert_eq!(run(&[]).1, 1);
}

/// An observer is composed with the definition and the dependency facets of its composition, so
/// the observer of a definition with a declared composition composes the declared facets: the
/// root's sources name `base-semantics`, which the observer holds without a `--dependency`.
/// It composes too the facet its own table declares (OBSERVER-COMPOSITION): its view applies a
/// function of `helper-semantics`, which the root's closure does not hold.
#[test]
fn an_observer_composes_the_declared_facets_of_the_definition() {
    let workspace = Workspace::declared();
    workspace.write_end();
    let compare = workspace.observe(&[]);
    assert_eq!(compare.status.code(), Some(0), "{}", stderr(&compare));
    assert_eq!(
        stdout(&compare),
        "krs compare: equal\n  views: `k` = `Seen`, in `observe-semantics:views`\n"
    );
}

/// OBSERVER-COMPOSITION: what an observer needs beside the definition it observes is the
/// observer's own statement, the `dependencies` key of its facet's table, and it adds to the
/// observer's composition alone. The definition is planned from its own declaration, so with
/// the observer in play it is the definition it was: the same emitted K and maps, the same
/// Definition IR (its compiled stage, whose key digests it, is not stored again), and the same
/// record of its prepared definition, which its next run restores. The observer's record is
/// keyed by its own composition, which holds what it adds; the definition's key does not.
/// Without the declaration the observer is refused, naming the observer's key, and the facet
/// given by `--dependency` composes as before, with the definition's list restated, since flags
/// replace the definition's declaration.
#[test]
fn an_observer_adds_the_facets_it_declares_and_leaves_the_definition_as_it_is() {
    let workspace = Workspace::declared();
    let store = temp_dir();
    let environment = [("KRS_STAGE_CACHE_DIR", store.path())];
    let stages = || stored_stages(store.path());
    let counters = workspace.path("counters.json");
    // The manifest by its absolute path, which the records' keys then hold: the fixture target
    // is shared with the other tests' workspaces, whose packages have these names.
    let manifest = workspace.path("Cargo.toml");
    let manifest = ["--manifest-path", manifest.to_str().unwrap()];
    let run = || {
        let run = workspace.krs_with(
            &[
                &["run"][..],
                &SELECTION,
                &manifest,
                &["--output", "end", "--counters", counters.to_str().unwrap()],
            ]
            .concat(),
            &environment,
        );
        assert!(run.status.success(), "{}", stderr(&run));
        let document: serde_json::Value =
            serde_json::from_slice(&fs::read(&counters).unwrap()).unwrap();
        (
            stdout(&run),
            document["counters"]["definition.reused"].as_u64().unwrap(),
        )
    };

    let alone = workspace.emitted("alone", &[]);
    assert!(!alone.contains(HELPER_MODULE), "{alone}");
    let (end, reused) = run();
    assert_eq!(reused, 0);
    workspace.write("end.json", &end);
    assert_eq!(stages(), 1);

    // The observer, with no `--dependency`: its view applies the helper's function.
    let compare = workspace.krs_with(
        &[
            &["compare"][..],
            &SELECTION,
            &["end.json", "end.json", "--compare", "k", "--view", "k=Seen"],
            &OBSERVER,
            &manifest,
        ]
        .concat(),
        &environment,
    );
    assert_eq!(compare.status.code(), Some(0), "{}", stderr(&compare));
    assert_eq!(
        stages(),
        2,
        "the store holds the definition's stage and the observer's, and no third"
    );

    // The definition is the one it was: its record is restored, and it emits the same files.
    assert_eq!(run(), (end, 1));
    workspace.emitted("observed", &[]);
    for file in ["definition.k", "symbols.json", "sources.json"] {
        assert_eq!(
            fs::read(workspace.path("alone").join(file)).unwrap(),
            fs::read(workspace.path("observed").join(file)).unwrap(),
            "{file} differs once the observer was composed"
        );
    }

    // Each record's key holds its own composition: the observer's the facet it adds, after the
    // definition and the definition's facets, and the definition's only its own.
    let own = ["base-semantics:base", "extra-semantics:extra"].map(str::to_owned);
    assert_eq!(
        workspace.recorded_compositions(),
        [
            (
                "observe-semantics:views".to_owned(),
                [
                    &["root-semantics:main".to_owned()][..],
                    &own,
                    &["helper-semantics:helper".to_owned()],
                ]
                .concat()
            ),
            ("root-semantics:main".to_owned(), own.to_vec()),
        ]
    );

    // Without the declaration the observer cannot collect the helper's function, and the
    // refusal names the observer's key, where the facet is stated for every command.
    workspace.declare_observer("");
    let undeclared = workspace.observe(&[]);
    assert_eq!(undeclared.status.code(), Some(2), "{}", stdout(&undeclared));
    let text = stderr(&undeclared);
    assert!(text.contains("package-not-selected"), "{text}");
    assert!(
        text.contains(
            "add `\"helper-semantics:helper\"` to `package.metadata.krs.definitions.views.dependencies` in package `observe-semantics`'s Cargo.toml"
        ),
        "{text}"
    );
    // `--dependency` keeps its meaning: it gives the definition's facets whole, and the one
    // outside the definition's closure goes to the observer.
    let flags = workspace.observe(&[
        "--dependency",
        "extra-semantics:extra",
        "--dependency",
        "base-semantics:base",
        "--dependency",
        "helper-semantics:helper",
    ]);
    assert_eq!(flags.status.code(), Some(0), "{}", stderr(&flags));
}

/// An observer adds to the composition it is compiled in and cannot change the definition it
/// observes, so its declaration is refused where composing it would: a facet of a package in the
/// definition's own closure that the definition is not composed with (whether it is composed is
/// part of what the definition is), and a cfg value the definition does not have (a cfg value
/// applies to every package of a composition). Each refusal names the observer's key and the
/// definition's key that states it instead. A facet or a cfg value the definition already has
/// adds nothing; `--dependency`, which replaces the definition's facets, decides what it has.
#[test]
fn an_observer_declaration_that_would_change_the_definition_is_refused_naming_its_key() {
    // The root depends on `extra-semantics` and is not composed with its facet.
    let alone = "dependencies = [\"base-semantics:base\"]\n";
    let with_extra = "dependencies = [\"base-semantics:base\", \"extra-semantics:extra\"]\n";
    let workspace = Workspace::new(alone);
    workspace.write_end();
    let refused = |composition: &[&str]| {
        let compare = workspace.observe(composition);
        assert_eq!(compare.status.code(), Some(2), "{}", stdout(&compare));
        stderr(&compare)
    };
    let accepted = |composition: &[&str]| {
        let compare = workspace.observe(composition);
        assert_eq!(compare.status.code(), Some(0), "{}", stderr(&compare));
    };

    workspace.declare_observer(
        "dependencies = [\"helper-semantics:helper\", \"extra-semantics:extra\"]\n",
    );
    let facet = refused(&[]);
    assert!(facet.contains("krs::plan::invalid-definition"), "{facet}");
    assert!(facet.contains(OBSERVER_KEY), "{facet}");
    assert!(
        facet.contains(
            "declares the dependency facet `extra-semantics:extra`, which the definition `root-semantics:main` it is composed with does not have: package `extra-semantics` is in package `root-semantics`'s resolved dependency closure"
        ),
        "{facet}"
    );
    assert!(
        facet.contains(
            "Add `\"extra-semantics:extra\"` to `package.metadata.krs.definitions.main.dependencies` in package `root-semantics`'s Cargo.toml"
        ),
        "{facet}"
    );
    assert!(
        facet.contains("in the observer `observe-semantics:views`"),
        "{facet}"
    );

    // Stated by the definition, the facet is the definition's, and the observer's entry adds
    // nothing; a `--dependency` that leaves it out of the definition has it refused again.
    workspace.declare(with_extra);
    accepted(&[]);
    let replaced = refused(&["--dependency", "base-semantics:base"]);
    assert!(replaced.contains(OBSERVER_KEY), "{replaced}");
    accepted(&[
        "--dependency",
        "base-semantics:base",
        "--dependency",
        "extra-semantics:extra",
    ]);

    // A cfg value the definition does not have.
    workspace.declare_observer(&format!(
        "{OBSERVER_DECLARATION}cfg = [\"tour_mode=extended\"]\n"
    ));
    let cfg = refused(&[]);
    assert!(cfg.contains("krs::plan::invalid-cfg"), "{cfg}");
    assert!(
        cfg.contains("`package.metadata.krs.definitions.views.cfg` of package `observe-semantics`"),
        "{cfg}"
    );
    assert!(
        cfg.contains(
            "Declare the value in `package.metadata.krs.definitions.main.cfg` in package `root-semantics`'s Cargo.toml"
        ),
        "{cfg}"
    );
    workspace.declare(&format!("{with_extra}cfg = [\"tour_mode=extended\"]\n"));
    accepted(&[]);

    // The observer's declaration is judged as a root facet's is: a facet its package does not
    // declare is refused naming the observer's key.
    workspace.declare_observer("dependencies = [\"helper-semantics:views\"]\n");
    let missing = refused(&[]);
    assert!(
        missing.contains("krs::plan::missing-definition"),
        "{missing}"
    );
    assert!(missing.contains(OBSERVER_KEY), "{missing}");
}

/// A declaration that cannot be the definition's composition is refused at planning, naming the
/// manifest key: a facet the package does not declare (with the facets it declares), a package
/// that is not in the graph, an entry or a key of another form, and a cfg key that is no Rust
/// identifier. The declaration is the manifest's, so it is judged whatever the command line gives.
#[test]
fn a_declaration_that_names_no_facet_is_refused_naming_the_manifest_key() {
    let workspace = Workspace::new("dependencies = [\"base-semantics:core\"]\n");
    let refused = |declaration: &str, flags: &[&str]| {
        workspace.declare(declaration);
        let check = workspace.krs(&[&["check"][..], &SELECTION, flags].concat());
        assert_eq!(check.status.code(), Some(1), "{}", stdout(&check));
        stderr(&check)
    };

    let missing = refused("dependencies = [\"base-semantics:core\"]\n", &[]);
    assert!(
        missing.contains("krs::plan::missing-definition"),
        "{missing}"
    );
    assert!(missing.contains(KEY), "{missing}");
    assert!(missing.contains("root/Cargo.toml"), "{missing}");
    assert!(
        missing.contains(
            "declares the dependency facet `base-semantics:core`: package `base-semantics` declares no KRS definition facet `core`; its definition facets are `base-semantics:base`"
        ),
        "{missing}"
    );
    let given = refused(
        "dependencies = [\"base-semantics:core\"]\n",
        &["--dependency", "base-semantics:base"],
    );
    assert!(given.contains("krs::plan::missing-definition"), "{given}");

    let package = refused("dependencies = [\"absent:main\"]\n", &[]);
    assert!(package.contains("krs::plan::missing-package"), "{package}");
    assert!(package.contains(KEY), "{package}");

    let form = refused("dependencies = [\"base-semantics\"]\n", &[]);
    assert!(form.contains("krs::plan::invalid-definition"), "{form}");
    assert!(form.contains("written `PACKAGE:FACET`"), "{form}");

    let shape = refused("dependencies = \"base-semantics:base\"\n", &[]);
    assert!(shape.contains("krs::plan::invalid-definition"), "{shape}");
    assert!(
        shape.contains("expected a list of `PACKAGE:FACET` strings"),
        "{shape}"
    );

    let cfg = refused(
        "dependencies = [\"base-semantics:base\"]\ncfg = [\"tour-mode\"]\n",
        &[],
    );
    assert!(cfg.contains("krs::plan::invalid-cfg"), "{cfg}");
    assert!(
        cfg.contains("`package.metadata.krs.definitions.main.cfg` of package `root-semantics`"),
        "{cfg}"
    );
}

/// SELECT-DIAGNOSTIC: a definition whose sources name an item of a package no selected facet is
/// of is refused with `package-not-selected`, and the diagnostic names the selection that holds
/// the package: the `--dependency PACKAGE:FACET` of the facet the package declares, and the
/// root facet's `dependencies` key, where the selection is stated once for every command.
#[test]
fn a_package_of_no_selected_facet_names_the_dependency_and_the_key_that_select_it() {
    let workspace = Workspace::new("");
    let refused = workspace.krs(&[&["check"][..], &SELECTION].concat());
    assert_eq!(refused.status.code(), Some(1), "{}", stdout(&refused));
    let text = stderr(&refused);
    assert!(text.contains("package-not-selected"), "{text}");
    assert!(
        text.contains("pass `--dependency base-semantics:base`"),
        "{text}"
    );
    assert!(
        text.contains(
            "add `\"base-semantics:base\"` to `package.metadata.krs.definitions.main.dependencies` in package `root-semantics`'s Cargo.toml"
        ),
        "{text}"
    );
    let selected = workspace.krs(
        &[
            &["check"][..],
            &SELECTION,
            &["--dependency", "base-semantics:base"],
        ]
        .concat(),
    );
    assert!(selected.status.success(), "{}", stderr(&selected));
}

/// `krs kink` on a corpus whose flow names the definition needs no selection at all: the flow
/// gives the package and the facet, and the facet's declaration the composition.
/// The K it writes is the K the same composition given by flags emits (`emit --check` finds it
/// unchanged), flags replace the declaration (one dependency facet alone is another K), and a
/// document's next step repeats what the command line gave, so it names no declared selection.
#[cfg(feature = "kink")]
#[test]
fn kink_composes_the_declaration_and_its_next_steps_omit_it() {
    let workspace = Workspace::declared();
    workspace.write(
        "root/kink/FLOW.toml",
        "[spec]\nkrs = { package = \"root-semantics\", definition = \"main\" }\n\n[budget]\ntime_ms = 600000\n\n[[program]]\nid = \"p1\"\nfile = \"cases/p1.prog\"\n",
    );
    workspace.write("root/kink/cases/p1.prog", "value-node\n");
    let kink = |arguments: &[&str]| {
        workspace.krs(&[&["kink"][..], arguments, &["--corpus", "root/kink"]].concat())
    };
    let json = |output: &Output| -> serde_json::Value {
        serde_json::from_slice(&output.stdout)
            .unwrap_or_else(|error| panic!("{error}: {}\n{}", stdout(output), stderr(output)))
    };

    let emit = kink(&["emit"]);
    assert_eq!(emit.status.code(), Some(0), "{}", stderr(&emit));
    assert_eq!(json(&emit)["definition"]["status"], "written");
    let emitted = fs::read_to_string(workspace.path("root/kink/definition.k")).unwrap();
    assert!(emitted.contains(EXTRA_MODULE), "{emitted}");
    assert!(emitted.contains(EXTENDED), "{emitted}");

    let same = kink(&[&["emit", "--check"][..], &AS_FLAGS].concat());
    assert_eq!(same.status.code(), Some(0), "{}", stdout(&same));

    let replaced = kink(&["emit", "--check", "--dependency", "base-semantics:base"]);
    assert_eq!(replaced.status.code(), Some(2), "{}", stdout(&replaced));
    assert_eq!(json(&replaced)["definition"]["status"], "stale");

    // A stale `definition.k` under `--locked` prints the command that rewrites it.
    workspace.write("root/kink/definition.k", &format!("{emitted}// edited\n"));
    let detail = |arguments: &[&str]| {
        let locked = kink(arguments);
        assert_eq!(locked.status.code(), Some(2), "{}", stdout(&locked));
        let document = json(&locked);
        assert_eq!(
            document["spec"]["reason"], "definition-stale",
            "{document:#}"
        );
        document["spec"]["detail"].as_str().unwrap().to_owned()
    };
    let declared = detail(&["coverage", "--tier", "1", "--locked"]);
    assert!(
        declared.contains(
            "krs kink emit --package root-semantics --definition main --corpus root/kink"
        ),
        "{declared}"
    );
    assert!(!declared.contains("--dependency"), "{declared}");
    assert!(!declared.contains("--cfg"), "{declared}");
    let given = detail(&[&["coverage", "--tier", "1", "--locked"][..], &AS_FLAGS].concat());
    assert!(
        given.contains("--dependency extra-semantics:extra --dependency base-semantics:base --cfg tour_mode=extended"),
        "{given}"
    );
}
