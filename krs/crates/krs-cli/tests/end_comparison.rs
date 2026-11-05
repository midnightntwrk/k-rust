//! `krs-exec` ends and their comparison on an authored definition: a run's and a search's ends
//! read by Rust field path (stopped, undefined and depth-bound ends included), end documents
//! written and read back, the compared cells (unobservable ones left out, narrowing), the first
//! difference's path and values (a value with no document shown as K text), the rules for sets
//! of ends, and what is no end: an inconclusive run and a constrained state.
//!
//! The fixture (`fixtures/ends`) copies every configuration variable into its own cell, so a run
//! of depth 0 ends with the values it was given; `toss` steps to `done(0)` or `done(1)`, and
//! `finish(v)` to `done(v)` by the rule `finish`.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::sync::OnceLock;

use k_rust::kore::ast::{KoreString, Pattern, Sort, Symbol, Variable, VariableKind};
use krs_exec::{
    Compared, Comparison, CompiledStage, ConfigInputs, ConfigValue, DIFFERENCE_FORMAT,
    DifferenceAt, End, EndCells, EndClass, EndError, Ends, Halt, RunOptions, SearchMode,
    SearchOptions, SearchReport, Semantics, Side, Solution, StopRules, Value,
};
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};
use serde_json::{Value as Json, json};

const FIXTURE: &str = include_str!("fixtures/ends/src/lib.rs");
const PACKAGE: &str = "krs-exec-ends-fixture";
const OBSERVER: &str = include_str!("fixtures/ends-observe/src/lib.rs");
const OBSERVER_PACKAGE: &str = "krs-exec-ends-observe-fixture";
const SHADOW_PACKAGE: &str = "krs-exec-ends-shadow-fixture";

/// A package that depends on the fixture and composes its definition, with a rewrite rule of its
/// own at the whole of the spelling of the fixture's rule `finish`
/// (`krs_exec_ends_fixture::finish`, the fixture's crate name and the rule's path), so that the
/// spelling selects both packages' items. The rule has a lower priority than the fixture's,
/// which applies to every `finish(v)`, so a run of `finish(3)` stops at the fixture's rule.
const SHADOW: &str = r"//! The `ends` fixture with a rule at the spelling of its rule `finish`.

pub mod krs_exec_ends_fixture {
    use k::Term;

    #[k::rule(priority = 60)]
    fn finish(k::term![ends::Cmd::Finish { value }]: Term<ends::Stmt>) -> Term<ends::Stmt> {
        ends::Cmd::Done(0)
    }
}
";

/// The Cargo manifest of a fixture package named `name`, with `dependencies` and a `[workspace]`
/// table when it stands alone.
fn manifest(name: &str, namespace: &str, dependencies: &str, alone: bool) -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n{}",
        if alone { "\n[workspace]\n" } else { "" }
    )
}

/// Write a package with `source` and `manifest` in `directory` below `root`; its manifest's path.
fn write_package(root: &Path, directory: &str, source: &str, manifest: &str) -> std::path::PathBuf {
    let project = root.join(directory);
    fs::create_dir_all(project.join("src")).unwrap();
    fs::write(project.join("src/lib.rs"), source).unwrap();
    fs::write(project.join("Cargo.toml"), manifest).unwrap();
    project.join("Cargo.toml")
}

/// The Definition IR `krs emit-k --ir` builds of `package`'s `main` definition, with `extra`
/// arguments, and its compiled stage.
fn emit(manifest: &Path, package: &str, extra: &[&str]) -> (DefinitionIr, CompiledStage) {
    let target = shared_fixture_target();
    let emitted = manifest
        .parent()
        .and_then(Path::parent)
        .unwrap()
        .join(format!("emitted-{package}"));
    let mut process = krs_command!();
    fixture_build_env(&mut process, target.path());
    let output = process
        .current_dir(manifest.parent().unwrap())
        .args(["emit-k", "--ir", "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"])
        .args(extra)
        .arg("--output")
        .arg(&emitted)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let definition: DefinitionIr =
        serde_json::from_slice(&fs::read(emitted.join("definition-ir.json")).unwrap()).unwrap();
    let stage = CompiledStage::compile(&definition, &mut Timings::disabled()).unwrap();
    (definition, stage)
}

/// The fixture's Definition IR and compiled stage, built once per test process.
fn compiled() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| {
        let temporary = temp_dir();
        let manifest = write_package(
            temporary.path(),
            "language",
            FIXTURE,
            &manifest(PACKAGE, "ORG-KRS-EXEC-ENDS", "", true),
        );
        emit(&manifest, PACKAGE, &[])
    })
}

/// The observer fixture's Definition IR and compiled stage: the package `ends-observe`, which
/// depends on the fixture, composed with the fixture's definition; built once per test process.
fn observer_compiled() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| {
        let temporary = temp_dir();
        write_package(
            temporary.path(),
            "language",
            FIXTURE,
            &manifest(PACKAGE, "ORG-KRS-EXEC-ENDS", "", false),
        );
        let manifest = write_package(
            temporary.path(),
            "observe",
            OBSERVER,
            &manifest(
                OBSERVER_PACKAGE,
                "ORG-KRS-EXEC-ENDS-OBSERVE",
                &format!("ends = {{ package = \"{PACKAGE}\", path = \"../language\" }}\n"),
                false,
            ),
        );
        fs::write(
            temporary.path().join("Cargo.toml"),
            "[workspace]\nmembers = [\"language\", \"observe\"]\nresolver = \"3\"\n",
        )
        .unwrap();
        emit(
            &manifest,
            OBSERVER_PACKAGE,
            &["--dependency", &format!("{PACKAGE}:main")],
        )
    })
}

/// The shadow package's Definition IR and compiled stage ([`SHADOW`]), composed with the
/// fixture's definition; built once per test process.
fn shadow_compiled() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| {
        let temporary = temp_dir();
        write_package(
            temporary.path(),
            "language",
            FIXTURE,
            &manifest(PACKAGE, "ORG-KRS-EXEC-ENDS", "", false),
        );
        let manifest = write_package(
            temporary.path(),
            "shadow",
            SHADOW,
            &manifest(
                SHADOW_PACKAGE,
                "ORG-KRS-EXEC-ENDS-SHADOW",
                &format!("ends = {{ package = \"{PACKAGE}\", path = \"../language\" }}\n"),
                false,
            ),
        );
        fs::write(
            temporary.path().join("Cargo.toml"),
            "[workspace]\nmembers = [\"language\", \"shadow\"]\nresolver = \"3\"\n",
        )
        .unwrap();
        emit(
            &manifest,
            SHADOW_PACKAGE,
            &["--dependency", &format!("{PACKAGE}:main")],
        )
    })
}

/// Run `test` on the fixture's semantics, on a thread with the stack every `krs-exec` operation
/// needs.
fn with_semantics(test: impl FnOnce(&mut Semantics) + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn_scoped(scope, || {
                let (definition, stage) = compiled();
                let mut semantics = Semantics::from_stage(
                    definition,
                    stage.clone(),
                    None,
                    &mut Timings::disabled(),
                )
                .unwrap();
                test(&mut semantics);
            })
            .unwrap()
            .join()
            .unwrap();
    });
}

fn ctor(semantics: &Semantics, name: &str, fields: Vec<(&str, Value)>) -> Value {
    semantics.values().ctor(name, fields).unwrap()
}

/// The configuration variables of the fixture's reference state, `pgm` the program.
fn variables(semantics: &Semantics, pgm: Value) -> Vec<(&'static str, Value)> {
    let register = |name| ctor(semantics, name, Vec::new());
    let read = |addr: i64| ctor(semantics, "CpuEvent::Read", vec![("addr", addr.into())]);
    vec![
        ("PGM", pgm),
        (
            "REGS",
            Value::map([
                (register("Register::A"), 1.into()),
                (register("Register::B"), 2.into()),
            ]),
        ),
        (
            "F",
            ctor(
                semantics,
                "FlagSet::Flags",
                vec![("zf", false.into()), ("cf", true.into())],
            ),
        ),
        ("PC", 256.into()),
        ("BUS", Value::list([read(1), read(2), read(3)])),
        (
            "MEMORY",
            Value::map([(5.into(), 7.into()), (6.into(), 8.into())]),
        ),
        ("IME", false.into()),
        ("W", 9.into()),
        ("Z", 10.into()),
    ]
}

fn state(semantics: &mut Semantics, variables: Vec<(&str, Value)>) -> krs_exec::State {
    semantics
        .configure(&ConfigInputs {
            variables: variables
                .into_iter()
                .map(|(name, value)| (name.to_owned(), ConfigValue::Value(value)))
                .collect(),
            ..ConfigInputs::default()
        })
        .unwrap()
}

/// The end of the run of depth `depth` from the reference state with program `pgm`.
fn run_end(semantics: &mut Semantics, pgm: Value, depth: Option<u64>) -> Ends {
    let variables = variables(semantics, pgm);
    let state = state(semantics, variables);
    let report = semantics
        .run(
            &state,
            RunOptions {
                depth,
                ..RunOptions::default()
            },
        )
        .unwrap();
    semantics.end_of(&report).unwrap()
}

fn done(semantics: &Semantics, value: i64) -> Value {
    ctor(semantics, "Cmd::Done", vec![("value", value.into())])
}

/// The reference end: the run of depth 0 from the reference state, holding `done(0)`.
fn reference(semantics: &mut Semantics) -> Ends {
    let pgm = done(semantics, 0);
    run_end(semantics, pgm, Some(0))
}

/// The end document of the reference end, with `edit` applied to its JSON.
fn edited(semantics: &Semantics, ends: &Ends, edit: impl FnOnce(&mut Json)) -> Ends {
    let mut document = semantics.end_document(&ends.ends[0]).unwrap();
    edit(&mut document);
    Ends::one(semantics.read_end(&document).unwrap())
}

fn side<'a>(name: &'a str, ends: &'a Ends) -> Side<'a> {
    Side { name, ends }
}

/// The difference of an expectation `expected` against `actual`, under `comparison`.
fn expectation(
    semantics: &Semantics,
    comparison: &Comparison,
    expected: &Ends,
    actual: &Ends,
) -> Compared {
    semantics
        .check_expectation(
            comparison,
            side("expected", expected),
            side("actual", actual),
        )
        .unwrap()
}

fn differs(compared: Compared) -> krs_exec::Difference {
    match compared {
        Compared::Differs(difference) => *difference,
        other => panic!("expected a difference, got {other:?}"),
    }
}

fn shown(side: &krs_exec::DifferenceSide) -> Json {
    side.value
        .as_ref()
        .map_or(Json::Null, |value| value.document.clone().unwrap())
}

#[test]
fn every_cell_is_listed_by_rust_path_with_its_type_and_observability() {
    with_semantics(|semantics| {
        let cells = semantics.cells();
        let listed = cells
            .iter()
            .map(|cell| {
                (
                    cell.path.as_str(),
                    cell.ty.as_ref().map(ToString::to_string),
                    cell.unobservable,
                )
            })
            .collect::<Vec<_>>();
        let leaf = |ty: &str| Some(ty.to_owned());
        assert_eq!(
            listed,
            [
                ("k", leaf("K"), false),
                ("regs", leaf("Map<Reg, Int>"), false),
                ("f", leaf("Flags"), false),
                ("pc", leaf("Int"), false),
                ("bus", leaf("List<Event>"), false),
                ("memory", leaf("Map<Int, Int>"), false),
                ("cpu", None, false),
                ("cpu.ime", leaf("Bool"), false),
                ("cpu.w", leaf("Int"), true),
                ("z", leaf("Int"), true),
                ("timer", leaf("Int"), false),
                ("threads", None, false),
                ("threads.thread", None, false),
                ("threads.thread.id", leaf("Int"), false),
                ("threads.thread.count", leaf("Int"), false),
                ("objects", None, false),
                ("objects.obj", None, false),
                ("objects.obj.oid", leaf("Int"), false),
                ("procs", None, false),
                ("procs.process", None, false),
                ("procs.process.pid", leaf("Int"), false),
                ("procs.process.ticks", leaf("Int"), false),
                ("mark", None, false),
                ("mark.seen", leaf("Int"), false),
            ]
        );
    });
}

#[test]
fn a_run_end_reads_every_cell_and_its_document_reads_back() {
    with_semantics(|semantics| {
        let ends = reference(semantics);
        assert_eq!(ends.incomplete, None);
        let [end] = ends.ends.as_slice() else {
            panic!("one end: {ends:?}");
        };
        assert_eq!(end.class.halt, Halt::DepthBound);
        assert_eq!(end.value("pc"), Some(&256.into()));
        assert_eq!(end.value("cpu.w"), Some(&9.into()));
        assert_eq!(end.value("timer"), None);
        let document = semantics.end_document(end).unwrap();
        // The document of a fixed end is a function of the end alone: recorded.
        assert_eq!(
            krs_exec::canonical_text(&document),
            concat!(
                r#"{"cells":{"bus":[{"Read":{"addr":1}},{"Read":{"addr":2}},{"Read":{"addr":3}}],"#,
                r#""cpu":{"ime":false,"w":9},"f":{"Flags":{"cf":true,"zf":false}},"#,
                r#""k":{"$seq":[{"Done":{"value":0}}]},"mark":[],"memory":{"5":7,"6":8},"#,
                r#""objects":{"obj":[{"oid":0}]},"pc":256,"procs":{"process":[{"pid":0,"ticks":0}]},"#,
                r#""regs":{"A":1,"B":2},"threads":{"thread":[{"count":0,"id":0}]},"timer":[],"#,
                r#""z":10},"halt":"depth-bound"}"#
            )
        );
        assert_eq!(&semantics.read_end(&document).unwrap(), end);
    });
}

#[test]
fn an_end_document_omits_unobservable_cells_and_states_every_compared_one() {
    with_semantics(|semantics| {
        let ends = reference(semantics);
        let all = Comparison::default();
        // The unobservable cells `z` and `cpu.w` may be left out, or stated with any value.
        let without = edited(semantics, &ends, |document| {
            let cells = document["cells"].as_object_mut().unwrap();
            cells.remove("z");
            cells["cpu"].as_object_mut().unwrap().remove("w");
        });
        assert_eq!(
            expectation(semantics, &all, &without, &ends),
            Compared::Equal
        );
        let other = edited(semantics, &ends, |document| {
            document["cells"]["z"] = json!(-1);
            document["cells"]["cpu"]["w"] = json!(-2);
        });
        assert_eq!(expectation(semantics, &all, &other, &ends), Compared::Equal);
        // A compared cell left out is refused, naming it and its type.
        let missing = edited(semantics, &ends, |document| {
            document["cells"].as_object_mut().unwrap().remove("pc");
        });
        let error = semantics
            .check_expectation(&all, side("expected", &missing), side("actual", &ends))
            .unwrap_err();
        assert_eq!(
            error,
            EndError::MissingCell {
                side: "expected".to_owned(),
                path: "pc".to_owned(),
                what: "Int".to_owned(),
            }
        );
        assert_eq!(
            error.to_string(),
            "the expected end does not state the compared cell `pc` (Int)"
        );
        // So is an instance's compared cell.
        let instance = edited(semantics, &ends, |document| {
            document["cells"]["threads"]["thread"][0]
                .as_object_mut()
                .unwrap()
                .remove("count");
        });
        assert!(matches!(
            semantics.check_expectation(&all, side("expected", &instance), side("actual", &ends)),
            Err(EndError::MissingCell { path, .. }) if path == "threads.thread[0].count"
        ));
        // Narrowed to `pc`, an end that states `pc` alone is enough.
        let narrowed = Comparison {
            compare: Some(vec!["pc".to_owned()]),
            ..Comparison::default()
        };
        let pc = Ends::one(
            semantics
                .read_end(&json!({"halt": "depth-bound", "cells": {"pc": 256}}))
                .unwrap(),
        );
        assert_eq!(
            expectation(semantics, &narrowed, &pc, &ends),
            Compared::Equal
        );
    });
}

#[test]
fn unknown_and_unobservable_cells_are_refused() {
    with_semantics(|semantics| {
        let ends = reference(semantics);
        let error = semantics
            .read_end(&json!({"halt": "stuck", "cells": {"cpu": {"bogus": 1}}}))
            .unwrap_err();
        assert_eq!(
            error,
            EndError::UnknownCell {
                path: "cpu.bogus".to_owned(),
                known: vec!["cpu.ime".to_owned(), "cpu.w".to_owned()],
            }
        );
        // A value is decoded at its cell's type.
        assert!(matches!(
            semantics.read_end(&json!({"halt": "stuck", "cells": {"pc": "x"}})),
            Err(EndError::Document { position, .. }) if position == "cells.pc"
        ));
        // A halt that is no end, and a rule outside a stopped end, are refused.
        assert!(semantics.read_end(&json!({"halt": "timeout"})).is_err());
        assert!(
            semantics
                .read_end(&json!({"halt": "stuck", "rule": "toss_heads"}))
                .is_err()
        );
        assert!(semantics.read_end(&json!({"halt": "stopped"})).is_err());
        let compare = |paths: &[&str]| {
            semantics.compare_ends(
                &Comparison {
                    compare: Some(paths.iter().map(|path| (*path).to_owned()).collect()),
                    ..Comparison::default()
                },
                side("left", &ends),
                side("right", &ends),
            )
        };
        assert!(matches!(
            compare(&["nope"]),
            Err(EndError::UnknownCell { path, known }) if path == "nope" && known.contains(&"threads.thread.count".to_owned())
        ));
        // Narrowing to an unobservable cell, or into one, is refused.
        for path in ["z", "cpu.w"] {
            assert_eq!(
                compare(&[path]),
                Err(EndError::Unobservable {
                    path: path.to_owned()
                })
            );
        }
        // A group names its observable leaves.
        let other = edited(semantics, &ends, |document| {
            document["cells"]["cpu"]["ime"] = json!(true);
        });
        let difference = differs(
            semantics
                .compare_ends(
                    &Comparison {
                        compare: Some(vec!["cpu".to_owned()]),
                        ..Comparison::default()
                    },
                    side("left", &ends),
                    side("right", &other),
                )
                .unwrap(),
        );
        assert_eq!(difference.compared, ["cpu.ime"]);
        assert_eq!(difference.path.as_deref(), Some("cpu.ime"));
        assert!(difference.not_compared.contains(&"cpu.w".to_owned()));
        assert!(difference.not_compared.contains(&"pc".to_owned()));
    });
}

#[test]
fn a_difference_names_the_rust_path_and_both_canonical_documents() {
    with_semantics(|semantics| {
        let ends = reference(semantics);
        let all = Comparison::default();
        let at = |edit: &dyn Fn(&mut Json)| {
            let expected = edited(semantics, &ends, edit);
            differs(expectation(semantics, &all, &expected, &ends))
        };
        let difference = at(&|document| document["cells"]["f"]["Flags"]["zf"] = json!(true));
        assert_eq!(difference.at, DifferenceAt::Cell);
        assert_eq!(difference.cell.as_deref(), Some("f"));
        assert_eq!(difference.path.as_deref(), Some("f.zf"));
        assert_eq!(difference.segments, [".zf"]);
        assert_eq!(shown(&difference.left), json!(true));
        assert_eq!(shown(&difference.right), json!(false));
        assert!(difference.also_differ.is_empty());

        let difference = at(&|document| {
            document["cells"]["bus"][2] = json!({"Write": {"addr": 3, "value": 4}});
        });
        assert_eq!(difference.path.as_deref(), Some("bus[2]"));
        assert_eq!(
            shown(&difference.left),
            json!({"Write": {"addr": 3, "value": 4}})
        );
        assert_eq!(shown(&difference.right), json!({"Read": {"addr": 3}}));

        let difference = at(&|document| document["cells"]["memory"]["5"] = json!(70));
        assert_eq!(difference.path.as_deref(), Some("memory[5]"));
        assert_eq!(shown(&difference.left), json!(70));
        assert_eq!(shown(&difference.right), json!(7));

        // A key one side lacks shows null there.
        let difference = at(&|document| document["cells"]["regs"]["C"] = json!(3));
        assert_eq!(difference.path.as_deref(), Some(r#"regs["C"]"#));
        assert_eq!(shown(&difference.left), json!(3));
        assert_eq!(difference.right.value, None);

        let difference = at(&|document| document["cells"]["regs"]["B"] = json!(20));
        assert_eq!(difference.path.as_deref(), Some(r#"regs["B"]"#));

        // The first compared cell in declaration order, and every other that differs.
        let difference = at(&|document| {
            document["cells"]["memory"]["6"] = json!(80);
            document["cells"]["pc"] = json!(257);
            document["cells"]["z"] = json!(0);
        });
        assert_eq!(difference.path.as_deref(), Some("pc"));
        assert_eq!(difference.also_differ, ["memory"]);

        // An optional cell present on one side only; an instance of a `List` collection.
        let difference = at(&|document| document["cells"]["timer"] = json!([3]));
        assert_eq!(difference.path.as_deref(), Some("timer"));
        assert_eq!(shown(&difference.left), json!([3]));
        assert_eq!(shown(&difference.right), json!([]));
        let difference = at(&|document| {
            document["cells"]["threads"]["thread"][0]["count"] = json!(1);
        });
        assert_eq!(difference.path.as_deref(), Some("threads.thread[0].count"));
        let difference = at(&|document| {
            document["cells"]["threads"]["thread"]
                .as_array_mut()
                .unwrap()
                .push(json!({"id": 1, "count": 0}));
        });
        assert_eq!(difference.path.as_deref(), Some("threads.thread[1]"));
        assert_eq!(shown(&difference.left), json!({"count": 0, "id": 1}));
        assert_eq!(difference.right.value, None);

        // A `Set` collection's instances are a set: their order in a document is no difference,
        // and the difference is the first instance, by canonical text, one side holds alone.
        let two = |first: i64, second: i64| {
            edited(semantics, &ends, |document| {
                document["cells"]["objects"]["obj"] = json!([{"oid": first}, {"oid": second}]);
            })
        };
        assert_eq!(two(2, 0), two(0, 2));
        let difference = differs(expectation(semantics, &all, &two(2, 0), &ends));
        assert_eq!(difference.cell.as_deref(), Some("objects.obj"));
        assert_eq!(
            difference.path.as_deref(),
            Some(r#"objects.obj{{"oid":2}}"#)
        );
        assert_eq!(shown(&difference.left), json!({"oid": 2}));
        assert_eq!(difference.right.value, None);

        // The class comes first.
        let difference = at(&|document| {
            document["halt"] = json!("stuck");
            document["cells"]["pc"] = json!(1);
        });
        assert_eq!(difference.at, DifferenceAt::Class);
        assert_eq!(difference.path, None);
        assert_eq!(difference.left.class.halt, Halt::Stuck);
        assert_eq!(difference.right.class.halt, Halt::DepthBound);
        assert_eq!(difference.also_differ, ["pc"]);
    });
}

#[test]
fn the_difference_document_has_the_format_krs_difference_1() {
    with_semantics(|semantics| {
        let ends = reference(semantics);
        let expected = edited(semantics, &ends, |document| {
            document["cells"]["f"]["Flags"]["zf"] = json!(true);
        });
        let difference = differs(expectation(
            semantics,
            &Comparison {
                compare: Some(vec!["f".to_owned(), "pc".to_owned()]),
                ..Comparison::default()
            },
            &expected,
            &ends,
        ));
        assert_eq!(difference.format, DIFFERENCE_FORMAT);
        let not_compared = [
            "k",
            "regs",
            "bus",
            "memory",
            "cpu.ime",
            "cpu.w",
            "z",
            "timer",
            "threads.thread.id",
            "threads.thread.count",
            "objects.obj.oid",
            "procs.process.pid",
            "procs.process.ticks",
            "mark.seen",
        ];
        assert_eq!(
            serde_json::to_value(&difference).unwrap(),
            json!({
                "format": "krs-difference/2",
                "at": "cell",
                "cell": "f",
                "path": "f.zf",
                "segments": [".zf"],
                "outside": "actual",
                "also_differ": [],
                "compared": ["f", "pc"],
                "not_compared": not_compared,
                "views": {},
                "left": {
                    "name": "expected",
                    "ends": 1,
                    "complete": true,
                    "class": {"halt": "depth-bound"},
                    "value": {"rendering": "document", "document": true, "truncated": false, "offset": 0},
                },
                "right": {
                    "name": "actual",
                    "ends": 1,
                    "complete": true,
                    "class": {"halt": "depth-bound"},
                    "value": {"rendering": "document", "document": false, "truncated": false, "offset": 0},
                },
            })
        );
    });
}

#[test]
fn sets_of_ends_meet_an_expectation_at_every_end_and_differ_by_the_pair_rule() {
    with_semantics(|semantics| {
        let toss = ctor(semantics, "Cmd::Toss", vec![("value", 0.into())]);
        let variables = variables(semantics, toss);
        let state = state(semantics, variables);
        let options = SearchOptions {
            mode: SearchMode::Final,
            ..SearchOptions::default()
        };
        let report = semantics.search(&state, options).unwrap();
        let search = semantics.ends_of(&report, &options).unwrap();
        assert_eq!(search.incomplete, None);
        let mut ks = search
            .ends
            .iter()
            .map(|end| (end.class.halt, end.value("k").cloned()))
            .collect::<Vec<_>>();
        ks.sort_by_key(|(_, k)| format!("{k:?}"));
        assert_eq!(
            ks,
            [
                (Halt::Stuck, Some(Value::seq([done(semantics, 0)]))),
                (Halt::Stuck, Some(Value::seq([done(semantics, 1)]))),
            ]
        );
        let all = Comparison::default();
        let stuck = |edit: &dyn Fn(&mut Json)| {
            let ends = Ends::one(search.ends[0].clone());
            edited(semantics, &ends, |document| {
                document["cells"]["k"] = json!({"$seq": [{"Done": {"value": 1}}]});
                edit(document);
            })
        };
        // An expectation is met only when every end agrees with it.
        let heads = stuck(&|_| {});
        let difference = differs(expectation(semantics, &all, &heads, &search));
        assert_eq!(difference.path.as_deref(), Some("k[0].value"));
        assert_eq!(difference.outside, "actual");
        assert_eq!(shown(&difference.left), json!(1));
        assert_eq!(shown(&difference.right), json!(0));
        assert_eq!(difference.right.ends, 2);
        let pc = Comparison {
            compare: Some(vec!["pc".to_owned()]),
            ..Comparison::default()
        };
        assert_eq!(
            expectation(semantics, &pc, &heads, &search),
            Compared::Equal
        );
        // The disagreeing end reported is a function of the set of ends, not of their order.
        let nowhere = stuck(&|document| document["cells"]["pc"] = json!(99));
        let reversed = Ends {
            ends: search.ends.iter().rev().cloned().collect(),
            incomplete: None,
        };
        assert_eq!(
            expectation(semantics, &all, &nowhere, &search),
            expectation(semantics, &all, &nowhere, &reversed)
        );
        // An expectation every end meets, of an incomplete set, is inconclusive.
        let partial = Ends {
            ends: search.ends.clone(),
            incomplete: Some("cut".to_owned()),
        };
        assert!(matches!(
            expectation(semantics, &pc, &heads, &partial),
            Compared::Inconclusive(reason) if reason.contains("cut")
        ));

        // Sets: equal when the sets of projected ends are.
        let compare = |comparison: &Comparison, left: &Ends, right: &Ends| {
            semantics
                .compare_ends(comparison, side("left", left), side("right", right))
                .unwrap()
        };
        assert_eq!(compare(&all, &search, &search), Compared::Equal);
        assert_eq!(compare(&pc, &search, &heads), Compared::Equal);
        // The end of the left set outside the right one, when the right one is complete.
        let difference = differs(compare(&all, &search, &heads));
        assert_eq!(difference.outside, "left");
        assert_eq!(difference.path.as_deref(), Some("k[0].value"));
        assert_eq!(shown(&difference.left), json!(0));
        let unknown = Ends {
            ends: heads.ends.clone(),
            incomplete: Some("cut".to_owned()),
        };
        assert!(matches!(
            compare(&all, &search, &unknown),
            Compared::Inconclusive(_)
        ));
        // An end of the right set outside the left one, paired with its nearest end there.
        let far = stuck(&|document| document["cells"]["pc"] = json!(99));
        let difference = differs(compare(&all, &search, &far));
        assert_eq!(difference.outside, "right");
        assert_eq!(difference.path.as_deref(), Some("pc"));
        assert!(difference.also_differ.is_empty(), "{difference:?}");
        assert_eq!(shown(&difference.left), json!(256));
        assert_eq!(shown(&difference.right), json!(99));
        assert_eq!(difference.left.ends, 2);
    });
}

#[test]
fn an_inconclusive_run_has_no_end_to_compare() {
    with_semantics(|semantics| {
        let ends = reference(semantics);
        let pgm = done(semantics, 0);
        let variables = variables(semantics, pgm);
        let state = state(semantics, variables);
        let mut report = semantics
            .run(
                &state,
                RunOptions {
                    depth: Some(0),
                    ..RunOptions::default()
                },
            )
            .unwrap();
        report.halt = Halt::Timeout;
        let none = semantics.end_of(&report).unwrap();
        assert!(none.ends.is_empty());
        assert!(none.incomplete.as_deref().unwrap().contains("timeout"));
        let all = Comparison::default();
        for compared in [
            expectation(semantics, &all, &ends, &none),
            semantics
                .compare_ends(&all, side("left", &ends), side("right", &none))
                .unwrap(),
        ] {
            assert!(
                matches!(&compared, Compared::Inconclusive(reason) if reason.contains("timeout")),
                "{compared:?}"
            );
        }
        // Every inconclusive halt is no end, so the expectation finds none, and says so rather
        // than that every end agrees.
        for halt in [
            Halt::Indeterminate,
            Halt::Timeout,
            Halt::Interrupted,
            Halt::UnsupportedHook,
            Halt::SimplificationError,
        ] {
            report.halt = halt;
            let none = semantics.end_of(&report).unwrap();
            assert_eq!(
                expectation(semantics, &all, &ends, &none),
                Compared::Inconclusive(format!(
                    "the actual side has no end: the run halted `{}`, which is no end of the definition",
                    halt.as_str()
                ))
            );
        }
        // A stopped end that does not name its rule cannot be compared on its class.
        let mut unnamed: End = ends.ends[0].clone();
        unnamed.class.halt = Halt::Stopped;
        assert!(matches!(
            expectation(semantics, &all, &ends, &Ends::one(unnamed)),
            Compared::Inconclusive(_)
        ));
    });
}

fn sort(name: &str) -> Sort {
    Sort::Application {
        name: name.to_owned(),
        arguments: Vec::new(),
    }
}

fn variable(name: &str, sort_name: &str) -> Pattern {
    Pattern::Variable(Variable {
        kind: VariableKind::Element,
        name: format!("Var{name}"),
        sort: sort(sort_name),
    })
}

/// `OnlyZero(1)` unevaluated, as a state may hold an application: a ground part with no document.
fn only_zero_of_one(semantics: &Semantics) -> Pattern {
    let name = semantics
        .definition_kore()
        .split("symbol ")
        .skip(1)
        .filter_map(|declaration| declaration.split('{').next())
        .find(|name| name.to_ascii_lowercase().ends_with("onlyzero"))
        .expect("the symbol of `OnlyZero`");
    Pattern::Application {
        symbol: Symbol {
            name: name.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments: vec![Pattern::DomainValue {
            sort: sort("SortInt"),
            value: KoreString::from("1"),
        }],
    }
}

/// Replace the content of the first cell application `symbol` in `pattern` by `content`.
fn replace_cell(pattern: &mut Pattern, symbol: &str, content: &Pattern) -> bool {
    match pattern {
        Pattern::Application {
            symbol: head,
            arguments,
        }
        | Pattern::AssociativeApplication {
            symbol: head,
            arguments,
            ..
        } => {
            if head.name == symbol {
                arguments[0] = content.clone();
                return true;
            }
            arguments
                .iter_mut()
                .any(|argument| replace_cell(argument, symbol, content))
        }
        _ => false,
    }
}

/// A run's report with its state replaced by `state`, for a state no run of the fixture reaches.
fn reported(
    semantics: &mut Semantics,
    replace: impl FnOnce(Pattern) -> Pattern,
) -> krs_exec::RunReport {
    let pgm = done(semantics, 0);
    let variables = variables(semantics, pgm);
    let start = state(semantics, variables);
    let mut report = semantics
        .run(
            &start,
            RunOptions {
                depth: Some(0),
                ..RunOptions::default()
            },
        )
        .unwrap();
    report.state = semantics
        .term(replace(report.state.kore().clone()))
        .unwrap();
    report
}

#[test]
fn a_stopped_end_names_a_rewrite_rule_of_the_definition() {
    with_semantics(|semantics| {
        let finish = ctor(semantics, "Cmd::Finish", vec![("value", 3.into())]);
        let variables = variables(semantics, finish);
        let state = state(semantics, variables);
        let report = semantics
            .run(
                &state,
                RunOptions {
                    stop: StopRules {
                        // The default label of the rule `finish`: the namespace, then the item.
                        after: vec!["org_krs_exec_ends--finish".to_owned()],
                        ..StopRules::default()
                    }
                    .into(),
                    ..RunOptions::default()
                },
            )
            .unwrap();
        let stopped = semantics.end_of(&report).unwrap();
        let [end] = stopped.ends.as_slice() else {
            panic!("one end: {stopped:?}");
        };
        assert_eq!(
            end.class,
            EndClass {
                halt: Halt::Stopped,
                rule: Some("crate::finish".to_owned()),
            }
        );
        assert_eq!(end.value("k"), Some(&Value::seq([done(semantics, 3)])));
        // The document names the rule as the stop flags do.
        let document = semantics.end_document(end).unwrap();
        assert_eq!(document["rule"], json!("crate::finish"));
        assert_eq!(&semantics.read_end(&document).unwrap(), end);
        let all = Comparison::default();
        let same = Ends::one(semantics.read_end(&document).unwrap());
        assert_eq!(
            expectation(semantics, &all, &same, &stopped),
            Compared::Equal
        );
        // Any name a stop accepts names the class: the item's K label reads as the item.
        let labelled = edited(semantics, &stopped, |document| {
            document["rule"] = json!("org_krs_exec_ends--finish");
        });
        assert_eq!(labelled.ends[0].class, end.class);
        assert_eq!(
            expectation(semantics, &all, &labelled, &stopped),
            Compared::Equal
        );
        // Another rewrite rule of the definition is another class.
        let other = edited(semantics, &stopped, |document| {
            document["rule"] = json!("crate::toss_heads");
        });
        let difference = differs(expectation(semantics, &all, &other, &stopped));
        assert_eq!(difference.at, DifferenceAt::Class);
        assert_eq!(
            difference.left.class.rule.as_deref(),
            Some("crate::toss_heads")
        );
        assert_eq!(
            difference.right.class.rule.as_deref(),
            Some("crate::finish")
        );
        // A name no stop accepts is refused, not compared: a rule the definition does not have
        // stops none of its runs; a bare path is a K label, which `finish` is not; and the main
        // package's items are named with `crate::`, as Rust names them inside the crate.
        let refused = |rule: &str| {
            let mut document = document.clone();
            document["rule"] = json!(rule);
            match semantics.read_end(&document) {
                Err(EndError::Document { position, message }) => {
                    assert_eq!(position, "rule");
                    message
                }
                other => panic!("`{rule}` is refused: {other:?}"),
            }
        };
        assert_eq!(refused("finsh"), "no rewrite rule has label `finsh`");
        assert_eq!(
            refused("finish"),
            "no rewrite rule has label `finish`; did you mean `crate::finish`?"
        );
        let message = refused("krs_exec_ends_fixture::finish");
        assert!(
            message.starts_with(
                "no rewrite rule is written by KRS item `krs_exec_ends_fixture::finish`"
            ),
            "{message}"
        );
    });
}

/// A stopped end's class is computed from the stop rule's identity: where the item's spelling
/// also selects another package's item, the class names it by a label, which reads back as the
/// item, and the other item is another class.
#[test]
fn a_stopped_end_names_a_dependency_item_its_spelling_does_not_name_alone() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn_scoped(scope, || {
                let (definition, compiled) = shadow_compiled();
                let semantics = &mut Semantics::from_stage(
                    definition,
                    compiled.clone(),
                    None,
                    &mut Timings::disabled(),
                )
                .unwrap();
                let finish = ctor(semantics, "Cmd::Finish", vec![("value", 3.into())]);
                let variables = variables(semantics, finish);
                let state = state(semantics, variables);
                let report = semantics
                    .run(
                        &state,
                        RunOptions {
                            stop: StopRules {
                                after: vec!["org_krs_exec_ends--finish".to_owned()],
                                ..StopRules::default()
                            }
                            .into(),
                            ..RunOptions::default()
                        },
                    )
                    .unwrap();
                // The report spells the item with its crate, which names the shadow's item too.
                let rule = report.stop.as_ref().and_then(|stop| stop.rule.as_ref());
                assert_eq!(
                    rule.and_then(|rule| rule.item.as_deref()),
                    Some("krs_exec_ends_fixture::finish")
                );
                let stopped = semantics.end_of(&report).unwrap();
                let [end] = stopped.ends.as_slice() else {
                    panic!("one end: {stopped:?}");
                };
                assert_eq!(
                    end.class,
                    EndClass {
                        halt: Halt::Stopped,
                        rule: Some("org_krs_exec_ends--finish".to_owned()),
                    }
                );
                let document = semantics.end_document(end).unwrap();
                assert_eq!(document["rule"], json!("org_krs_exec_ends--finish"));
                assert_eq!(&semantics.read_end(&document).unwrap(), end);
                // The spelling selects both items, so it names no class.
                let mut ambiguous = document.clone();
                ambiguous["rule"] = json!("krs_exec_ends_fixture::finish");
                assert!(
                    matches!(
                        semantics.read_end(&ambiguous),
                        Err(EndError::Document { ref position, .. }) if position == "rule"
                    ),
                    "{:?}",
                    semantics.read_end(&ambiguous)
                );
                // The shadow's item at that path is another class, named with `crate::`.
                let shadowed = edited(semantics, &stopped, |document| {
                    document["rule"] = json!("crate::krs_exec_ends_fixture::finish");
                });
                assert_eq!(
                    shadowed.ends[0].class.rule.as_deref(),
                    Some("crate::krs_exec_ends_fixture::finish")
                );
                let difference = differs(expectation(
                    semantics,
                    &Comparison::default(),
                    &shadowed,
                    &stopped,
                ));
                assert_eq!(difference.at, DifferenceAt::Class);
            })
            .unwrap()
            .join()
            .unwrap();
    });
}

#[test]
fn an_undefined_end_has_no_cells() {
    with_semantics(|semantics| {
        let reference = reference(semantics);
        let pgm = done(semantics, 0);
        let mut variables = variables(semantics, pgm);
        variables[3].1 = semantics
            .values()
            .call("OnlyZero", [("n", 1.into())])
            .unwrap();
        let state = state(semantics, variables);
        let report = semantics.run(&state, RunOptions::default()).unwrap();
        assert_eq!(report.halt, Halt::Undefined);
        let undefined = semantics.end_of(&report).unwrap();
        let end = End {
            class: EndClass {
                halt: Halt::Undefined,
                rule: None,
            },
            cells: EndCells::default(),
        };
        assert_eq!(undefined, Ends::one(end.clone()));
        let document = semantics.end_document(&end).unwrap();
        assert_eq!(document, json!({"halt": "undefined"}));
        assert_eq!(semantics.read_end(&document).unwrap(), end);
        assert!(
            semantics
                .read_end(&json!({"halt": "undefined", "cells": {"pc": 1}}))
                .is_err()
        );
        let all = Comparison::default();
        assert_eq!(
            expectation(semantics, &all, &undefined, &undefined),
            Compared::Equal
        );
        let difference = differs(
            semantics
                .compare_ends(&all, side("left", &reference), side("right", &undefined))
                .unwrap(),
        );
        assert_eq!(difference.at, DifferenceAt::Class);
        assert!(difference.also_differ.is_empty());
        assert_eq!(difference.right.class.halt, Halt::Undefined);
    });
}

#[test]
fn a_search_classifies_its_ends_by_its_bound_and_reads_bottom_and_constraints() {
    with_semantics(|semantics| {
        let toss = ctor(semantics, "Cmd::Toss", vec![("value", 0.into())]);
        let variables = variables(semantics, toss.clone());
        let state = state(semantics, variables);
        let bounded = |semantics: &mut Semantics, depth| {
            let options = SearchOptions {
                mode: SearchMode::Final,
                depth: Some(depth),
                ..SearchOptions::default()
            };
            let report = semantics.search(&state, options).unwrap();
            semantics.ends_of(&report, &options).unwrap()
        };
        // At the bound, a solution is `depth-bound`, as a run cut by its bound is.
        let at_zero = bounded(semantics, 0);
        let [end] = at_zero.ends.as_slice() else {
            panic!("one end: {at_zero:?}");
        };
        assert_eq!(end.class.halt, Halt::DepthBound);
        assert_eq!(end.value("k"), Some(&Value::seq([toss])));
        let at_one = bounded(semantics, 1);
        assert_eq!(at_one.ends.len(), 2, "{at_one:?}");
        assert!(
            at_one
                .ends
                .iter()
                .all(|end| end.class.halt == Halt::DepthBound)
        );

        let final_state = SearchOptions {
            mode: SearchMode::Final,
            ..SearchOptions::default()
        };
        let top = sort("SortGeneratedTopCell");
        let solutions = |semantics: &Semantics, state: Pattern| SearchReport {
            complete: true,
            solutions: vec![Solution {
                state: semantics.term(state).unwrap(),
                depth: 1,
                trace: Vec::new(),
            }],
            log: Vec::new(),
            implementation_chosen_values: Vec::new(),
        };
        // A `\bottom` solution is an undefined end.
        let bottom = solutions(semantics, Pattern::Bottom { sort: top.clone() });
        assert_eq!(
            semantics.ends_of(&bottom, &final_state).unwrap(),
            Ends::one(End {
                class: EndClass {
                    halt: Halt::Undefined,
                    rule: None,
                },
                cells: EndCells::default(),
            })
        );
        // A constrained state is no end, of a run or of a search.
        let constrain = |configuration: Pattern| Pattern::And {
            sort: top.clone(),
            arguments: vec![
                configuration,
                Pattern::Equals {
                    operand_sort: Box::new(sort("SortInt")),
                    result_sort: top.clone(),
                    left: Box::new(variable("X", "SortInt")),
                    right: Box::new(variable("Y", "SortInt")),
                },
            ],
        };
        let report = reported(semantics, constrain);
        let none = semantics.end_of(&report).unwrap();
        assert!(none.ends.is_empty());
        assert!(
            none.incomplete.as_deref().unwrap().contains("constraint"),
            "{none:?}"
        );
        let search = solutions(semantics, report.state.kore().clone());
        let none = semantics.ends_of(&search, &final_state).unwrap();
        assert!(none.ends.is_empty());
        assert!(
            none.incomplete.as_deref().unwrap().contains("constraint"),
            "{none:?}"
        );
    });
}

#[test]
fn map_collections_and_optional_groups_are_read_and_compared() {
    with_semantics(|semantics| {
        let ends = reference(semantics);
        let all = Comparison::default();
        // The run's `Map` collection holds its instance beside the instance's key cell: it reads
        // as the one instance.
        let document = semantics.end_document(&ends.ends[0]).unwrap();
        assert_eq!(
            document["cells"]["procs"],
            json!({"process": [{"pid": 0, "ticks": 0}]})
        );
        assert_eq!(document["cells"]["mark"], json!([]));
        // Its instances are a set.
        let two = |first: i64, second: i64| {
            edited(semantics, &ends, |document| {
                document["cells"]["procs"]["process"] =
                    json!([{"pid": first, "ticks": 0}, {"pid": second, "ticks": 0}]);
            })
        };
        assert_eq!(two(1, 0), two(0, 1));
        let difference = differs(expectation(semantics, &all, &two(1, 0), &ends));
        assert_eq!(
            difference.path.as_deref(),
            Some(r#"procs.process{{"pid":1,"ticks":0}}"#)
        );
        assert_eq!(shown(&difference.left), json!({"pid": 1, "ticks": 0}));
        assert_eq!(difference.right.value, None);

        // An optional group present on one side only, and on both.
        let marked = |seen: i64| {
            edited(semantics, &ends, |document| {
                document["cells"]["mark"] = json!([{"seen": seen}]);
            })
        };
        let difference = differs(expectation(semantics, &all, &marked(1), &ends));
        assert_eq!(difference.path.as_deref(), Some("mark"));
        assert_eq!(shown(&difference.left), json!([{"seen": 1}]));
        assert_eq!(shown(&difference.right), json!([]));
        let difference = differs(
            semantics
                .compare_ends(&all, side("left", &marked(1)), side("right", &marked(2)))
                .unwrap(),
        );
        assert_eq!(difference.path.as_deref(), Some("mark.seen"));
        assert_eq!(
            (shown(&difference.left), shown(&difference.right)),
            (json!(1), json!(2))
        );

        // A compared cell missing inside a present optional group is refused.
        let missing = edited(semantics, &ends, |document| {
            document["cells"]["mark"] = json!([{}]);
        });
        assert_eq!(
            semantics.check_expectation(&all, side("expected", &missing), side("actual", &ends)),
            Err(EndError::MissingCell {
                side: "expected".to_owned(),
                path: "mark.seen".to_owned(),
                what: "Int".to_owned(),
            })
        );
        // An instance of a set collection is named by its content, which a set's instance is
        // known by, not by where the document wrote it.
        let incomplete = edited(semantics, &ends, |document| {
            document["cells"]["objects"]["obj"] = json!([{"oid": 5}, {}]);
        });
        assert!(matches!(
            semantics.check_expectation(&all, side("expected", &incomplete), side("actual", &ends)),
            Err(EndError::MissingCell { path, .. }) if path == "objects.obj{{}}.oid"
        ));
    });
}

#[test]
fn a_value_with_no_document_is_shown_as_k_text_naming_the_part_inside_it() {
    with_semantics(|semantics| {
        let reference = reference(semantics);
        let all = Comparison::default();
        // An instance whose `count` holds an unevaluated application, which has no document.
        let application = only_zero_of_one(semantics);
        let report = reported(semantics, |mut configuration| {
            assert!(replace_cell(
                &mut configuration,
                "Lbl'-LT-'count'-GT-'",
                &application
            ));
            configuration
        });
        let opaque = semantics.end_of(&report).unwrap();
        let error = semantics.end_document(&opaque.ends[0]).unwrap_err();
        assert!(
            matches!(&error, EndError::Document { position, .. } if position == "cells.threads.thread[0].count"),
            "{error:?}"
        );
        // The instance the actual side holds alone is shown whole as K text; `opaque` names the
        // part with no document inside it.
        let none = edited(semantics, &reference, |document| {
            document["cells"]["threads"]["thread"] = json!([]);
        });
        let difference = differs(expectation(semantics, &all, &none, &opaque));
        assert_eq!(difference.path.as_deref(), Some("threads.thread[0]"));
        assert_eq!(difference.left.value, None);
        let rendered = difference.right.value.clone().unwrap();
        assert_eq!(
            (
                rendered.rendering,
                rendered.document.as_ref(),
                rendered.opaque.as_deref()
            ),
            ("k", None, Some(".count")),
            "{rendered:?}"
        );
        let text = rendered.text.unwrap();
        assert!(
            text.contains("<count>") && text.contains("nlyZero"),
            "{text}"
        );
        // Within one instance, the value itself is the part.
        let difference = differs(expectation(semantics, &all, &reference, &opaque));
        assert_eq!(difference.path.as_deref(), Some("threads.thread[0].count"));
        assert_eq!(shown(&difference.left), json!(0));
        let rendered = difference.right.value.unwrap();
        assert_eq!(
            (
                rendered.rendering,
                rendered.document.as_ref(),
                rendered.opaque.as_deref()
            ),
            ("k", None, Some("")),
            "{rendered:?}"
        );
        assert!(rendered.text.unwrap().contains("nlyZero"));
        // The difference document carries the rendering.
        let value =
            serde_json::to_value(differs(expectation(semantics, &all, &none, &opaque))).unwrap();
        assert_eq!(value["right"]["value"]["rendering"], json!("k"));
        assert_eq!(value["right"]["value"]["opaque"], json!(".count"));
        assert!(value["right"]["value"].get("document").is_none());
    });
}

/// Run `test` on the fixture's semantics and its observer's, on one thread with the stack every
/// `krs-exec` operation needs.
fn with_observer(test: impl FnOnce(&mut Semantics, &mut Semantics) + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn_scoped(scope, || {
                let load = |(definition, stage): &(DefinitionIr, CompiledStage)| {
                    Semantics::from_stage(definition, stage.clone(), None, &mut Timings::disabled())
                        .unwrap()
                };
                let mut subject = load(compiled());
                let mut observer = load(observer_compiled());
                test(&mut subject, &mut observer);
            })
            .unwrap()
            .join()
            .unwrap();
    });
}

/// The comparison of every observable cell under the views `named` (function by cell), resolved
/// and evaluated in the fixture's own definition at the ends of `sides`.
fn viewed(
    semantics: &mut Semantics,
    named: &[(&str, &str)],
    sides: &[(&str, &Ends)],
) -> Result<Comparison, EndError> {
    let named: BTreeMap<String, String> = named
        .iter()
        .map(|(cell, function)| ((*cell).to_owned(), (*function).to_owned()))
        .collect();
    let mut views = semantics.cell_views(semantics, &named)?;
    let sides = sides
        .iter()
        .map(|(name, ends)| side(name, ends))
        .collect::<Vec<_>>();
    views.evaluate(semantics, &sides)?;
    Ok(Comparison {
        views,
        ..Comparison::default()
    })
}

/// The reference end with its `bus` replaced by `bus` (event documents).
fn with_bus(semantics: &Semantics, ends: &Ends, bus: Json) -> Ends {
    edited(semantics, ends, |document| document["cells"]["bus"] = bus)
}

/// A view's refusal message, the error's display.
fn refusal(result: Result<Comparison, EndError>) -> String {
    match result {
        Err(error @ EndError::View { .. }) => error.to_string(),
        other => panic!("expected a view's refusal, got {other:?}"),
    }
}

#[test]
fn evaluate_computes_a_function_of_the_definition_at_values() {
    with_semantics(|semantics| {
        let read = |addr: i64| ctor(semantics, "CpuEvent::Read", vec![("addr", addr.into())]);
        let log = Value::list([read(1), read(2)]);
        assert_eq!(
            semantics
                .evaluate("EventCount", vec![("log", log)])
                .unwrap(),
            2.into()
        );
        assert_eq!(
            semantics
                .evaluate("Sum", vec![("m", 3.into()), ("n", 4.into())])
                .unwrap(),
            7.into()
        );
        // Outside a partial function's domain, and at a value the definition leaves to the
        // implementation, there is no value.
        let none = semantics
            .evaluate("OnlyZero", vec![("n", 5.into())])
            .unwrap_err();
        assert!(
            matches!(none, krs_exec::EvaluationError::NoValue(_)),
            "{none}"
        );
        let a = ctor(semantics, "Register::A", Vec::new());
        let b = ctor(semantics, "Register::B", Vec::new());
        let chosen = semantics
            .evaluate(
                "RegisterOrder",
                vec![("regs", Value::map([(a, 1.into()), (b, 2.into())]))],
            )
            .unwrap_err();
        assert!(
            matches!(chosen, krs_exec::EvaluationError::NoValue(_)),
            "{chosen}"
        );
        // A constructor is no function.
        let wrong = semantics
            .evaluate("CpuEvent::Read", vec![("addr", 1.into())])
            .unwrap_err();
        assert!(
            matches!(wrong, krs_exec::EvaluationError::Application(_)),
            "{wrong}"
        );
    });
}

#[test]
fn a_viewed_cell_is_compared_on_its_view_and_shown_as_the_viewed_value() {
    with_semantics(|semantics| {
        let ends = reference(semantics);
        let write = |addr: i64| json!({"Write": {"addr": addr, "value": 0}});
        // The same number of events, other events: equal under the view, not without it.
        let same_count = with_bus(semantics, &ends, json!([write(1), write(2), write(3)]));
        let comparison = viewed(
            semantics,
            &[("bus", "EventCount")],
            &[("expected", &same_count), ("actual", &ends)],
        )
        .unwrap();
        assert_eq!(
            expectation(semantics, &comparison, &same_count, &ends),
            Compared::Equal
        );
        let raw = differs(expectation(
            semantics,
            &Comparison::default(),
            &same_count,
            &ends,
        ));
        assert_eq!(raw.path.as_deref(), Some("bus[0]"));
        // Fewer events: the difference is at the viewed cell, between the viewed values.
        let fewer = with_bus(semantics, &ends, json!([write(1), write(2)]));
        let comparison = viewed(
            semantics,
            &[("bus", "EventCount")],
            &[("left", &fewer), ("right", &ends)],
        )
        .unwrap();
        let difference = differs(
            semantics
                .compare_ends(&comparison, side("left", &fewer), side("right", &ends))
                .unwrap(),
        );
        assert_eq!(difference.at, DifferenceAt::Cell);
        assert_eq!(difference.path.as_deref(), Some("bus"));
        assert!(difference.segments.is_empty());
        assert_eq!(shown(&difference.left), json!(2));
        assert_eq!(shown(&difference.right), json!(3));
        assert_eq!(
            serde_json::to_value(&difference).unwrap()["views"],
            json!({"bus": "EventCount"})
        );
    });
}

#[test]
fn a_view_without_a_value_at_an_end_refuses_the_comparison() {
    with_semantics(|semantics| {
        let ends = reference(semantics);
        // `pc` is 256, outside `OnlyZero`'s domain.
        let partial = refusal(viewed(
            semantics,
            &[("pc", "OnlyZero")],
            &[("expected", &ends), ("actual", &ends)],
        ));
        assert!(
            partial.starts_with(
                "the view `OnlyZero` of the cell `pc`: it has no value at the expected end's `pc`: the definition gives it no value"
            ),
            "{partial}"
        );
        // `regs` has two keys, whose `keys_list` order the definition leaves to the
        // implementation: a view never rests on k-rust's choice.
        let chosen = refusal(viewed(
            semantics,
            &[("regs", "RegisterOrder")],
            &[("expected", &ends), ("actual", &ends)],
        ));
        assert!(
            chosen.starts_with(
                "the view `RegisterOrder` of the cell `regs`: it has no value at the expected end's `regs`: the definition gives it no value: its result holds an unevaluated application of the builtin function `MAP.keys_list`"
            ),
            "{chosen}"
        );
        // With a value at `pc` = 0 the same view applies.
        let zero = edited(semantics, &ends, |document| {
            document["cells"]["pc"] = json!(0);
        });
        let comparison = viewed(
            semantics,
            &[("pc", "OnlyZero")],
            &[("expected", &zero), ("actual", &zero)],
        )
        .unwrap();
        assert_eq!(
            expectation(semantics, &comparison, &zero, &zero),
            Compared::Equal
        );
    });
}

#[test]
fn a_view_must_be_a_one_parameter_function_admitting_an_observable_compared_leaf_cell() {
    with_semantics(|semantics| {
        let ends = reference(semantics);
        let both = [("expected", &ends), ("actual", &ends)];
        let sort = refusal(viewed(semantics, &[("bus", "Doubled")], &both));
        assert!(
            sort.contains("is of sort Int, which does not admit the cell's sort List"),
            "{sort}"
        );
        let arity = refusal(viewed(semantics, &[("pc", "Sum")], &both));
        assert!(
            arity.contains("takes 2 parameters; a view takes exactly one"),
            "{arity}"
        );
        let group = refusal(viewed(semantics, &[("cpu", "EventCount")], &both));
        assert!(group.contains("the cell is a group cell"), "{group}");
        let constructor = refusal(viewed(semantics, &[("pc", "CpuEvent::Read")], &both));
        assert!(
            constructor.contains("CpuEvent::Read` is a constructor"),
            "{constructor}"
        );
        assert!(matches!(
            viewed(semantics, &[("z", "Doubled")], &both),
            Err(EndError::Unobservable { .. })
        ));
        // A view of a cell the comparison does not compare would change nothing it decides.
        let mut narrowed = viewed(semantics, &[("bus", "EventCount")], &both).unwrap();
        narrowed.compare = Some(vec!["pc".to_owned()]);
        let outside = semantics
            .check_expectation(&narrowed, side("expected", &ends), side("actual", &ends))
            .unwrap_err();
        assert!(
            outside
                .to_string()
                .contains("the comparison does not compare the cell"),
            "{outside}"
        );
    });
}

#[test]
fn a_view_declared_by_an_observer_package_is_evaluated_there_and_shown_at_its_sort() {
    with_observer(|subject, observer| {
        // The compared definition does not hold the observer's view.
        assert!(subject.values().function_decl("LogShape").is_err());
        let ends = reference(subject);
        let fewer = with_bus(
            subject,
            &ends,
            json!([{"Read": {"addr": 1}}, {"Read": {"addr": 2}}]),
        );
        // The observer's view of its own sort, and one built from the compared definition's
        // constructors: both carried across by declaration.
        let read = ctor(subject, "CpuEvent::Read", vec![("addr", 0.into())]);
        let mut log = match ends.ends[0].value("bus") {
            Some(Value::List(items)) => items.clone(),
            other => panic!("a list bus: {other:?}"),
        };
        log.push(read);
        assert_eq!(
            observer
                .evaluate(
                    "WithRead",
                    vec![("log", ends.ends[0].value("bus").unwrap().clone())]
                )
                .unwrap(),
            Value::List(log)
        );
        let named = BTreeMap::from([("bus".to_owned(), "LogShape".to_owned())]);
        let mut views = subject.cell_views(observer, &named).unwrap();
        views
            .evaluate(observer, &[side("left", &fewer), side("right", &ends)])
            .unwrap();
        let comparison = Comparison {
            views,
            ..Comparison::default()
        };
        let difference = differs(
            subject
                .compare_ends(&comparison, side("left", &fewer), side("right", &ends))
                .unwrap(),
        );
        // The viewed value is of the observer's sort `Summary`, written by the observer.
        assert_eq!(difference.path.as_deref(), Some("bus.events"));
        assert_eq!(shown(&difference.left), json!(2));
        assert_eq!(shown(&difference.right), json!(3));
        assert_eq!(
            subject
                .compare_ends(&comparison, side("left", &ends), side("right", &ends))
                .unwrap(),
            Compared::Equal
        );
        // Views resolved in the observer are evaluated there only.
        let mut views = subject.cell_views(observer, &named).unwrap();
        assert!(matches!(
            views.evaluate(subject, &[side("left", &ends)]),
            Err(EndError::State(_))
        ));
    });
}

/// The comparison of every observable cell under the view `Positive` of `cell`, evaluated at
/// the ends of `sides`.
fn positive(semantics: &mut Semantics, cell: &str, sides: &[&Ends]) -> Comparison {
    let named = ["a", "b", "c", "d"];
    let sides = sides
        .iter()
        .zip(named)
        .map(|(ends, name)| (name, *ends))
        .collect::<Vec<_>>();
    viewed(semantics, &[(cell, "Positive")], &sides).unwrap()
}

/// `left` against `right` under `comparison`.
fn compared(semantics: &Semantics, comparison: &Comparison, left: &Ends, right: &Ends) -> Compared {
    semantics
        .compare_ends(comparison, side("left", left), side("right", right))
        .unwrap()
}

/// The reference end with `edit` applied to its cells' document.
fn with_cells(semantics: &Semantics, ends: &Ends, edit: impl FnOnce(&mut Json)) -> Ends {
    edited(semantics, ends, |document| edit(&mut document["cells"]))
}

#[test]
fn a_view_applies_in_every_instance_and_a_difference_always_names_the_views() {
    with_semantics(|semantics| {
        let ends = reference(semantics);
        let views =
            |cell: &str, function: &str| BTreeMap::from([(cell.to_owned(), function.to_owned())]);

        // A `List` collection: each instance viewed at its index.
        let threads = |semantics: &Semantics, counts: [i64; 2]| {
            with_cells(semantics, &ends, |cells| {
                cells["threads"]["thread"] = json!([
                    {"id": 1, "count": counts[0]},
                    {"id": 2, "count": counts[1]},
                ]);
            })
        };
        let (a, b, c) = (
            threads(semantics, [5, -3]),
            threads(semantics, [7, -1]),
            threads(semantics, [5, 4]),
        );
        let comparison = positive(semantics, "threads.thread.count", &[&a, &b, &c]);
        assert_eq!(compared(semantics, &comparison, &a, &b), Compared::Equal);
        let difference = differs(compared(semantics, &comparison, &a, &c));
        assert_eq!(difference.path.as_deref(), Some("threads.thread[1].count"));
        assert_eq!(
            (shown(&difference.left), shown(&difference.right)),
            (json!(0), json!(1))
        );
        assert_eq!(difference.views, views("threads.thread.count", "Positive"));

        // A set collection: its viewed instances are a set, so two objects that view alike are
        // one viewed instance, and an instance is named by its viewed content.
        let objects = |semantics: &Semantics, oids: &[i64]| {
            with_cells(semantics, &ends, |cells| {
                cells["objects"]["obj"] = oids.iter().map(|oid| json!({"oid": oid})).collect();
            })
        };
        let (two, one, mixed) = (
            objects(semantics, &[1, 2]),
            objects(semantics, &[3]),
            objects(semantics, &[-1, 2]),
        );
        let comparison = positive(semantics, "objects.obj.oid", &[&two, &one, &mixed]);
        assert_eq!(
            compared(semantics, &comparison, &two, &one),
            Compared::Equal
        );
        let difference = differs(compared(semantics, &comparison, &mixed, &one));
        assert_eq!(
            difference.path.as_deref(),
            Some(r#"objects.obj{{"oid":0}}"#)
        );
        assert_eq!(shown(&difference.left), json!({"oid": 0}));
        assert_eq!(difference.right.value, None);
        assert_eq!(difference.views, views("objects.obj.oid", "Positive"));

        // An optional leaf cell: a present value is viewed, an absent one stays absent.
        let timer = |semantics: &Semantics, value: Json| {
            with_cells(semantics, &ends, |cells| cells["timer"] = value)
        };
        let (five, six, absent) = (
            timer(semantics, json!([5])),
            timer(semantics, json!([6])),
            timer(semantics, json!([])),
        );
        let comparison = positive(semantics, "timer", &[&five, &six, &absent]);
        assert_eq!(
            compared(semantics, &comparison, &five, &six),
            Compared::Equal
        );
        let difference = differs(compared(semantics, &comparison, &five, &absent));
        assert_eq!(difference.path.as_deref(), Some("timer"));
        assert_eq!(
            (shown(&difference.left), shown(&difference.right)),
            (json!([1]), json!([]))
        );

        // A leaf cell of an optional group.
        let mark = |semantics: &Semantics, seen: i64| {
            with_cells(semantics, &ends, |cells| {
                cells["mark"] = json!([{"seen": seen}]);
            })
        };
        let (three, four) = (mark(semantics, 3), mark(semantics, 4));
        let comparison = positive(semantics, "mark.seen", &[&three, &four]);
        assert_eq!(
            compared(semantics, &comparison, &three, &four),
            Compared::Equal
        );

        // A difference at a cell no view applies to, and one in the class, name the views too:
        // the comparison that found them is weaker than the one without views.
        let other_pc = with_cells(semantics, &ends, |cells| cells["pc"] = json!(1));
        let stuck = edited(semantics, &ends, |document| {
            document["halt"] = json!("stuck");
        });
        let comparison = viewed(
            semantics,
            &[("bus", "EventCount")],
            &[("a", &ends), ("b", &other_pc), ("c", &stuck)],
        )
        .unwrap();
        let difference = differs(compared(semantics, &comparison, &ends, &other_pc));
        assert_eq!(difference.path.as_deref(), Some("pc"));
        assert_eq!(difference.views, views("bus", "EventCount"));
        let difference = differs(compared(semantics, &comparison, &ends, &stuck));
        assert_eq!(difference.at, DifferenceAt::Class);
        assert_eq!(difference.views, views("bus", "EventCount"));
    });
}

/// The inputs of a case on the fixture that bind the reference state's variables, `pgm` the
/// program.
fn reference_inputs(pgm: &Json) -> Json {
    json!({
        "pgm": pgm,
        "regs": {"A": 1, "B": 2},
        "f": {"Flags": {"zf": false, "cf": true}},
        "pc": 256,
        "bus": [{"Read": {"addr": 1}}, {"Read": {"addr": 2}}, {"Read": {"addr": 3}}],
        "memory": {"5": 7, "6": 8},
        "ime": false,
        "w": 9,
        "z": 10,
    })
}

/// `value` as a TOML inline value: a table's keys quoted, a string as JSON quotes it (which TOML
/// reads alike for the strings these documents hold).
fn toml_inline(value: &Json) -> String {
    match value {
        Json::Object(table) => {
            let members = table
                .iter()
                .map(|(key, value)| {
                    format!("{} = {}", Json::from(key.as_str()), toml_inline(value))
                })
                .collect::<Vec<_>>();
            format!("{{ {} }}", members.join(", "))
        }
        Json::Array(items) => {
            let items = items.iter().map(toml_inline).collect::<Vec<_>>();
            format!("[{}]", items.join(", "))
        }
        Json::Null => panic!("TOML has no null"),
        scalar => scalar.to_string(),
    }
}

/// `table` as a TOML document, each top-level key on its own line with an inline value.
fn toml_table(table: &Json) -> String {
    table
        .as_object()
        .unwrap()
        .iter()
        .fold(String::new(), |mut document, (key, value)| {
            let _ = writeln!(
                document,
                "{} = {}",
                Json::from(key.as_str()),
                toml_inline(value)
            );
            document
        })
}

/// The fixture and its observer as a workspace, with the documents `krs compare` reads in the
/// fixture's package: `end.toml`, the end of `finish(3)` from the reference state; `moved.json`,
/// that end with `pc` and `bus` changed; `partial.json`, that end without `pc`; `cases.toml`,
/// the named cases `finish` and `toss` from the reference state; and `expect.json`, a case that
/// expects `finish(3)`'s end on `k` and `pc`.
struct CompareWorkspace {
    directory: krs_test_support::TempDir,
    target: krs_test_support::SharedFixtureTarget,
}

impl CompareWorkspace {
    fn new() -> Self {
        // The end of `finish(3)` from the reference state, written by the definition itself.
        let mut end = Json::Null;
        with_semantics(|semantics| {
            let pgm = ctor(semantics, "Cmd::Finish", vec![("value", 3.into())]);
            let ends = run_end(semantics, pgm, None);
            end = semantics.end_document(&ends.ends[0]).unwrap();
        });
        assert_eq!(end["halt"], "stuck", "{end}");
        let directory = temp_dir();
        let root = directory.path();
        write_package(
            root,
            "language",
            FIXTURE,
            &manifest(PACKAGE, "ORG-KRS-EXEC-ENDS", "", false),
        );
        write_package(
            root,
            "observe",
            OBSERVER,
            &manifest(
                OBSERVER_PACKAGE,
                "ORG-KRS-EXEC-ENDS-OBSERVE",
                &format!("ends = {{ package = \"{PACKAGE}\", path = \"../language\" }}\n"),
                false,
            ),
        );
        fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"language\", \"observe\"]\nresolver = \"3\"\n",
        )
        .unwrap();
        let language = root.join("language");
        let write =
            |file: &str, contents: String| fs::write(language.join(file), contents).unwrap();
        write("end.toml", toml_table(&end));
        let mut moved = end.clone();
        moved["cells"]["pc"] = json!(257);
        moved["cells"]["bus"] = json!([{"Write": {"addr": 9, "value": 9}}, {"Read": {"addr": 2}}]);
        write("moved.json", moved.to_string());
        let mut partial = end;
        partial["cells"].as_object_mut().unwrap().remove("pc");
        write("partial.json", partial.to_string());
        let finish = json!({"Finish": {"value": 3}});
        let toss = json!({"Toss": {"value": 0}});
        write(
            "cases.toml",
            format!(
                "[[case]]\n{}\n[[case]]\n{}",
                toml_table(&json!({"name": "finish", "inputs": reference_inputs(&finish)})),
                toml_table(&json!({"name": "toss", "inputs": reference_inputs(&toss)})),
            ),
        );
        write(
            "expect.json",
            json!({
                "inputs": reference_inputs(&finish),
                "expect": {
                    "halt": "stuck",
                    "compare": ["k", "pc"],
                    "cells": {"k": {"$seq": [{"Done": {"value": 3}}]}, "pc": 256},
                },
            })
            .to_string(),
        );
        Self {
            directory,
            target: shared_fixture_target(),
        }
    }

    /// `krs compare` on the fixture with `arguments`, from its package: the exit status, stdout
    /// and stderr.
    fn compare(&self, arguments: &[&str]) -> (Option<i32>, String, String) {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        let output = process
            .current_dir(self.directory.path().join("language"))
            .args(["compare", "--package", PACKAGE, "--definition", "main"])
            .args(arguments)
            .output()
            .unwrap();
        let text = |bytes: &[u8]| String::from_utf8_lossy(bytes).into_owned();
        (
            output.status.code(),
            text(&output.stdout),
            text(&output.stderr),
        )
    }
}

/// `krs compare` reads each side as an end document or a case document, whose case it runs
/// (`FILE#NAME` naming a named case), and prints `equal` or the first difference in the lines
/// `krs run --case` prints, with the cells that also differ, or as a `krs-compare/1` document
/// whose difference is a `krs-difference/2` document; `--compare` narrows the compared cells, and
/// `--view` compares a cell on a view's value, evaluated in the compared definition or in the
/// observer `--observer` names. Two runs that may end elsewhere are inconclusive (exit 3);
/// `--expect` checks a side against a case's expectation; an end document that leaves out a
/// compared cell is refused, naming it, before the case runs.
#[test]
fn krs_compare_reads_ends_and_cases_and_prints_the_first_difference() {
    let workspace = CompareWorkspace::new();
    compare_ends_and_runs(&workspace);
    compare_under_views(&workspace);
    compare_against_expectations_and_refusals(&workspace);
}

fn compare_ends_and_runs(workspace: &CompareWorkspace) {
    // A TOML end document and a named case's run: equal.
    let (code, stdout, stderr) = workspace.compare(&["end.toml", "cases.toml#finish"]);
    assert_eq!(
        (code, stdout.as_str()),
        (Some(0), "krs compare: equal\n"),
        "{stderr}"
    );

    // The first difference in declaration order, the others listed after it.
    let (code, stdout, stderr) = workspace.compare(&["moved.json", "cases.toml#finish"]);
    assert_eq!(code, Some(1), "{stderr}");
    assert_eq!(
        stdout,
        "krs compare: differs at `pc`\n  left:  257\n  right: 256\n  also differ: `bus`\n"
    );
    let (code, stdout, stderr) =
        workspace.compare(&["moved.json", "cases.toml#finish", "--output", "json"]);
    assert_eq!(code, Some(1), "{stderr}");
    let document: Json = serde_json::from_str(&stdout).unwrap();
    assert_eq!(document["schema"], "krs-compare/1", "{document}");
    assert_eq!(document["verdict"], "differs", "{document}");
    let difference = &document["difference"];
    assert_eq!(difference["format"], DIFFERENCE_FORMAT, "{difference}");
    assert_eq!(difference["path"], "pc", "{difference}");
    assert_eq!(difference["also_differ"], json!(["bus"]), "{difference}");
    assert_eq!(difference["left"]["name"], "left", "{difference}");
    assert_eq!(difference["left"]["value"]["document"], 257, "{difference}");
    assert_eq!(
        difference["right"]["value"]["document"], 256,
        "{difference}"
    );

    // Narrowed to cells both sides agree on.
    let (code, stdout, stderr) = workspace.compare(&[
        "moved.json",
        "cases.toml#finish",
        "--compare",
        "k,f",
        "--compare",
        "cpu",
    ]);
    assert_eq!(
        (code, stdout.as_str()),
        (Some(0), "krs compare: equal\n"),
        "{stderr}"
    );

    // A run that chose among successors is not its case's only end.
    let (code, stdout, stderr) = workspace.compare(&["cases.toml#toss", "cases.toml#toss"]);
    assert_eq!(code, Some(3), "{stderr}");
    assert!(
        stdout.starts_with("krs compare: inconclusive: the left side's ends are incomplete: "),
        "{stdout}"
    );
}

fn compare_under_views(workspace: &CompareWorkspace) {
    // A view of the compared definition: the logs differ, their lengths too.
    let (code, stdout, stderr) = workspace.compare(&[
        "moved.json",
        "cases.toml#finish",
        "--compare",
        "bus",
        "--view",
        "bus=EventCount",
    ]);
    assert_eq!(code, Some(1), "{stderr}");
    assert_eq!(
        stdout,
        "krs compare: differs at `bus`\n  left:  2\n  right: 3\n  views: `bus` = `EventCount`\n"
    );
    // A view of the observer, shown at its own sort; and one under which the ends are equal,
    // which the verdict names.
    let observer = format!("{OBSERVER_PACKAGE}:main");
    let (code, stdout, stderr) = workspace.compare(&[
        "moved.json",
        "end.toml",
        "--compare",
        "bus",
        "--view",
        "bus=LogShape",
        "--observer",
        &observer,
        "--output",
        "json",
    ]);
    assert_eq!(code, Some(1), "{stderr}");
    let document: Json = serde_json::from_str(&stdout).unwrap();
    let difference = &document["difference"];
    assert_eq!(difference["path"], "bus.events", "{difference}");
    assert_eq!(
        difference["views"],
        json!({"bus": "LogShape"}),
        "{difference}"
    );
    assert_eq!(document["observer"], json!(observer), "{document}");
    assert_eq!(difference["left"]["value"]["document"], 2, "{difference}");
    let (code, stdout, stderr) = workspace.compare(&[
        "end.toml",
        "cases.toml#finish",
        "--view",
        "bus=WithRead",
        "--observer",
        &observer,
    ]);
    assert_eq!(code, Some(0), "{stderr}");
    assert_eq!(
        stdout,
        format!("krs compare: equal\n  views: `bus` = `WithRead`, in `{observer}`\n")
    );
}

fn compare_against_expectations_and_refusals(workspace: &CompareWorkspace) {
    // A side checked against a case's expectation, as `krs run --case` checks a run's end.
    let (code, stdout, stderr) = workspace.compare(&["--expect", "expect.json", "moved.json"]);
    assert_eq!(code, Some(1), "{stderr}");
    assert_eq!(
        stdout,
        "krs compare: expectation unmet at `pc`\n  expected: 256\n  actual:   257\n"
    );
    let (code, stdout, stderr) =
        workspace.compare(&["--expect", "expect.json", "cases.toml#finish"]);
    assert_eq!(
        (code, stdout.as_str()),
        (Some(0), "krs compare: expectation met\n"),
        "{stderr}"
    );

    // A compared cell an end document leaves out is refused, naming it, before the case runs;
    // an end document has no named case.
    let (code, stdout, stderr) = workspace.compare(&["partial.json", "cases.toml#toss"]);
    assert_eq!(code, Some(1), "{stdout}");
    assert!(
        stderr.contains("`partial.json`: the left end does not state the compared cell `pc`"),
        "{stderr}"
    );
    let (code, _, stderr) = workspace.compare(&["end.toml#finish", "cases.toml#finish"]);
    assert_eq!(code, Some(2), "{stderr}");
    assert!(
        stderr.contains("`end.toml` is an end document, which states one end and no named case"),
        "{stderr}"
    );
}
