//! `krs-exec` ends and their comparison on an authored definition: a run's and a search's ends
//! read by Rust field path (stopped, undefined and depth-bound ends included), end documents
//! written and read back, the compared cells (unobservable ones left out, narrowing), the first
//! difference's path and values (a value with no document shown as K text), the rules for sets
//! of ends, and what is no end: an inconclusive run and a constrained state.
//!
//! The fixture (`fixtures/ends`) copies every configuration variable into its own cell, so a run
//! of depth 0 ends with the values it was given; `toss` steps to `done(0)` or `done(1)`, and
//! `finish(v)` to `done(v)` by the rule `finish`.

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

/// The fixture's Definition IR and compiled stage, built once per test process.
fn compiled() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| {
        let target = shared_fixture_target();
        let temporary = temp_dir();
        let project = temporary.path().join("language");
        fs::create_dir_all(project.join("src")).unwrap();
        fs::write(project.join("src/lib.rs"), FIXTURE).unwrap();
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        fs::write(
            project.join("Cargo.toml"),
            format!(
                "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-EXEC-ENDS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
            ),
        )
        .unwrap();
        let emitted = temporary.path().join("emitted");
        let mut process = krs_command!();
        fixture_build_env(&mut process, target.path());
        let output = process
            .current_dir(&project)
            .args(["emit-k", "--ir", "--manifest-path"])
            .arg(project.join("Cargo.toml"))
            .args(["--package", PACKAGE, "--definition", "main", "--output"])
            .arg(&emitted)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let definition: DefinitionIr =
            serde_json::from_slice(&fs::read(emitted.join("definition-ir.json")).unwrap())
                .unwrap();
        let stage = CompiledStage::compile(&definition, &mut Timings::disabled()).unwrap();
        (definition, stage)
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
                "format": "krs-difference/1",
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
                rule: Some("finish".to_owned()),
            }
        );
        assert_eq!(end.value("k"), Some(&Value::seq([done(semantics, 3)])));
        let document = semantics.end_document(end).unwrap();
        assert_eq!(document["rule"], json!("finish"));
        assert_eq!(&semantics.read_end(&document).unwrap(), end);
        let all = Comparison::default();
        let same = Ends::one(semantics.read_end(&document).unwrap());
        assert_eq!(
            expectation(semantics, &all, &same, &stopped),
            Compared::Equal
        );
        // Another rewrite rule of the definition is another class.
        let other = edited(semantics, &stopped, |document| {
            document["rule"] = json!("toss_heads");
        });
        let difference = differs(expectation(semantics, &all, &other, &stopped));
        assert_eq!(difference.at, DifferenceAt::Class);
        assert_eq!(difference.left.class.rule.as_deref(), Some("toss_heads"));
        assert_eq!(difference.right.class.rule.as_deref(), Some("finish"));
        // A rule the definition does not have stops none of its runs, and a rule is named
        // without its crate's name: both are refused, not compared.
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
        let message = refused("finsh");
        assert!(
            message.contains("`finish`") && message.contains("`toss_heads`"),
            "{message}"
        );
        let message = refused("krs_exec_ends_fixture::finish");
        assert!(
            message.contains("`finish`, not `krs_exec_ends_fixture::finish`"),
            "{message}"
        );
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
