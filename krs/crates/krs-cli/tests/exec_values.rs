//! `krs-exec` values and views on an authored definition: configuration inputs given as values,
//! results read by KRS names, and their agreement with configuration text.
//!
//! The fixture (`fixtures/values`) copies every configuration variable into its own cell, so a
//! run of depth 0 shows each value the configuration was given.

use std::fs;
use std::path::Path;
use std::sync::OnceLock;

use k_rust::kore::ast::{KoreString, Pattern, Sort, Symbol, Variable, VariableKind};
use krs_exec::{
    CompiledStage, ConfigInputs, ConfigValue, ExecError, Float, RunOptions, Semantics, Value,
    ValueError, View,
};
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};
use proptest::prelude::*;

const FIXTURE: &str = include_str!("fixtures/values/src/lib.rs");
const PACKAGE: &str = "krs-exec-values-fixture";

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
                "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-EXEC-VALUES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
            ),
        )
        .unwrap();
        let emitted = temporary.path().join("emitted");
        let mut process = krs_command!();
        fixture_build_env(&mut process, target.path());
        let output = process
            .current_dir(&project)
            .arg("emit-k")
            .args(["--manifest-path"])
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

/// Run `test` on the fixture's semantics, on a thread with the stack every `krs-exec` operation needs.
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

fn ctor(semantics: &Semantics, name: &str) -> Value {
    semantics.values().ctor(name, []).unwrap()
}

fn read(semantics: &Semantics, addr: i64, value: i64) -> Value {
    semantics
        .values()
        .ctor(
            "Cycle::Read",
            [("value", value.into()), ("addr", addr.into())],
        )
        .unwrap()
}

/// One value per configuration variable, every kind of value among them.
fn values(semantics: &Semantics) -> Vec<(&'static str, Value)> {
    let index = semantics.values();
    vec![
        (
            "REGS",
            Value::map([
                (ctor(semantics, "Register::A"), 1.into()),
                (ctor(semantics, "Register::C"), (-2).into()),
            ]),
        ),
        ("EI", true.into()),
        (
            "BUS",
            Value::list([read(semantics, 1, 2), ctor(semantics, "Cycle::Idle")]),
        ),
        (
            "CONDS",
            Value::set([
                ctor(semantics, "Condition::C"),
                ctor(semantics, "Condition::Z"),
            ]),
        ),
        ("NAME", "h\u{e9}llo \"q\"\n".into()),
        ("BLOB", vec![0_u8, 0xff, b'\n', b'"'].into()),
        ("RATIO", Float::from_f64(1.5).into()),
        (
            "LABEL",
            Value::Token {
                sort: index.sort("Label").unwrap(),
                text: "@top".to_owned(),
            },
        ),
        (
            "IDENT",
            Value::Token {
                sort: index.sort("Id").unwrap(),
                text: "x".to_owned(),
            },
        ),
        (
            "VAL",
            index.ctor("ValSyntax::V", [("n", 7.into())]).unwrap(),
        ),
    ]
}

/// The cell each variable is copied into.
const CELLS: [(&str, &str); 10] = [
    ("REGS", "cpu.regs"),
    ("EI", "cpu.ei_pending"),
    ("BUS", "bus"),
    ("CONDS", "conds"),
    ("NAME", "name"),
    ("BLOB", "blob"),
    ("RATIO", "ratio"),
    ("LABEL", "label"),
    ("IDENT", "ident"),
    ("VAL", "val"),
];

fn configure(
    semantics: &mut Semantics,
    variables: Vec<(&str, ConfigValue)>,
) -> Result<krs_exec::State, ExecError> {
    semantics.configure(&ConfigInputs {
        variables: variables
            .into_iter()
            .map(|(name, value)| (name.to_owned(), value))
            .collect(),
        ..ConfigInputs::default()
    })
}

/// The cells of the state a run of depth 0 reaches from `variables`.
fn initial_cells(semantics: &mut Semantics, variables: Vec<(&str, ConfigValue)>) -> Vec<Value> {
    let state = configure(semantics, variables).unwrap();
    let report = semantics
        .run(
            &state,
            RunOptions {
                depth: Some(0),
                trace: false,
            },
        )
        .unwrap();
    let View::State(view) = semantics.view(&report.state).unwrap() else {
        panic!("the initial state is defined");
    };
    CELLS
        .iter()
        .map(|(_, path)| view.value(path).unwrap())
        .collect()
}

#[test]
fn values_configure_and_read_back_by_krs_names() {
    with_semantics(|semantics| {
        let given = values(semantics);
        let variables = given
            .iter()
            .map(|(name, value)| (*name, value.clone().into()))
            .collect();
        let state = configure(semantics, variables).unwrap();
        let report = semantics
            .run(
                &state,
                RunOptions {
                    depth: Some(0),
                    trace: false,
                },
            )
            .unwrap();
        let View::State(view) = semantics.view(&report.state).unwrap() else {
            panic!("the initial state is defined");
        };
        for ((variable, value), (cell_variable, path)) in given.iter().zip(CELLS) {
            assert_eq!(variable, &cell_variable);
            assert_eq!(&view.value(path).unwrap(), value, "{path}");
        }
        // The renamed cell is addressed by its Rust field, through its group or from it.
        assert_eq!(
            view.at("cpu").unwrap().value("ei_pending").unwrap(),
            true.into()
        );
        assert!(matches!(
            view.value("eiPending"),
            Err(krs_exec::CellError::Unknown { .. })
        ));
        assert_eq!(view.value("k").unwrap(), Value::seq([]));
        // `timer` is optional and starts absent; `thread` starts with one instance.
        assert!(!view.present("timer").unwrap());
        assert!(matches!(
            view.value("timer"),
            Err(krs_exec::CellError::Absent { .. })
        ));
        let threads = view.instances("threads.thread").unwrap();
        assert_eq!(threads.len(), 1);
        assert_eq!(threads[0].value("id").unwrap(), 0.into());
        assert!(matches!(
            view.value("threads.thread.id"),
            Err(krs_exec::CellError::Kind { .. })
        ));
        assert!(view.constraints().is_empty());
        // A constructor names its declaration, not its emitted symbol (`registerC`).
        let regs = view.value("cpu.regs").unwrap();
        let keys = regs
            .as_map()
            .unwrap()
            .keys()
            .map(|key| key.as_ctor().unwrap().decl().path().to_owned())
            .collect::<Vec<_>>();
        assert_eq!(
            keys,
            [
                "krs_exec_values_fixture::Register::A",
                "krs_exec_values_fixture::Register::C"
            ]
        );
        assert_eq!(
            view.value("ratio").unwrap().as_float().unwrap().to_f64(),
            Some(1.5)
        );
    });
}

#[test]
fn text_and_values_configure_the_same_state() {
    with_semantics(|semantics| {
        let texts = [
            ("REGS", "a |-> 1"),
            ("EI", "true"),
            ("BUS", "ListItem(read(1, 2)) ListItem(idle)"),
            ("CONDS", "SetItem(z)"),
            ("NAME", "\"abc\""),
            ("BLOB", "b\"\\x00\\xff\""),
            ("RATIO", "1.5"),
            ("LABEL", "@top"),
            ("IDENT", "x"),
            ("VAL", "v(7)"),
        ];
        let from_text = initial_cells(
            semantics,
            texts
                .iter()
                .map(|(name, text)| (*name, (*text).into()))
                .collect(),
        );
        let decoded = CELLS
            .iter()
            .map(|(variable, _)| *variable)
            .zip(from_text.clone())
            .map(|(variable, value)| (variable, value.into()))
            .collect();
        assert_eq!(initial_cells(semantics, decoded), from_text);
        // Without a float, whose literal text is not canonical, the configured patterns agree.
        let ratio = ("RATIO", ConfigValue::Text("1.5".to_owned()));
        let text_state = configure(
            semantics,
            texts
                .iter()
                .map(|(name, text)| (*name, (*text).into()))
                .collect(),
        )
        .unwrap();
        let value_state = configure(
            semantics,
            CELLS
                .iter()
                .map(|(variable, _)| *variable)
                .zip(from_text)
                .map(|(variable, value)| match variable {
                    "RATIO" => ratio.clone(),
                    _ => (variable, value.into()),
                })
                .collect(),
        )
        .unwrap();
        assert_eq!(value_state.kore(), text_state.kore());
    });
}

#[test]
fn a_value_names_the_constructor_that_text_leaves_ambiguous() {
    with_semantics(|semantics| {
        let mut variables = values(semantics)
            .into_iter()
            .map(|(name, value)| (name, ConfigValue::from(value)))
            .collect::<Vec<_>>();
        // `c` is `Register::C` and `Condition::C`; a Map key is read at KItem, where both fit.
        variables[0].1 = "c |-> 1".into();
        assert!(matches!(
            configure(semantics, variables.clone()),
            Err(ExecError::Parse { .. })
        ));
        let register = ctor(semantics, "Register::C");
        variables[0].1 = Value::map([(register.clone(), 1.into())]).into();
        let cells = initial_cells(semantics, variables);
        assert_eq!(cells[0], Value::map([(register, 1.into())]));
    });
}

#[test]
fn a_value_must_be_a_term_of_its_variable_sort() {
    with_semantics(|semantics| {
        let mut variables = values(semantics)
            .into_iter()
            .map(|(name, value)| (name, ConfigValue::from(value)))
            .collect::<Vec<_>>();
        let val = variables.len() - 1;
        variables[val].1 = ctor(semantics, "Condition::C").into();
        let error = configure(semantics, variables.clone()).unwrap_err();
        assert!(
            matches!(&error, ExecError::Value { variable, .. } if variable == "VAL"),
            "{error}"
        );
        assert!(error.to_string().contains("Cond"), "{error}");
        // A field of the wrong sort is the value's error too.
        variables[val].1 = semantics
            .values()
            .ctor("ValSyntax::V", [("n", 7.into())])
            .unwrap()
            .into();
        let bad_field = semantics
            .values()
            .ctor("Cycle::Read", [("addr", true.into()), ("value", 2.into())])
            .unwrap();
        variables[2].1 = Value::list([bad_field]).into();
        let error = configure(semantics, variables.clone()).unwrap_err();
        assert!(
            matches!(&error, ExecError::Value { variable, .. } if variable == "BUS"),
            "{error}"
        );
        variables[2].1 = Value::list([]).into();
        variables[val].1 = Value::Opaque(variable("X", "SortVal")).into();
        assert!(matches!(
            configure(semantics, variables),
            Err(ExecError::Value {
                error: ValueError::Unencodable(_),
                ..
            })
        ));
    });
}

#[test]
fn a_parametric_constructor_decodes_with_its_sort_arguments_and_configures_again() {
    with_semantics(|semantics| {
        let mut variables = values(semantics)
            .into_iter()
            .map(|(name, value)| (name, ConfigValue::from(value)))
            .collect::<Vec<_>>();
        let val = variables.len() - 1;
        variables[val].1 = "wrap(v(7))".into();
        let wrapped = initial_cells(semantics, variables.clone()).remove(val);
        let ctor = wrapped.as_ctor().unwrap();
        assert_eq!(ctor.decl().path(), "krs_exec_values_fixture::Wrap");
        assert_eq!(ctor.sort_args(), [semantics.values().sort("Val").unwrap()]);
        assert_eq!(
            ctor.field("inner").unwrap().as_ctor().unwrap().field("n"),
            Some(&7.into())
        );
        // The builder takes no sort arguments.
        assert!(matches!(
            semantics.values().ctor("Wrap", [("inner", 7.into())]),
            Err(ValueError::Unencodable(_))
        ));
        variables[val].1 = wrapped.clone().into();
        assert_eq!(initial_cells(semantics, variables).remove(val), wrapped);
    });
}

#[test]
fn names_resolve_by_unique_path_suffix() {
    with_semantics(|semantics| {
        let index = semantics.values();
        assert_eq!(
            index.decl("Register::C").unwrap().path(),
            "krs_exec_values_fixture::Register::C"
        );
        assert_eq!(
            index
                .decl("krs_exec_values_fixture::Register::C")
                .unwrap()
                .path(),
            "krs_exec_values_fixture::Register::C"
        );
        assert_eq!(
            index.decl("C"),
            Err(ValueError::AmbiguousName {
                name: "C".to_owned(),
                candidates: vec![
                    "krs_exec_values_fixture::Condition::C".to_owned(),
                    "krs_exec_values_fixture::Register::C".to_owned()
                ],
            })
        );
        assert_eq!(
            index.decl("Register::B"),
            Err(ValueError::UnknownName {
                kind: "constructor",
                name: "Register::B".to_owned(),
                candidates: Vec::new(),
            })
        );
        // `ster::C` is no `::`-aligned suffix.
        assert!(index.decl("ster::C").is_err());
        assert!(matches!(
            index.ctor("Cycle::Read", [("addr", 1.into())]),
            Err(ValueError::Fields { .. })
        ));
        assert_eq!(
            index.sort("Reg").unwrap().to_string(),
            "krs_exec_values_fixture::Reg"
        );
        assert_eq!(index.sort("Int").unwrap().to_string(), "Int");
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

fn application(name: &str, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: name.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments,
    }
}

#[test]
fn states_split_into_disjuncts_and_keep_their_constraints() {
    with_semantics(|semantics| {
        let variables = values(semantics)
            .into_iter()
            .map(|(name, value)| (name, value.into()))
            .collect();
        let state = configure(semantics, variables).unwrap();
        let report = semantics
            .run(
                &state,
                RunOptions {
                    depth: Some(0),
                    trace: false,
                },
            )
            .unwrap();
        let configuration = report.state.kore().clone();
        let top = sort("SortGeneratedTopCell");
        let constraint = Pattern::Equals {
            operand_sort: Box::new(sort("SortInt")),
            result_sort: top.clone(),
            left: Box::new(variable("N", "SortInt")),
            right: Box::new(Pattern::DomainValue {
                sort: sort("SortInt"),
                value: KoreString::from("3"),
            }),
        };
        let disjunction = Pattern::Or {
            sort: top.clone(),
            arguments: vec![
                Pattern::And {
                    sort: top.clone(),
                    arguments: vec![configuration.clone(), constraint],
                },
                Pattern::Bottom { sort: top.clone() },
            ],
        };
        let term = semantics.term(disjunction).unwrap();
        let views = semantics.views(&term).unwrap();
        let [View::State(view), View::Bottom] = views.as_slice() else {
            panic!("expected a state and bottom, got {views:?}");
        };
        assert_eq!(view.constraints().len(), 1);
        assert_eq!(view.value("cpu.ei_pending").unwrap(), true.into());
        assert!(matches!(
            semantics.view(&term),
            Err(ValueError::Malformed(_))
        ));
        let bottom = semantics.term(Pattern::Bottom { sort: top }).unwrap();
        assert!(matches!(semantics.view(&bottom), Ok(View::Bottom)));
    });
}

#[test]
fn what_has_no_krs_description_decodes_opaque_and_what_is_no_term_is_an_error() {
    with_semantics(|semantics| {
        let index = semantics.values().clone();
        // A variable, and a map with a frame, are opaque.
        let x = variable("X", "SortInt");
        assert_eq!(index.decode(&x).unwrap(), Value::Opaque(x.clone()));
        let map = values(semantics).remove(0).1;
        let state = configure(
            semantics,
            values(semantics)
                .into_iter()
                .map(|(name, value)| (name, value.into()))
                .collect(),
        )
        .unwrap();
        let report = semantics
            .run(
                &state,
                RunOptions {
                    depth: Some(0),
                    trace: false,
                },
            )
            .unwrap();
        let regs = cell_content(report.state.kore(), "Lbl'-LT-'regs'-GT-'");
        assert_eq!(index.decode(&regs).unwrap(), map);
        let Pattern::Application { symbol, .. } = &regs else {
            panic!("a map is an application");
        };
        let framed = Pattern::Application {
            symbol: symbol.clone(),
            arguments: vec![regs.clone(), variable("M", "SortMap")],
        };
        assert_eq!(
            index.decode(&framed).unwrap(),
            Value::Opaque(framed.clone())
        );
        // A literal its sort does not have, and a symbol the definition does not declare.
        let bad = Pattern::DomainValue {
            sort: sort("SortInt"),
            value: KoreString::from("one"),
        };
        assert!(matches!(index.decode(&bad), Err(ValueError::Malformed(_))));
        assert!(matches!(
            index.decode(&application("LblnoSuchSymbol", Vec::new())),
            Err(ValueError::Malformed(_))
        ));
        assert!(!Value::Opaque(x).is_ground());
    });
}

/// The content of the first cell labelled `symbol` in `pattern`.
fn cell_content(pattern: &Pattern, symbol: &str) -> Pattern {
    let mut stack = vec![pattern];
    while let Some(pattern) = stack.pop() {
        if let Pattern::Application {
            symbol: head,
            arguments,
        } = pattern
        {
            if head.name == symbol {
                return arguments[0].clone();
            }
            stack.extend(arguments);
        }
    }
    panic!("no cell {symbol}")
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn every_generated_value_reads_back_unchanged(
        regs in proptest::collection::btree_map(any::<bool>(), any::<i64>(), 0..3),
        bus in proptest::collection::vec(proptest::option::of((any::<i64>(), any::<i64>())), 0..4),
        conds in proptest::collection::btree_set(any::<bool>(), 0..3),
        name in ".{0,8}",
        blob in proptest::collection::vec(any::<u8>(), 0..8),
        ratio in any::<f64>(),
        n in any::<i64>(),
    ) {
        with_semantics(|semantics| {
            let register = |c: bool| ctor(semantics, if c { "Register::C" } else { "Register::A" });
            let condition = |c: bool| ctor(semantics, if c { "Condition::C" } else { "Condition::Z" });
            let mut given = values(semantics);
            given[0].1 = Value::map(regs.iter().map(|(key, value)| (register(*key), (*value).into())));
            given[2].1 = Value::list(bus.iter().map(|cycle| match cycle {
                Some((addr, value)) => read(semantics, *addr, *value),
                None => ctor(semantics, "Cycle::Idle"),
            }));
            given[3].1 = Value::set(conds.iter().map(|c| condition(*c)));
            given[4].1 = name.as_str().into();
            given[5].1 = blob.clone().into();
            given[6].1 = Float::from_f64(ratio).into();
            given[9].1 = semantics.values().ctor("ValSyntax::V", [("n", n.into())]).unwrap();
            let cells = initial_cells(
                semantics,
                given.iter().map(|(name, value)| (*name, value.clone().into())).collect(),
            );
            let expected = given.into_iter().map(|(_, value)| value).collect::<Vec<_>>();
            assert_eq!(cells, expected);
        });
    }
}
