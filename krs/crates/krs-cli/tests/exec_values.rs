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
    Case, CompiledStage, ConfigInputs, ConfigValue, ExecError, Float, InputFiles, NoFiles,
    ProgramInput, RunOptions, Semantics, Value, ValueError, View,
};
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};
use proptest::prelude::*;
use serde_json::json;

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

/// Run `test` on the fixture's semantics, on a thread with the stack every `krs-exec` operation needs.
fn with_semantics(test: impl FnOnce(&mut Semantics) + Send) {
    with_semantics_of(None, test);
}

/// Run `test` on the fixture's semantics, with the configuration variable `main` marked as
/// the main parameter in its Definition IR when one is given.
fn with_semantics_of(main: Option<&str>, test: impl FnOnce(&mut Semantics) + Send) {
    /// Mark every configuration variable named `variable` main; the count marked.
    fn mark(node: &mut serde_json::Value, variable: &str) -> usize {
        match node {
            serde_json::Value::Object(object) => {
                if object
                    .get("external_name")
                    .and_then(serde_json::Value::as_str)
                    == Some(variable)
                    && let Some(main) = object.get_mut("main")
                {
                    *main = serde_json::Value::Bool(true);
                    return 1;
                }
                object.values_mut().map(|child| mark(child, variable)).sum()
            }
            serde_json::Value::Array(items) => {
                items.iter_mut().map(|child| mark(child, variable)).sum()
            }
            _ => 0,
        }
    }
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn_scoped(scope, || {
                let (definition, stage) = compiled();
                let marked = main.map(|main| {
                    let mut json = serde_json::to_value(definition).unwrap();
                    assert_eq!(mark(&mut json, main), 1, "{main} is one variable");
                    serde_json::from_value::<DefinitionIr>(json).unwrap()
                });
                let mut semantics = Semantics::from_stage(
                    marked.as_ref().unwrap_or(definition),
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
    state_cells(semantics, &state)
}

/// The cells of the state a run of depth 0 reaches from `state`.
fn state_cells(semantics: &mut Semantics, state: &krs_exec::State) -> Vec<Value> {
    let report = semantics
        .run(
            state,
            RunOptions {
                depth: Some(0),
                ..RunOptions::default()
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
                    ..RunOptions::default()
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

/// Each variable of the fixture written in the typed encoding, by its parameter's Rust name:
/// the values [`values`] gives.
fn documents() -> Vec<(&'static str, serde_json::Value)> {
    vec![
        ("regs", json!({"A": 1, "C": -2})),
        ("ei", json!(true)),
        ("bus", json!([{"Read": {"addr": 1, "value": 2}}, "Idle"])),
        ("conds", json!(["C", "Z"])),
        ("name", json!("h\u{e9}llo \"q\"\n")),
        ("rom", json!([0, 255, 10, 34])),
        ("ratio", json!(1.5)),
        ("label", json!("@top")),
        ("ident", json!("x")),
        ("val", json!({"V": {"n": 7}})),
    ]
}

/// Files by name, read as the decoder asks for them; each read is recorded.
#[derive(Default)]
struct Files {
    files: std::collections::BTreeMap<String, Vec<u8>>,
    reads: Vec<(Option<String>, String)>,
}

impl Files {
    fn with(files: &[(&str, &[u8])]) -> Self {
        Self {
            files: files
                .iter()
                .map(|(name, bytes)| ((*name).to_owned(), bytes.to_vec()))
                .collect(),
            reads: Vec::new(),
        }
    }
}

impl InputFiles for Files {
    fn read(&mut self, from: Option<&str>, path: &str) -> Result<(String, Vec<u8>), String> {
        self.reads.push((from.map(str::to_owned), path.to_owned()));
        let bytes = self
            .files
            .get(path)
            .ok_or_else(|| "no such file".to_owned())?;
        Ok((path.to_owned(), bytes.clone()))
    }
}

/// The initial configuration `documents` configure, each decoded by its input's name.
fn configure_documents(
    semantics: &mut Semantics,
    documents: &[(&str, serde_json::Value)],
    files: &mut dyn InputFiles,
) -> Result<krs_exec::State, ExecError> {
    let mut variables = Vec::new();
    for (name, document) in documents {
        variables.push((*name, semantics.decode_input(name, document, files)?));
    }
    configure(semantics, variables)
}

/// The message of the refusal of `document` for the input `name`.
fn refusal(semantics: &Semantics, name: &str, document: &serde_json::Value) -> String {
    match semantics.decode_input(name, document, &mut NoFiles) {
        Err(error @ ExecError::Input(_)) => error.to_string(),
        other => panic!("{name} = {document} is accepted or refused otherwise: {other:?}"),
    }
}

#[test]
fn the_encoding_configures_what_values_configure() {
    with_semantics(|semantics| {
        let expected = configure(
            semantics,
            values(semantics)
                .into_iter()
                .map(|(name, value)| (name, value.into()))
                .collect(),
        )
        .unwrap();
        let state = configure_documents(semantics, &documents(), &mut NoFiles).unwrap();
        assert_eq!(state.kore(), expected.kore());
        // Every other spelling of the same values configures the same state: fields in
        // declaration order, longer paths, key pairs, integer strings, tagged forms, a K name.
        let alternatives = [
            ("regs", json!([["Register::A", 1], ["C", -2]])),
            (
                "regs",
                json!({"krs_exec_values_fixture::Register::A": "0x1", "C": "-2"}),
            ),
            ("bus", json!([{"Cycle::Read": [1, 2]}, {"Idle": []}])),
            (
                "bus",
                json!({"$list": [{"Read": {"addr": 1, "value": 2}}, {"Idle": {}}]}),
            ),
            (
                "conds",
                json!({"$set": [{"Condition::C": []}, {"Condition::Z": []}]}),
            ),
            ("name", json!({"$string": "h\u{e9}llo \"q\"\n"})),
            ("rom", json!({"$hex": "00FF0a22"})),
            ("BLOB", json!([0, 255, 10, 34])),
            ("$BLOB", json!({"$hex": "00ff0a22"})),
            ("ratio", json!("1.5")),
            ("ratio", json!({"$float": "1.5"})),
            ("label", json!({"$token": "@top"})),
            ("ident", json!({"$token": {"sort": "Id", "text": "x"}})),
            ("val", json!({"ValSyntax::V": [7]})),
            ("EI", json!(true)),
            ("$VAL", json!({"V": [7]})),
        ];
        for (name, alternative) in alternatives {
            let parameter = semantics.parameter(name).unwrap().name.clone();
            let mut documents = documents();
            documents.retain(|(other, _)| *other != parameter);
            documents.push((name, alternative.clone()));
            let state = configure_documents(semantics, &documents, &mut NoFiles)
                .unwrap_or_else(|error| panic!("{name} = {alternative}: {error}"));
            assert_eq!(state.kore(), expected.kore(), "{name} = {alternative}");
        }
        // A TOML case whose map comes from a data file and whose bytes from a binary file.
        let case = Case::from_toml(
            r#"
            [inputs]
            regs = { "$data-file" = "data/regs.toml" }
            ei = true
            bus = { "$data-file" = "bus.json" }
            conds = ["C", "Z"]
            name = "héllo \"q\"\n"
            rom = { "$file" = "blob.bin" }
            ratio = 1.5
            label = "@top"
            ident = "x"
            val = { V = { n = 7 } }
            "#,
        )
        .unwrap();
        let mut files = Files::with(&[
            ("data/regs.toml", b"A = 1\nC = -2\n"),
            (
                "bus.json",
                br#"[{"Read": {"addr": 1, "value": 2}}, "Idle"]"#,
            ),
            ("blob.bin", &[0, 0xff, b'\n', b'"']),
        ]);
        let inputs = semantics.case_inputs(&case, None, &mut files).unwrap();
        let state = semantics.configure(&inputs).unwrap();
        assert_eq!(state.kore(), expected.kore());
        assert_eq!(files.reads.len(), 3);
        // The same values as one JSON case.
        let case = Case::from_json(
            &json!({"inputs": documents()
                .into_iter()
                .map(|(name, document)| (name.to_owned(), document))
                .collect::<serde_json::Map<_, _>>()})
            .to_string(),
        )
        .unwrap();
        let inputs = semantics.case_inputs(&case, None, &mut NoFiles).unwrap();
        assert_eq!(
            semantics.configure(&inputs).unwrap().kore(),
            expected.kore()
        );
    });
}

#[test]
fn typed_shorthands_need_their_type() {
    with_semantics(|semantics| {
        let refused = |name, document| refusal(semantics, name, &document);
        // The elements of `$set` are untyped: a bare string there has no reading, and `C`
        // names a register and a condition.
        let bare = refused("conds", json!({"$set": ["C"]}));
        assert!(
            bare.starts_with("input `conds` (Set<Cond>) at `$set[0]`: the string \"C\" is undetermined at an untyped position"),
            "{bare}"
        );
        assert_eq!(
            refused("conds", json!({"$set": [{"C": []}]})),
            "input `conds` (Set<Cond>) at `$set[0]`: `C` names several declarations: krs_exec_values_fixture::Condition::C, krs_exec_values_fixture::Register::C"
        );
        // At a declared sort, a name resolves among that sort's constructors only.
        assert_eq!(
            refused("regs", json!({"Q": 1})),
            "input `regs` (Map<Reg, Int>) at `[key \"Q\"]`: the string \"Q\" is no value of Reg; it takes a constructor form; its constructors are A, C"
        );
        assert_eq!(
            refused("regs", json!({"A": 1, "Register::A": 2})),
            "input `regs` (Map<Reg, Int>) at `[\"Register::A\"]`: this key decodes to the same value as the key at `[\"A\"]`; K's map of two bindings of one key has no value"
        );
        assert_eq!(
            refused("conds", json!(["C", "C"])),
            "input `conds` (Set<Cond>) at `[1]`: this element decodes to the same value as the element at index 0; K's set of two equal elements has no value"
        );
        let string_bytes = refused("rom", json!("00ff"));
        assert!(
            string_bytes.contains("a string has no determined byte encoding"),
            "{string_bytes}"
        );
        assert_eq!(
            refused("regs", json!({"A": 1.5})),
            "input `regs` (Map<Reg, Int>) at `[\"A\"]`: 1.5 is no integer that JSON delivers exactly: an Int is written as an integer, and one beyond 64 bits as a string of its digits, so that it is not rounded"
        );
        // JSON delivers an integer beyond 64 bits as a float, which is refused, never rounded;
        // its digits as a string read exactly.
        let beyond = krs_exec::json_document("{\"A\": 18446744073709551616}").unwrap();
        assert!(refused("regs", beyond).contains("is no integer that JSON delivers exactly"));
        let regs = semantics
            .decode_input("regs", &json!({"A": "18446744073709551616"}), &mut NoFiles)
            .unwrap();
        let ConfigValue::Value(Value::Map(regs)) = regs else {
            panic!("{regs:?}");
        };
        assert_eq!(
            regs.values().next().unwrap().as_int().unwrap().to_string(),
            "18446744073709551616"
        );
        assert_eq!(
            refused("ei", json!(1)),
            "input `ei` (Bool): the number 1 is no value of Bool; it takes `true` or `false`"
        );
        assert_eq!(
            refused("bus", json!(["Read"])),
            "input `bus` (List<Bus>) at `[0]`: `krs_exec_values_fixture::Cycle::Read` has 2 fields (addr, value), not 0"
        );
        assert_eq!(
            refused("bus", json!([{"$text": "idle"}])),
            "input `bus` (List<Bus>) at `[0]`: `$text` stands for a whole input, which is parsed at the input's sort; inside a value write the value's own form"
        );
        assert_eq!(
            refused("bus", json!({"$set": [], "x": 1})),
            "input `bus` (List<Bus>): a tagged form is an object with exactly one key; this one has `$set`, `x`"
        );
        assert_eq!(
            refused("regs", json!({"$set": []})),
            "input `regs` (Map<Reg, Int>): `$set` gives a value of sort Set, which is not at most Map"
        );
        assert!(matches!(
            semantics.decode_input("nope", &json!(1), &mut NoFiles),
            Err(ExecError::UnknownVariable { .. })
        ));
        // A parameter is named by its Rust name (`rom`) or its K name (`BLOB`), not by the
        // lowercase of its K name.
        assert!(matches!(
            semantics.decode_input("blob", &json!([]), &mut NoFiles),
            Err(ExecError::UnknownVariable { .. })
        ));
        // A key that starts with `$` makes the object a tagged form; the map is written in pairs.
        assert_eq!(
            refused("regs", json!({"$x": 1})),
            "input `regs` (Map<Reg, Int>): unknown tag `$x`; the tags are $text, $text-file, $file, $hex, $data-file, $string, $int, $float, $token, $list, $set, $seq, $map and $call; a map with a key that starts with `$` is written as an array of [key, value] pairs"
        );
        assert_eq!(
            refused("regs", json!({"$x": 1, "A": 2})),
            "input `regs` (Map<Reg, Int>): a tagged form is an object with exactly one key; this one has `$x`, `A`; a map with a key that starts with `$` is written as an array of [key, value] pairs"
        );
        // `$text` binds a whole input as K text.
        assert_eq!(
            semantics
                .decode_input("name", &json!({"$text": "\"abc\""}), &mut NoFiles)
                .unwrap(),
            ConfigValue::Text("\"abc\"".to_owned())
        );
    });
}

#[test]
fn a_function_is_applied_with_call_and_evaluated_before_the_first_step() {
    with_semantics(|semantics| {
        let index = semantics.values().clone();
        // A function is no constructor, and a constructor no function.
        assert_eq!(
            index.ctor("ReadBack", [("addr", 3.into())]),
            Err(ValueError::WrongKind {
                decl: "krs_exec_values_fixture::ReadBack".to_owned(),
                function: true,
            })
        );
        assert!(matches!(
            index.call("Cycle::Idle", []),
            Err(ValueError::WrongKind {
                function: false,
                ..
            })
        ));
        assert_eq!(
            refusal(semantics, "bus", &json!([{"ReadBack": {"addr": 3}}])),
            "input `bus` (List<Bus>) at `[0]`: `krs_exec_values_fixture::ReadBack` is a function; write {\"$call\": {\"ReadBack\": ..}} to apply it"
        );
        assert_eq!(
            refusal(semantics, "bus", &json!([{"$call": {"Idle": []}}])),
            "input `bus` (List<Bus>) at `[0]`: `krs_exec_values_fixture::Cycle::Idle` is a constructor; write it without $call: {\"Idle\": ..}"
        );
        let call = index.call("ReadBack", [("addr", 3.into())]).unwrap();
        let decoded = semantics
            .decode_input(
                "bus",
                &json!([{"$call": {"ReadBack": {"addr": 3}}}]),
                &mut NoFiles,
            )
            .unwrap();
        assert_eq!(decoded, ConfigValue::Value(Value::list([call])));
        // The configuration holds the application, and the first state its value.
        let bus = CELLS.iter().position(|(name, _)| *name == "BUS").unwrap();
        let mut variables = values(semantics)
            .into_iter()
            .map(|(name, value)| (name, ConfigValue::from(value)))
            .collect::<Vec<_>>();
        variables[bus].1 = decoded;
        assert_eq!(
            initial_cells(semantics, variables).remove(bus),
            Value::list([read(semantics, 3, 3)])
        );
    });
}

#[test]
fn files_resolve_from_the_including_document_and_a_cycle_is_refused() {
    with_semantics(|semantics| {
        let mut files = Files::with(&[
            ("a.json", br#"{"$data-file": "b.json"}"#),
            ("b.json", br#"{"$data-file": "a.json"}"#),
            ("name.txt", b"\"abc\""),
            ("bad.txt", b"\"abc"),
        ]);
        let cycle = semantics
            .decode_input("regs", &json!({"$data-file": "a.json"}), &mut files)
            .unwrap_err();
        assert_eq!(
            cycle.to_string(),
            "input `regs` (Map<Reg, Int>) at `$data-file(a.json)$data-file(b.json)`: `$data-file` includes itself: `a.json` includes `b.json` includes `a.json`"
        );
        assert_eq!(
            files.reads,
            [
                (None, "a.json".to_owned()),
                (Some("a.json".to_owned()), "b.json".to_owned()),
                (Some("b.json".to_owned()), "a.json".to_owned()),
            ]
        );
        // `$text-file` binds the file's text, and a parse error is located in the file.
        let name = semantics
            .decode_input("name", &json!({"$text-file": "name.txt"}), &mut files)
            .unwrap();
        assert_eq!(
            name,
            ConfigValue::TextFile(ProgramInput {
                name: "name.txt".to_owned(),
                text: "\"abc\"".to_owned(),
            })
        );
        let mut variables = values(semantics)
            .into_iter()
            .map(|(name, value)| (name, ConfigValue::from(value)))
            .collect::<Vec<_>>();
        let name_cell = CELLS.iter().position(|(name, _)| *name == "NAME").unwrap();
        variables[name_cell].1 = name;
        assert_eq!(
            initial_cells(semantics, variables.clone()).remove(name_cell),
            "abc".into()
        );
        variables[name_cell].1 = semantics
            .decode_input("name", &json!({"$text-file": "bad.txt"}), &mut files)
            .unwrap();
        let Err(ExecError::Parse { input, .. }) = configure(semantics, variables) else {
            panic!("bad.txt parses");
        };
        assert!(input.starts_with("bad.txt:1:"), "{input}");
        let missing = semantics
            .decode_input("rom", &json!({"$file": "none.bin"}), &mut files)
            .unwrap_err();
        assert_eq!(
            missing.to_string(),
            "input `rom` (Bytes): `$file` `none.bin`: no such file"
        );
    });
}

#[test]
fn a_definition_without_a_main_parameter_takes_no_program_file() {
    with_semantics(|semantics| {
        assert!(semantics.main_parameter().is_none());
        assert_eq!(
            semantics
                .parameters()
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            [
                "regs: Map<Reg, Int>",
                "ei: Bool",
                "bus: List<Bus>",
                "conds: Set<Cond>",
                "name: String",
                "rom: Bytes",
                "ratio: Float",
                "label: Label",
                "ident: Id",
                "val: Val"
            ]
        );
        let stray = semantics
            .configure(&ConfigInputs {
                program: Some(ProgramInput {
                    name: "prog.txt".to_owned(),
                    text: "idle".to_owned(),
                }),
                ..ConfigInputs::default()
            })
            .unwrap_err();
        assert_eq!(
            stray.to_string(),
            "the #[k::init] has no main parameter (none is marked #[k::config_var(main)] or read in the computation cell), so FILE binds nothing; bind its parameters by name: regs: Map<Reg, Int>, ei: Bool, bus: List<Bus>, conds: Set<Cond>, name: String, rom: Bytes, ratio: Float, label: Label, ident: Id, val: Val"
        );
        // Two spellings of one parameter bind it twice.
        let mut variables = values(semantics)
            .into_iter()
            .map(|(name, value)| (name, ConfigValue::from(value)))
            .collect::<Vec<_>>();
        variables.push(("ei", Value::from(true).into()));
        let twice = configure(semantics, variables).unwrap_err();
        assert_eq!(
            twice.to_string(),
            "configuration variable `$EI` (init parameter ei) is bound twice"
        );
    });
}

#[test]
fn a_declared_sort_reads_the_builtin_its_json_type_names() {
    with_semantics(|semantics| {
        let index = semantics.values().clone();
        let decoded = |document: serde_json::Value| match semantics.decode_input(
            "val",
            &document,
            &mut NoFiles,
        ) {
            Ok(ConfigValue::Value(value)) => value,
            other => panic!("val = {document}: {other:?}"),
        };
        // `Val` has the builtin subsorts Int, String and Float: a string is a String there,
        // never an Int, an integer an Int, and a number with a fraction a Float.
        assert_eq!(decoded(json!("12")), Value::from("12"));
        assert_eq!(decoded(json!(3)), 3.into());
        assert_eq!(decoded(json!(2.5)), Float::from_f64(2.5).into());
        assert_eq!(decoded(json!({"$float": 2.0})), Float::from_f64(2.0).into());
        assert_eq!(
            decoded(json!({"$int": "18446744073709551616"}))
                .as_int()
                .unwrap()
                .to_string(),
            "18446744073709551616"
        );
        assert_eq!(
            decoded(json!({"Nothing": []})),
            index.ctor("ValSyntax::Nothing", []).unwrap()
        );
        // A float with an integral value may be a rounded integer beyond 64 bits.
        assert_eq!(
            refusal(semantics, "val", &json!(2.0)),
            "input `val` (Val): 2.0 is undetermined at Val: JSON delivers an integer beyond 64 bits as a float, so a float with an integral value reads as an Int or a Float; write a Float as {\"$float\": 2.0} and an Int as an integer or {\"$int\": \"digits\"}"
        );
        // A bare string that names a nullary constructor is also a String.
        assert_eq!(
            refusal(semantics, "val", &json!("Nothing")),
            "input `val` (Val): the string \"Nothing\" reads several ways at Val: as a `String` ({\"$string\": ..}), or the constructor `krs_exec_values_fixture::ValSyntax::Nothing` ({\"krs_exec_values_fixture::ValSyntax::Nothing\": ..}); write the form of the one meant"
        );
        // `Real`'s only builtin subsort is Float: every number is a Float there.
        let real = |x: f64| {
            index
                .ctor("ValSyntax::R", [("x", Float::from_f64(x).into())])
                .unwrap()
        };
        assert_eq!(decoded(json!({"R": {"x": 2.0}})), real(2.0));
        assert_eq!(decoded(json!({"R": [3]})), real(3.0));
        let inexact = refusal(semantics, "val", &json!({"R": [9_007_199_254_740_993_u64]}));
        assert!(
            inexact.starts_with(
                "input `val` (Val) at `.R.x`: 9007199254740993 is no binary64 value exactly"
            ),
            "{inexact}"
        );
        let string = refusal(semantics, "val", &json!({"R": ["1.5"]}));
        assert!(
            string.contains("a value of its builtin subsorts Float"),
            "{string}"
        );
        // The decoded values configure.
        let configured = [
            (decoded(json!("12")), Value::from("12")),
            (decoded(json!({"R": [3]})), real(3.0)),
        ];
        let at = CELLS.iter().position(|(name, _)| *name == "VAL").unwrap();
        for (value, expected) in configured {
            let mut variables = values(semantics)
                .into_iter()
                .map(|(name, value)| (name, ConfigValue::from(value)))
                .collect::<Vec<_>>();
            variables[at].1 = value.into();
            assert_eq!(initial_cells(semantics, variables).remove(at), expected);
        }
    });
}

#[test]
fn a_number_at_float_is_its_binary64_value_or_refused() {
    with_semantics(|semantics| {
        let decoded = |document: &serde_json::Value| match semantics.decode_input(
            "ratio",
            document,
            &mut NoFiles,
        ) {
            Ok(ConfigValue::Value(value)) => value.as_float().unwrap().to_f64(),
            other => panic!("ratio = {document}: {other:?}"),
        };
        assert_eq!(decoded(&json!(3)), Some(3.0));
        // 2^63 is beyond i64 and a binary64 value.
        assert_eq!(
            decoded(&json!({"$float": 9_223_372_036_854_775_808_u64})),
            Some(9_223_372_036_854_775_808.0)
        );
        let inexact = refusal(semantics, "ratio", &json!(9_007_199_254_740_993_u64));
        assert!(
            inexact.contains("is no binary64 value exactly"),
            "{inexact}"
        );
        // JSON delivers an integer beyond 64 bits as a float, rounded: refused, not taken.
        let beyond = krs_exec::json_document("18446744073709551617").unwrap();
        let rounded = refusal(semantics, "ratio", &beyond);
        assert!(
            rounded.contains("is a float that an integer beyond the 64-bit integers rounds to"),
            "{rounded}"
        );
        assert!(refusal(semantics, "ratio", &json!({"$float": beyond})).contains("`$float`: "));
    });
}

#[test]
fn file_binds_the_main_parameter_whatever_its_k_name() {
    with_semantics_of(Some("NAME"), |semantics| {
        let main = semantics.main_parameter().unwrap();
        assert_eq!(
            (main.name.as_str(), main.variable.as_str()),
            ("name", "NAME")
        );
        assert!(semantics.variables()[0].is_main);
        assert_eq!(semantics.variables()[0].name, "NAME");
        let file = |text: &str| ProgramInput {
            name: "prog.txt".to_owned(),
            text: text.to_owned(),
        };
        let others = values(semantics)
            .into_iter()
            .filter(|(name, _)| *name != "NAME")
            .map(|(name, value)| (name.to_owned(), ConfigValue::from(value)))
            .collect::<Vec<_>>();
        // FILE is read as `-c` text of the main parameter, at its sort.
        let state = semantics
            .configure(&ConfigInputs {
                program: Some(file("\"abc\"")),
                variables: others.clone(),
                ..ConfigInputs::default()
            })
            .unwrap();
        let at = CELLS.iter().position(|(name, _)| *name == "NAME").unwrap();
        assert_eq!(state_cells(semantics, &state).remove(at), "abc".into());
        let Err(ExecError::Parse { input, .. }) = semantics.configure(&ConfigInputs {
            program: Some(file("abc\"")),
            variables: others.clone(),
            ..ConfigInputs::default()
        }) else {
            panic!("the text parses");
        };
        assert!(input.starts_with("prog.txt"), "{input}");
        // FILE and a binding by name, by either name, bind it twice.
        for written in ["name", "$NAME"] {
            let mut variables = others.clone();
            variables.push((written.to_owned(), Value::from("x").into()));
            let twice = semantics
                .configure(&ConfigInputs {
                    program: Some(file("\"abc\"")),
                    variables,
                    ..ConfigInputs::default()
                })
                .unwrap_err();
            assert_eq!(
                twice.to_string(),
                "configuration variable `$NAME` (init parameter name) is bound twice"
            );
        }
        // Bound by name alone it needs no FILE; bound by neither it is missing.
        let mut variables = others.clone();
        variables.push(("name".to_owned(), Value::from("abc").into()));
        let by_name = semantics
            .configure(&ConfigInputs {
                variables,
                ..ConfigInputs::default()
            })
            .unwrap();
        assert_eq!(by_name.kore(), state.kore());
        let missing = semantics
            .configure(&ConfigInputs {
                variables: others,
                ..ConfigInputs::default()
            })
            .unwrap_err();
        assert_eq!(
            missing.to_string(),
            "the main parameter `name` ($NAME: String) is unbound; pass FILE, `-` for standard input, or bind `name` by name"
        );
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
                    ..RunOptions::default()
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
                    ..RunOptions::default()
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
