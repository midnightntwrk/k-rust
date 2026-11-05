//! A declared type types every document of its position: a constructor's field, a function's
//! parameter and a function's result declared `Map<Reg8, Int>` read and write the short form of
//! the typed encoding (`{"B": 1}`), as a parameter or a cell of that type does, and a difference
//! below them names a key by its document at the key type (`["B"]`).
//!
//! The definition's one cell, `snap`, holds a `Snapshot::Cpu { regs: Map<Reg8, Int>, pc: Int }`
//! copied from its one input; `Boot(regs)` is the snapshot of `regs` at `pc` 0, a function whose
//! parameter is a typed map, and `Registers(snap)` a snapshot's registers, a view whose result is
//! a map keyed by a constructor.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::sync::OnceLock;

use krs_exec::{
    Compared, Comparison, CompiledStage, ConfigInputs, ConfigValue, Ends, NoFiles, RunOptions,
    Semantics, Side, Value,
};
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};
use serde_json::{Value as Json, json};

const PACKAGE: &str = "krs-cli-field-types-fixture";

const FIXTURE: &str = r#"
use k::KResult;
use k::Term;
use k::builtin::{Int, KSequence, Map};

k::sorts! {
    Reg8;
    Snap;
}

#[k::constructors(sort = Reg8, result = KResult)]
#[k::precedence((B, C))]
#[rustfmt::skip]
pub enum Register8 {
    #[k::syntax("b")] B,
    #[k::syntax("c")] C,
}

#[k::constructors(sort = Snap, result = KResult)]
#[rustfmt::skip]
pub enum Snapshot {
    #[k::syntax("cpu({regs}, {pc})")] Cpu { regs: Map<Reg8, Int>, pc: Int },
}

/// The snapshot of `regs` at `pc` 0.
#[k::function(total, internal)]
pub fn Boot(regs: Term<Map<Reg8, Int>>) -> Term<Snap> {
    Snapshot::Cpu(regs, 0)
}

/// A snapshot's registers.
#[k::function(total, internal)]
pub fn Registers(snap: Term<Snap>) -> Term<Map<Reg8, Int>>;

#[k::equation]
fn registers(
    k::term![Registers(Snapshot::Cpu { regs, pc })]: Term<Map>,
) -> Term<Map> {
    regs
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub snap: Snap,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "SNAP")] snap: Snap) -> Self {
        Self { k: k::k![], snap }
    }
}
"#;

/// The fixture's Definition IR, as `krs emit-k --ir` builds it, and its compiled stage, built
/// once per test process.
fn compiled() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| {
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
                "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-FIELD-TYPES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
            ),
        )
        .unwrap();
        let emitted = temporary.path().join("emitted");
        let target = shared_fixture_target();
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

/// The value the input `snap` reads from `document`.
fn input(semantics: &Semantics, document: &Json) -> Value {
    match semantics.decode_input("snap", document, &mut NoFiles) {
        Ok(ConfigValue::Value(value)) => value,
        other => panic!("{document} reads as no value: {other:?}"),
    }
}

/// The end of the run of depth 0 from the state whose input `snap` is `snap`.
fn configured(semantics: &mut Semantics, snap: Value) -> Ends {
    let state = semantics
        .configure(&ConfigInputs {
            variables: [("SNAP".to_owned(), ConfigValue::Value(snap))]
                .into_iter()
                .collect(),
            ..ConfigInputs::default()
        })
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
    semantics.end_of(&report).unwrap()
}

/// The snapshot `Cpu { regs, pc }` with the registers `regs` (register name, value).
fn snapshot(semantics: &Semantics, regs: &[(&str, i64)], pc: i64) -> Value {
    let values = semantics.values();
    let regs = Value::map(regs.iter().map(|(register, value)| {
        (
            values
                .ctor(&format!("Register8::{register}"), Vec::new())
                .unwrap(),
            Value::from(*value),
        )
    }));
    values
        .ctor("Snapshot::Cpu", vec![("regs", regs), ("pc", pc.into())])
        .unwrap()
}

#[test]
fn a_constructor_field_and_a_call_argument_read_a_typed_map_in_short_form() {
    with_semantics(|semantics| {
        // A constructor's field: the key "B" reads at the field's key type, `Reg8`.
        assert_eq!(
            input(
                semantics,
                &json!({"Cpu": {"regs": {"B": 1, "C": 2}, "pc": 7}})
            ),
            snapshot(semantics, &[("B", 1), ("C", 2)], 7)
        );
        // A function's argument: the same short form reads at the parameter's declared type, and
        // the application is evaluated when the configuration is built.
        let call = input(semantics, &json!({"$call": {"Boot": {"regs": {"B": 1}}}}));
        let ends = configured(semantics, call);
        assert_eq!(
            semantics.end_document(&ends.ends[0]).unwrap()["cells"]["snap"],
            json!({"Cpu": {"regs": {"B": 1}, "pc": 0}})
        );
        // A key of another sort is refused at the field's position, not left undetermined.
        let refused = semantics
            .decode_input(
                "snap",
                &json!({"Cpu": {"regs": {"Q": 1}, "pc": 7}}),
                &mut NoFiles,
            )
            .unwrap_err()
            .to_string();
        assert!(
            refused.contains(".Cpu.regs") && refused.contains("no value of Reg8"),
            "{refused}"
        );
    });
}

#[test]
fn an_end_document_writes_a_constructor_field_typed_map_in_short_form_and_reads_it_back() {
    with_semantics(|semantics| {
        let snap = snapshot(semantics, &[("B", 1), ("C", 2)], 7);
        let ends = configured(semantics, snap);
        let document = semantics.end_document(&ends.ends[0]).unwrap();
        assert_eq!(
            document["cells"]["snap"],
            json!({"Cpu": {"regs": {"B": 1, "C": 2}, "pc": 7}})
        );
        assert_eq!(semantics.read_end(&document).unwrap(), ends.ends[0]);
    });
}

#[test]
fn a_difference_below_a_field_or_a_view_result_names_the_key_at_its_type() {
    with_semantics(|semantics| {
        let left_snap = snapshot(semantics, &[("B", 1), ("C", 2)], 7);
        let right_snap = snapshot(semantics, &[("B", 3), ("C", 2)], 7);
        let left = configured(semantics, left_snap);
        let right = configured(semantics, right_snap);
        let side = |name, ends| Side { name, ends };
        let differs = |compared: Compared| match compared {
            Compared::Differs(difference) => *difference,
            other => panic!("expected a difference, got {other:?}"),
        };
        // Below a constructor's field.
        let difference = differs(
            semantics
                .compare_ends(
                    &Comparison::default(),
                    side("left", &left),
                    side("right", &right),
                )
                .unwrap(),
        );
        assert_eq!(difference.path.as_deref(), Some(r#"snap.Cpu.regs["B"]"#));
        // Below a view's result, a map keyed by a constructor.
        let named = BTreeMap::from([("snap".to_owned(), "Registers".to_owned())]);
        let mut views = semantics.cell_views(semantics, &named).unwrap();
        views
            .evaluate(semantics, &[side("left", &left), side("right", &right)])
            .unwrap();
        let comparison = Comparison {
            views,
            ..Comparison::default()
        };
        let difference = differs(
            semantics
                .compare_ends(&comparison, side("left", &left), side("right", &right))
                .unwrap(),
        );
        assert_eq!(difference.path.as_deref(), Some(r#"snap["B"]"#));
        assert_eq!(difference.segments, vec![r#"["B"]"#.to_owned()]);
    });
}
