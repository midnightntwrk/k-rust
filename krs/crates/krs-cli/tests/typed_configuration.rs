//! `krs-exec` checks the values configuration variables give typed collection cells: a variable
//! that fills a `Map<Id, Value>` cell must hold `Id` keys and `Value` values, in the definition's
//! sort lattice, recursively through nested collections, whether it is given as text
//! (`krs run -c NAME=TEXT`) or as a value.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use krs_exec::{
    CompiledStage, ConfigInputs, ConfigValue, ElementSortMismatch, ExecError, Semantics, Value,
};
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const FIXTURE: &str = r#"
use k::builtin::{Id, Int, KSequence, List, Map, Set, set};
use k::{KResult, Term};

k::sorts! {
    Stmt;
    Value: KResult;
    Ptr: Value;
    impl Value for Int;
}

/// `forget x` makes identifiers part of the grammar.
#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Skip, Forget))]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("forget {name}")]
    Forget { name: Id },
}

#[k::constructors(sort = Ptr, result = KResult)]
#[k::precedence((At))]
pub enum PtrSyntax {
    #[k::syntax("ptr({n})")]
    At { n: Int },
}

/// A set the configuration leaves unevaluated: its elements are not seen.
#[k::function(total, sort = Set, syntax = "evens({n})")]
pub struct Evens {
    pub n: Term<Int>,
}

#[k::equation]
fn evens(k::term![Evens(n)]: Term<Set>) -> Term<Set> {
    set::item(n * 2)
}

/// A statement the configuration leaves unevaluated: its result sort is still a Stmt.
#[k::function(total, sort = Stmt, syntax = "noop({n})")]
pub struct Noop {
    pub n: Term<Int>,
}

#[k::equation]
fn noop(k::term![Noop(_)]: Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Skip()
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub locals: Map<Id, Int>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Value>,
    #[k::cell]
    pub stack: List<Value>,
    #[k::cell]
    pub nested: Map<Id, Set<Int>>,
    #[k::cell]
    pub raw: Map,
    #[k::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "ENV")] env: Map<Id, Value>,
        #[k::config_var(name = "STACK")] stack: List<Value>,
        #[k::config_var(name = "NESTED")] nested: Map<Id, Set<Int>>,
        #[k::config_var(name = "RAW")] raw: Map,
        #[k::config_var(name = "LOCALS")] locals: Map<Id, Int>,
    ) -> Self {
        Self {
            k: k::k![],
            env,
            stack,
            nested,
            raw,
            frame: Frame { locals },
        }
    }
}
"#;
const PACKAGE: &str = "krs-typed-configuration-fixture";

fn materialize(temporary: &Path) -> PathBuf {
    let project = temporary.join("language");
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
            "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-TYPED-CONFIGURATION\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
        ),
    )
    .unwrap();
    project.join("Cargo.toml")
}

/// The fixture's Definition IR and compiled stage, built once per test process.
fn compiled() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| {
        let target = shared_fixture_target();
        let temporary = temp_dir();
        let manifest = materialize(temporary.path());
        let emitted = temporary.path().join("emitted");
        let mut process = krs_command!();
        fixture_build_env(&mut process, target.path());
        let output = process
            .current_dir(manifest.parent().unwrap())
            .arg("emit-k")
            .args(["--manifest-path"])
            .arg(&manifest)
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
            serde_json::from_slice(&fs::read(emitted.join("definition-ir.json")).unwrap()).unwrap();
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

/// Values that fit every typed cell, as text.
const FITTING: [(&str, &str); 5] = [
    ("ENV", "x |-> 1"),
    ("STACK", "ListItem(1)"),
    ("NESTED", "x |-> SetItem(1)"),
    ("RAW", "x |-> skip"),
    ("LOCALS", "x |-> 1"),
];

/// Configure with the fitting texts, `variable` replaced by `value`.
fn configure_with(
    semantics: &mut Semantics,
    variable: &str,
    value: ConfigValue,
) -> Result<krs_exec::State, ExecError> {
    let mut variables = FITTING
        .iter()
        .map(|(name, text)| ((*name).to_owned(), ConfigValue::from(*text)))
        .collect::<Vec<_>>();
    let slot = variables
        .iter_mut()
        .find(|(name, _)| name == variable)
        .expect("a fixture variable");
    slot.1 = value;
    semantics.configure(&ConfigInputs {
        variables,
        ..ConfigInputs::default()
    })
}

fn mismatch(semantics: &mut Semantics, variable: &str, text: &str) -> ElementSortMismatch {
    match configure_with(semantics, variable, text.into()) {
        Err(ExecError::CollectionElementSort(mismatch)) => *mismatch,
        other => panic!("`{variable}={text}` is not rejected for its element sort: {other:?}"),
    }
}

#[test]
fn a_statement_stored_in_a_map_of_values_is_rejected_and_a_value_is_accepted() {
    with_semantics(|semantics| {
        let rejected = mismatch(semantics, "ENV", "x |-> skip");
        assert_eq!(
            rejected,
            ElementSortMismatch {
                variable: "ENV".to_owned(),
                cell: "env".to_owned(),
                declared: "Map<Id, Value>".to_owned(),
                position: "the value at key `x`".to_owned(),
                element: "skip".to_owned(),
                sort: "Stmt".to_owned(),
                expected: "Value".to_owned(),
            }
        );
        assert_eq!(
            ExecError::CollectionElementSort(Box::new(rejected)).to_string(),
            "configuration variable `$ENV`: the cell `env` is declared `Map<Id, Value>`, but the value at key `x` is `skip` of sort Stmt, which is not a subsort of Value"
        );
        configure_with(semantics, "ENV", "x |-> 1".into()).unwrap();
        // An untyped cell takes any element.
        configure_with(semantics, "RAW", "x |-> skip y |-> 1".into()).unwrap();
        // A key is checked too.
        let key = mismatch(semantics, "ENV", "5 |-> 1");
        assert_eq!(
            (
                key.position.as_str(),
                key.element.as_str(),
                key.sort.as_str()
            ),
            ("a key", "5", "Int")
        );
    });
}

#[test]
fn an_element_of_a_subsort_is_accepted() {
    with_semantics(|semantics| {
        // `Int` and `Ptr` are both declared subsorts of `Value`.
        configure_with(semantics, "ENV", "x |-> 1 y |-> ptr(2)".into()).unwrap();
        configure_with(semantics, "STACK", "ListItem(ptr(1)) ListItem(3)".into()).unwrap();
        let rejected = mismatch(semantics, "STACK", "ListItem(1) ListItem(skip)");
        assert_eq!(rejected.position, "the element at index 1");
        assert_eq!(rejected.declared, "List<Value>");
    });
}

#[test]
fn nested_collections_are_checked_against_their_own_element_types() {
    with_semantics(|semantics| {
        configure_with(semantics, "NESTED", "x |-> SetItem(1) SetItem(2)".into()).unwrap();
        let rejected = mismatch(semantics, "NESTED", "x |-> SetItem(skip)");
        assert_eq!(rejected.declared, "Map<Id, Set<Int>>");
        assert_eq!(rejected.position, "an element of the value at key `x`");
        assert_eq!(
            (rejected.element.as_str(), rejected.sort.as_str()),
            ("skip", "Stmt")
        );
        // A typed cell inside a group cell is checked as well.
        let rejected = mismatch(semantics, "LOCALS", "x |-> ptr(1)");
        assert_eq!(
            (
                rejected.cell.as_str(),
                rejected.declared.as_str(),
                rejected.sort.as_str()
            ),
            ("locals", "Map<Id, Int>", "Ptr")
        );
    });
}

#[test]
fn an_unevaluated_part_is_checked_only_at_its_declared_sort() {
    with_semantics(|semantics| {
        // The elements of a set a function computes are not seen.
        configure_with(semantics, "NESTED", "x |-> evens(1)".into()).unwrap();
        // A function application has its result sort, which is no Value here.
        let rejected = mismatch(semantics, "ENV", "x |-> noop(1)");
        assert_eq!(
            (rejected.element.as_str(), rejected.sort.as_str()),
            ("noop ( 1 )", "Stmt")
        );
    });
}

#[test]
fn a_value_is_checked_as_text_is() {
    with_semantics(|semantics| {
        let index = semantics.values();
        let x = Value::Token {
            sort: index.sort("Id").unwrap(),
            text: "x".to_owned(),
        };
        let skip = index.ctor("StmtSyntax::Skip", []).unwrap();
        let at = index.ctor("PtrSyntax::At", [("n", 1.into())]).unwrap();
        configure_with(semantics, "ENV", Value::map([(x.clone(), at)]).into()).unwrap();
        let Err(ExecError::CollectionElementSort(rejected)) =
            configure_with(semantics, "ENV", Value::map([(x, skip)]).into())
        else {
            panic!("a statement value is accepted in a map of values");
        };
        assert_eq!(
            (rejected.element.as_str(), rejected.sort.as_str()),
            ("skip", "Stmt")
        );
    });
}

#[test]
fn krs_run_rejects_a_configuration_variable_that_breaks_its_cell_type() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = materialize(temporary.path());
    let run = |env: &str| {
        let mut process = krs_command!();
        fixture_build_env(&mut process, target.path());
        process
            .current_dir(manifest.parent().unwrap())
            .arg("run")
            .args(["--manifest-path"])
            .arg(&manifest)
            .args(["--package", PACKAGE, "--definition", "main"])
            .args(["-c", &format!("ENV={env}")]);
        for (name, text) in &FITTING[1..] {
            process.args(["-c", &format!("{name}={text}")]);
        }
        process.output().unwrap()
    };
    let rejected = run("x |-> skip");
    let stderr = String::from_utf8_lossy(&rejected.stderr);
    assert_ne!(rejected.status.code(), Some(0), "{stderr}");
    assert!(
        stderr.contains("krs::exec::collection-element-sort")
            && stderr.contains(
                "the cell `env` is declared `Map<Id, Value>`, but the value at key `x` is `skip` of sort Stmt, which is not a subsort of Value"
            ),
        "{stderr}"
    );
    let accepted = run("x |-> 1");
    assert_eq!(
        accepted.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&accepted.stderr)
    );
}
