//! Condition records of run coverage (G-7): an execute request that sets `collectConditions`
//! beside `collectCoverage` receives, for each rule it names whose `requires` the run began to
//! decide, the bindings of the variables the condition reads and the condition's atoms with
//! their operands evaluated under the instance (docs/compatibility.md, "Run coverage").
//!
//! The definition is the fuzz crate's IMP fixture (`crates/k-rust-fuzz/tests/data/imp/imp.k`),
//! compiled in-process and assembled with its programs as `krun --io off` does.

use std::sync::OnceLock;

use k_rust::{
    backend::{Backend, BackendOptions, ConditionCollection, ExecuteRequest, ResultModalityOutput},
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ConfigurationError,
        ProgramGrammar, compile_loaded_definition,
    },
    kore::ast::Pattern,
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};
use serde_json::{Value, json};

const IMP: &str = include_str!("../../k-rust-fuzz/tests/data/imp/imp.k");

struct Imp {
    kore: String,
    syntax_module: String,
    grammar: ProgramGrammar,
    variables: std::collections::BTreeMap<String, Sort>,
}

/// The IMP fixture compiled once per test binary.
fn imp() -> &'static Imp {
    static IMP_COMPILED: OnceLock<Imp> = OnceLock::new();
    IMP_COMPILED.get_or_init(|| {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let options = LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        };
        let (loaded, syntax_module) = load_for_compilation(
            ResolvedSource::new("imp.k", IMP),
            "IMP",
            None,
            &mut resolver,
            &options,
        )
        .unwrap();
        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
        let grammar = ProgramGrammar::new(&loaded.into_definition()).unwrap();
        Imp {
            kore: artifacts.definition_kore,
            syntax_module,
            grammar,
            variables: artifacts.configuration_variables,
        }
    })
}

/// The initial configuration of `program`.
fn state(program: &str) -> Pattern {
    let imp = imp();
    let mut assembler =
        ConfigurationAssembler::new(&imp.grammar, "IMP", &imp.syntax_module, &imp.variables);
    assembler
        .program_file(&Sort::new("Pgm"), program, "test.imp")
        .unwrap();
    assembler
        .bind_stream_defaults(false, false, || Ok::<_, ConfigurationError>(b"\n".to_vec()))
        .unwrap();
    assembler.finish().unwrap()
}

fn backend() -> Backend {
    Backend::new(&imp().kore, "IMP", BackendOptions::default()).unwrap()
}

/// The id of the division rule, `I1 / I2 => I1 /Int I2 requires I2 =/=Int 0` (imp.k:57), which
/// has no label: the one rule whose condition, recorded for every rule of the catalog on a
/// division, holds an `INT.ne` atom.
fn division_rule() -> String {
    let every = backend()
        .rule_catalog(None)
        .unwrap()
        .into_iter()
        .map(|rule| rule.id)
        .collect::<Vec<_>>();
    let result = run(request(
        "int x, y, q; x = 10; y = 2; q = x / y;",
        Some(ConditionCollection::new(every)),
    ));
    let ids = result["coverage"]["conditions"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|rule| {
            rule["records"].as_array().unwrap().iter().any(|record| {
                record["condition"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|node| node["atom"]["hook"] == "INT.ne")
            })
        })
        .map(|rule| rule["rule"].as_str().unwrap().to_owned())
        .collect::<Vec<_>>();
    let [id] = &ids[..] else {
        panic!("rules with an INT.ne atom: {ids:?}")
    };
    id.clone()
}

fn request(program: &str, conditions: Option<ConditionCollection>) -> ExecuteRequest {
    let mut request = ExecuteRequest::new(state(program));
    request.collect_coverage = true;
    request.collect_conditions = conditions;
    request
}

/// The wire output of `request` on a fresh backend.
fn run(request: ExecuteRequest) -> Value {
    serde_json::from_str(&backend().execute_json(request).unwrap()).unwrap()
}

/// A KORE term as the wire writes one, in its envelope.
fn kore(term: Value) -> Value {
    json!({"format": "KORE", "version": 1, "term": term})
}

fn int(value: i64) -> Value {
    kore(json!({
        "tag": "DV",
        "sort": {"tag": "SortApp", "name": "SortInt", "args": []},
        "value": value.to_string(),
    }))
}

/// The records of rule `id` in a wire result.
fn records<'a>(result: &'a Value, id: &str) -> &'a Value {
    let conditions = result["coverage"]["conditions"]
        .as_array()
        .expect("the result has condition records");
    let rule = conditions
        .iter()
        .find(|rule| rule["rule"] == id)
        .unwrap_or_else(|| panic!("no records of {id}: {conditions:?}"));
    &rule["records"]
}

/// A division by zero blocks the division rule: its entry is recorded with the binding of the
/// divisor, the one variable the condition reads, and the failing atom `I2 =/=Int 0` with both
/// operands 0 and its truth false.
#[test]
fn a_blocked_imp_rule_reports_its_bindings_and_failing_operands() {
    let id = division_rule();
    let result = run(request(
        "int x, y, q; x = 10; y = 0; q = x / y;",
        Some(ConditionCollection::new([id.as_str()])),
    ));
    assert!(
        !result["coverage"]["applied"]
            .as_array()
            .unwrap()
            .contains(&json!(id)),
        "the division never applies"
    );
    let variable = kore(json!({
        "tag": "EVar",
        "name": "VarI2",
        "sort": {"tag": "SortApp", "name": "SortInt", "args": []},
    }));
    assert_eq!(
        records(&result, &id),
        &json!([{
            "bindings": [{"variable": variable, "value": {"kind": "value", "term": int(0)}}],
            "condition": [{"atom": {
                "head": "Lbl'UndsEqlsSlshEqls'Int'Unds'",
                "hook": "INT.ne",
                "operands": [
                    {"kind": "value", "term": int(0)},
                    {"kind": "value", "term": int(0)},
                ],
                "reads": [0],
                "value": false,
            }}],
        }])
    );
}

/// A negated atom keeps its connective: `notBool (X in keys(STATE))` of the `decl` rule, entered
/// for a second declaration of `x`, is recorded as `not` around the membership atom, whose
/// operands are the identifier and the evaluated key set, and which holds. The rule is named by
/// its label.
#[test]
fn a_negated_atom_is_recorded_under_its_connective() {
    let result = run(request(
        "int x, x; x = 1;",
        Some(ConditionCollection::new(["IMP.decl"])),
    ));
    let conditions = result["coverage"]["conditions"].as_array().unwrap();
    let [rule] = &conditions[..] else {
        panic!("{conditions:?}")
    };
    let records = rule["records"].as_array().unwrap();
    let blocked = records
        .iter()
        .find(|record| record["condition"][0]["not"]["atom"]["value"] == json!(true))
        .unwrap_or_else(|| panic!("no entry where x is declared: {records:?}"));
    let atom = &blocked["condition"][0]["not"]["atom"];
    assert_eq!(atom["hook"], "SET.in", "{atom}");
    let operands = atom["operands"].as_array().unwrap();
    assert_eq!(operands.len(), 2, "{atom}");
    assert!(
        operands.iter().all(|operand| operand["kind"] == "value"),
        "{atom}"
    );
}

/// The records are the first `limit` distinct entries in the run's order, and a rule with more
/// distinct entries is marked truncated; equal entries are recorded once.
#[test]
fn the_limit_keeps_the_first_distinct_entries() {
    let id = division_rule();
    let program = "int n, q; n = 4; while (0 < n) { q = 12 / n; q = 12 / n; n = n - 1; }";
    let divisors = |result: &Value| {
        records(result, &id)
            .as_array()
            .unwrap()
            .iter()
            .map(|record| record["bindings"][0]["value"]["term"]["term"]["value"].clone())
            .collect::<Vec<_>>()
    };
    let truncated = |result: &Value| {
        result["coverage"]["conditions"][0]
            .get("truncated")
            .cloned()
    };
    let all = run(request(
        program,
        Some(ConditionCollection::new([id.as_str()])),
    ));
    assert_eq!(divisors(&all), ["4", "3", "2", "1"]);
    assert_eq!(truncated(&all), None);
    let mut first_two = ConditionCollection::new([id.as_str()]);
    first_two.limit = 2;
    let limited = run(request(program, Some(first_two)));
    assert_eq!(divisors(&limited), ["4", "3"]);
    assert_eq!(truncated(&limited), Some(json!(true)));
}

/// Off by default: without `collectConditions` the coverage has no `conditions` key, and asking
/// for records changes no other field of the result, under either modality; two runs on fresh
/// backends write the same bytes.
#[test]
fn records_change_nothing_else_and_are_deterministic() {
    let id = division_rule();
    let decl = "IMP.decl".to_owned();
    for program in [
        "int x, y, q; x = 10; y = 0; q = x / y;",
        "int n, q; n = 4; while (0 < n) { q = 12 / n; n = n - 1; }",
        "int x, x; x = 1;",
    ] {
        for modality in [
            ResultModalityOutput::StateSet,
            ResultModalityOutput::PathSet,
        ] {
            let with = |conditions: Option<ConditionCollection>| {
                let mut request = request(program, conditions);
                request.result_modality = modality;
                backend().execute_json(request).unwrap()
            };
            let collection = || Some(ConditionCollection::new([id.clone(), decl.clone()]));
            let on = with(collection());
            assert_eq!(on, with(collection()), "{program}: two runs");
            let off = with(None);
            let mut on: Value = serde_json::from_str(&on).unwrap();
            let off: Value = serde_json::from_str(&off).unwrap();
            assert!(off["coverage"].get("conditions").is_none(), "{program}");
            assert!(
                on["coverage"]["conditions"].is_array(),
                "{program}: records asked for"
            );
            on["coverage"].as_object_mut().unwrap().remove("conditions");
            assert_eq!(on, off, "{program} {modality:?}");
        }
    }
}

/// `collectConditions` is part of the run's coverage: without `collectCoverage` the request is
/// refused, and the wire form is read with its defaults.
#[test]
fn conditions_need_coverage_and_are_read_from_the_wire() {
    let mut refused = ExecuteRequest::new(state("int x; x = 1;"));
    refused.collect_conditions = Some(ConditionCollection::new(["IMP.decl"]));
    let error = backend().execute(refused).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("collectConditions requires collectCoverage"),
        "{error}"
    );
    let state = k_rust::kore::codec::to_value(&state("int x; x = 1;")).unwrap();
    let request: ExecuteRequest = serde_json::from_value(json!({
        "state": state,
        "collectCoverage": true,
        "collectConditions": {"rules": ["IMP.decl"]},
    }))
    .unwrap();
    let conditions = request.collect_conditions.clone().unwrap();
    assert_eq!(conditions, ConditionCollection::new(["IMP.decl"]));
    let result = run(request);
    let bindings = &result["coverage"]["conditions"][0]["records"][0]["bindings"];
    assert_eq!(
        bindings.as_array().unwrap().len(),
        2,
        "X and STATE: {result}"
    );
}
