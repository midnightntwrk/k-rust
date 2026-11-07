//! Guard outcomes of run coverage: an execute request that sets `collectGuards` beside
//! `collectCoverage` receives, for each rule and equation it names whose `requires` the run
//! entered, the outcomes each node of the written condition took where it was reached, the
//! entries' guard outcomes and their valuation combinations (docs/compatibility.md, "Run
//! coverage").
//!
//! The definition is `fixtures/coverage/guards.k`, compiled in-process and assembled with its
//! programs as `krun --io off` does.

use std::sync::OnceLock;

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest, GuardCollection, ResultModalityOutput},
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

struct Definition {
    kore: String,
    syntax_module: String,
    grammar: ProgramGrammar,
    variables: std::collections::BTreeMap<String, Sort>,
}

const MAIN: &str = "GUARDS";

fn guards() -> &'static Definition {
    static COMPILED: OnceLock<Definition> = OnceLock::new();
    COMPILED.get_or_init(|| {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let options = LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        };
        let (loaded, syntax_module) = load_for_compilation(
            ResolvedSource::new("guards.k", include_str!("fixtures/coverage/guards.k")),
            MAIN,
            None,
            &mut resolver,
            &options,
        )
        .unwrap();
        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
        let grammar = ProgramGrammar::new(&loaded.into_definition()).unwrap();
        Definition {
            kore: artifacts.definition_kore,
            syntax_module,
            grammar,
            variables: artifacts.configuration_variables,
        }
    })
}

impl Definition {
    fn state(&self, program: &str) -> Pattern {
        let mut assembler =
            ConfigurationAssembler::new(&self.grammar, MAIN, &self.syntax_module, &self.variables);
        assembler
            .program_file(&Sort::new("Pgm"), program, "test.pgm")
            .unwrap();
        assembler
            .bind_stream_defaults(false, false, || Ok::<_, ConfigurationError>(b"\n".to_vec()))
            .unwrap();
        assembler.finish().unwrap()
    }

    fn backend(&self) -> Backend {
        Backend::new(&self.kore, MAIN, BackendOptions::default()).unwrap()
    }

    fn id(&self, label: &str) -> String {
        let label = format!("{MAIN}.{label}");
        self.backend()
            .rule_catalog(None)
            .unwrap()
            .into_iter()
            .find(|rule| rule.label.as_deref() == Some(label.as_str()))
            .unwrap_or_else(|| panic!("no axiom {label}"))
            .id
    }

    fn run(&self, program: &str, guards: Option<GuardCollection>) -> Value {
        let mut request = ExecuteRequest::new(self.state(program));
        request.collect_coverage = true;
        request.collect_guards = guards;
        serde_json::from_str(&self.backend().execute_json(request).unwrap()).unwrap()
    }
}

/// The guard of `id` in `result`.
fn guard<'a>(result: &'a Value, id: &str) -> &'a Value {
    result["coverage"]["guards"]
        .as_array()
        .unwrap()
        .iter()
        .find(|guard| guard["axiom"] == id)
        .unwrap_or_else(|| panic!("no guard of {id}: {result:#}"))
}

/// The reached outcomes of the node at `path`.
fn reached(guard: &Value, path: &[u32]) -> Value {
    guard["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|node| node["path"] == json!(path))
        .unwrap_or_else(|| panic!("no node {path:?}: {guard:#}"))["reached"]
        .clone()
}

/// Complementary rules over `X ==Int 0 andThenBool Y ==Int 0`: on `go(1, 5)` `both` is refuted
/// by its first operand, whose `false` is the only outcome, and the second operand is not
/// reached; `notboth` holds. On `go(0, 5)` the second operand is reached and `false`.
#[test]
fn complementary_rules_report_their_operands_where_reached() {
    let definition = guards();
    let both = definition.id("both");
    let notboth = definition.id("notboth");
    let collection = || Some(GuardCollection::new([both.as_str(), notboth.as_str()]));
    let first = definition.run("go(1, 5)", collection());
    let guard_both = guard(&first, &both);
    assert_eq!(
        guard_both["outcomes"],
        json!(["refuted-false"]),
        "{first:#}"
    );
    let nodes = guard_both["nodes"].as_array().unwrap();
    assert_eq!(
        nodes[0]["shape"],
        json!({"node": "equals", "literal": true})
    );
    assert_eq!(
        nodes[1]["shape"],
        json!({"node": "connective", "connective": "andThenBool"})
    );
    assert_eq!(nodes[2]["shape"]["node"], "term");
    assert_eq!(reached(guard_both, &[0, 0, 0]), json!(["false"]));
    assert_eq!(reached(guard_both, &[0, 0, 1]), json!([]));
    assert_eq!(guard(&first, &notboth)["outcomes"], json!(["held"]));
    let combinations = guard_both["combinations"].as_array().unwrap();
    assert_eq!(combinations.len(), 1);
    assert_eq!(combinations[0]["atoms"], json!(["false", "false"]));
    assert_eq!(combinations[0]["outcome"], "refuted-false");

    let second = definition.run("go(0, 5)", collection());
    assert_eq!(reached(guard(&second, &both), &[0, 0, 0]), json!(["true"]));
    assert_eq!(reached(guard(&second, &both), &[0, 0, 1]), json!(["false"]));
}

/// The equations of a function are reported: `positive` holds or is refuted, and on `call(0)`
/// the `owise` equation `rest` is entered after it and holds. The loaded `requires` of an `owise`
/// equation is its written condition alone: that no other equation applies is its priority, not
/// a guard node.
#[test]
fn equations_are_reported_and_owise_guards_are_written_conditions() {
    let definition = guards();
    let positive = definition.id("positive");
    let rest = definition.id("rest");
    let collection = || Some(GuardCollection::new([positive.as_str(), rest.as_str()]));
    let held = definition.run("call(3)", collection());
    assert_eq!(
        guard(&held, &positive)["outcomes"],
        json!(["held"]),
        "{held:#}"
    );
    let refuted = definition.run("call(0)", collection());
    assert_eq!(
        guard(&refuted, &positive)["outcomes"],
        json!(["refuted-false"]),
        "{refuted:#}"
    );
    let rest = guard(&refuted, &rest);
    assert_eq!(rest["outcomes"], json!(["held"]), "{rest:#}");
    let shapes = rest["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|node| node["shape"]["node"].clone())
        .collect::<Vec<_>>();
    assert_eq!(shapes, [json!("equals"), json!("term")], "{rest:#}");
}

/// Off by default; asking changes no other field of the result under either modality, and two
/// runs write the same bytes. Without `collectCoverage` the request is refused; the wire form is
/// read with its defaults.
#[test]
fn guards_change_nothing_else_need_coverage_and_read_their_defaults() {
    let definition = guards();
    let every = definition
        .backend()
        .rule_catalog(None)
        .unwrap()
        .into_iter()
        .map(|rule| rule.id)
        .collect::<Vec<_>>();
    for program in ["go(1, 5)", "go(0, 0)", "call(3)", "call(0)"] {
        for modality in [
            ResultModalityOutput::StateSet,
            ResultModalityOutput::PathSet,
        ] {
            let with = |guards: Option<GuardCollection>| {
                let mut request = ExecuteRequest::new(definition.state(program));
                request.collect_coverage = true;
                request.collect_guards = guards;
                request.result_modality = modality;
                definition.backend().execute_json(request).unwrap()
            };
            let on = with(Some(GuardCollection::new(every.clone())));
            assert_eq!(
                on,
                with(Some(GuardCollection::new(every.clone()))),
                "{program}: two runs"
            );
            let mut on: Value = serde_json::from_str(&on).unwrap();
            let off: Value = serde_json::from_str(&with(None)).unwrap();
            assert!(off["coverage"].get("guards").is_none(), "{program}");
            assert!(on["coverage"]["guards"].is_array(), "{program}");
            on["coverage"].as_object_mut().unwrap().remove("guards");
            assert_eq!(on, off, "{program} {modality:?}");
        }
    }
    let mut refused = ExecuteRequest::new(definition.state("go(1, 5)"));
    refused.collect_guards = Some(GuardCollection::new(["x"]));
    let error = definition.backend().execute_kore(refused).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("collectGuards requires collectCoverage"),
        "{error}"
    );
    let read: GuardCollection = serde_json::from_value(json!({"axioms": ["a"]})).unwrap();
    assert_eq!(read, GuardCollection::new(["a"]));
    let capabilities = serde_json::to_value(definition.backend().capabilities()).unwrap();
    assert_eq!(capabilities["coverageGuards"], true);
}
