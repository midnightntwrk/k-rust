//! Bindings of run coverage: an execute request that sets `collectBindings` beside
//! `collectCoverage` receives, per rule and equation, the named symbols that were the head of an
//! operand of a fired instance, and the values of the template binders it selects
//! (docs/compatibility.md, "Run coverage").
//!
//! The definition is `fixtures/coverage/bindings.k`, compiled in-process and assembled with its
//! programs as `krun --io off` does. No request sets a step timeout, and every run ends by
//! itself, so none depends on a clock.

use std::sync::OnceLock;

use k_rust::{
    backend::{
        Backend, BackendOptions, BinderSelection, BindingCollection, ExecuteRequest,
        ResultModalityOutput,
    },
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

const MAIN: &str = "BINDINGS";

/// The program every test runs: `big` is entered and refuted on `inc(5)` and fires on
/// `inc(200)`; `decode` fires on `op(3)`, `op(9)` and `op(1)`.
const PROGRAM: &str = "inc(5) ; op(3) ; op(9) ; op(1) ; inc(200)";

fn bindings() -> &'static Definition {
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
            ResolvedSource::new("bindings.k", include_str!("fixtures/coverage/bindings.k")),
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

    fn request(
        &self,
        bindings: Option<BindingCollection>,
        modality: ResultModalityOutput,
    ) -> ExecuteRequest {
        let mut request = ExecuteRequest::new(self.state(PROGRAM));
        request.collect_coverage = true;
        request.collect_bindings = bindings;
        request.result_modality = modality;
        request
    }

    fn run(&self, bindings: Option<BindingCollection>, modality: ResultModalityOutput) -> String {
        self.backend()
            .execute_json(self.request(bindings, modality))
            .unwrap()
    }
}

/// The instruction symbols and the sequencing symbol, and the binders of `big` and `decode`.
fn collection(definition: &Definition) -> BindingCollection {
    BindingCollection {
        binders: vec![
            BinderSelection {
                axiom: definition.id("big"),
                variable: "VarN".to_owned(),
                cap: 4,
            },
            BinderSelection {
                axiom: definition.id("decode"),
                variable: "VarB".to_owned(),
                cap: 2,
            },
        ],
        ..BindingCollection::new(["Lblinc", "Lblop", "Lblseq"])
    }
}

/// `split` takes each instruction and the rest of the program as operands, through their
/// injections; `small`, `big` and `decode` take integers and a continuation, and record no head.
/// (A function equation the compiler generates, with no source, takes the program as an operand
/// too and records its head under its own id.)
/// `big`'s binder holds only the value of the instance that fired (200, not the refuted 5), and
/// `decode`'s the least two of 1, 3 and 9, truncated.
#[test]
fn bindings_record_operand_heads_and_binder_values_of_fired_instances() {
    let definition = bindings();
    let result: Value = serde_json::from_str(
        &definition.run(Some(collection(definition)), ResultModalityOutput::PathSet),
    )
    .unwrap();
    let bindings = &result["coverage"]["bindings"];
    let operands = |axiom: &str| {
        bindings["operands"]
            .as_array()
            .unwrap()
            .iter()
            .find(|operands| operands["axiom"] == axiom)
            .map(|operands| operands["symbols"].clone())
    };
    assert_eq!(
        operands(&definition.id("split")),
        Some(json!(["Lblinc", "Lblop", "Lblseq"])),
        "{result:#}"
    );
    for label in ["small", "big", "decode"] {
        assert_eq!(operands(&definition.id(label)), None, "{label}: {result:#}");
    }
    let mut expected = vec![
        json!({"axiom": definition.id("big"), "variable": "VarN", "values": ["200"]}),
        json!({
            "axiom": definition.id("decode"),
            "variable": "VarB",
            "values": ["1", "3"],
            "truncated": true
        }),
    ];
    expected.sort_by_key(|binder| binder["axiom"].as_str().unwrap().to_owned());
    assert_eq!(bindings["binders"], json!(expected), "{result:#}");
    assert!(
        result["coverage"]["matched"]
            .as_array()
            .unwrap()
            .contains(&json!(definition.id("big"))),
        "{result:#}"
    );
}

/// Off by default; asking changes no other field of the result under either modality, and two
/// runs write the same bytes. Without `collectCoverage`, or with a binder selected twice (under
/// one name, or under its axiom's `UNIQUE_ID` and its label), the request is refused; the wire form is read with its defaults, and the capability is
/// advertised.
#[test]
fn bindings_change_nothing_else_need_coverage_and_select_a_binder_once() {
    let definition = bindings();
    for modality in [
        ResultModalityOutput::StateSet,
        ResultModalityOutput::PathSet,
    ] {
        let on = definition.run(Some(collection(definition)), modality);
        assert_eq!(
            on,
            definition.run(Some(collection(definition)), modality),
            "two runs"
        );
        let mut on: Value = serde_json::from_str(&on).unwrap();
        let off: Value = serde_json::from_str(&definition.run(None, modality)).unwrap();
        assert!(off["coverage"].get("bindings").is_none(), "{off:#}");
        assert!(on["coverage"]["bindings"].is_object(), "{on:#}");
        on["coverage"].as_object_mut().unwrap().remove("bindings");
        assert_eq!(on, off, "{modality:?}");
    }
    let mut uncovered = definition.request(
        Some(BindingCollection::new(["Lblinc"])),
        ResultModalityOutput::PathSet,
    );
    uncovered.collect_coverage = false;
    let error = definition.backend().execute_kore(uncovered).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("collectBindings requires collectCoverage"),
        "{error}"
    );
    let mut twice = collection(definition);
    twice.binders.push(BinderSelection {
        axiom: definition.id("decode"),
        variable: "VarB".to_owned(),
        cap: 7,
    });
    let error = definition
        .backend()
        .execute_kore(definition.request(Some(twice), ResultModalityOutput::PathSet))
        .unwrap_err();
    assert!(error.to_string().contains("twice"), "{error}");
    let mut by_label = collection(definition);
    by_label.binders.push(BinderSelection {
        axiom: format!("{MAIN}.decode"),
        variable: "VarB".to_owned(),
        cap: 7,
    });
    let error = definition
        .backend()
        .execute_kore(definition.request(Some(by_label), ResultModalityOutput::PathSet))
        .unwrap_err();
    assert!(error.to_string().contains("twice"), "{error}");
    let read: BindingCollection = serde_json::from_value(json!({"symbols": ["a"]})).unwrap();
    assert_eq!(read, BindingCollection::new(["a"]));
    let capabilities = serde_json::to_value(definition.backend().capabilities()).unwrap();
    assert_eq!(capabilities["coverageBindings"], true);
}
