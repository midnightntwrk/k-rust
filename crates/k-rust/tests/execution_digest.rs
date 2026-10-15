//! The contract of `k_rust::backend::execution_digest`: definitions with equal digests execute
//! alike through `Backend::new`, `from_definition` and `internalize_definition`, except in values
//! derived from rule origins; layout and the resolver identity do not move the digest, rule
//! order does, and the source route's `execution_rewrite_order` is outside it.

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionDigest, ExecutionStrategy,
        ResultModalityOutput, execution_digest,
    },
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, CompiledKoreArtifacts, ConfigurationAssembler,
        ProgramGrammar, compile_loaded_definition,
    },
    kore::{
        ast::{Pattern, Sentence},
        parser::parse_definition,
        printer::Printer,
    },
    names::KoreAttribute,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use serde_json::Value;

/// Two rewrite rules of one priority on one subject, and two overlapping equations of one
/// priority, in the order `first`, `second`, `third`, `fourth` gives them.
fn source(rules: [&str; 4]) -> String {
    let [first, second, third, fourth] = rules;
    format!(
        r#"
module DIG
  imports INT
  syntax Exp ::= "go" | "left" | "right" | "calc" | val(Int)
  syntax Int ::= f(Int) [function]
  configuration <k> $PGM:Exp </k>
  {first}
  {second}
  {third}
  {fourth}
  rule <k> calc => val(f(0)) </k>
endmodule
"#
    )
}

const LEFT: &str = "rule <k> go => left </k>";
const RIGHT: &str = "rule <k> go => right </k>";
const ANY_ONE: &str = "rule f(_) => 1";
const ZERO_TWO: &str = "rule f(0) => 2";

struct Compiled {
    artifacts: CompiledKoreArtifacts,
    grammar: ProgramGrammar,
}

fn compile(path: &str, text: &str) -> Compiled {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new(path, text),
        "DIG",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let grammar = ProgramGrammar::new(&loaded.into_definition()).unwrap();
    Compiled { artifacts, grammar }
}

impl Compiled {
    fn digest(&self) -> ExecutionDigest {
        let digest =
            execution_digest(&parse_definition(&self.artifacts.definition_kore).unwrap()).unwrap();
        assert_eq!(self.artifacts.execution_digest(), Ok(digest));
        digest
    }

    fn initial(&self, program: &str) -> Pattern {
        let mut assembler = ConfigurationAssembler::new(
            &self.grammar,
            "DIG",
            "DIG",
            &self.artifacts.configuration_variables,
        );
        assembler.program(&Sort::new("Exp"), program).unwrap();
        assembler.finish().unwrap()
    }

    /// The results of `program` under `any` and under `all` in both modalities, as JSON, with
    /// the values derived from rule origins removed.
    fn results(&self, backend: &mut Backend, program: &str) -> Vec<Value> {
        let initial = self.initial(program);
        let mut results = Vec::new();
        for (strategy, modality) in [
            (ExecutionStrategy::Any, ResultModalityOutput::StateSet),
            (ExecutionStrategy::All, ResultModalityOutput::StateSet),
            (ExecutionStrategy::All, ResultModalityOutput::PathSet),
        ] {
            let result = backend
                .execute(ExecuteRequest {
                    strategy,
                    result_modality: modality,
                    max_depth: Some(10),
                    ..ExecuteRequest::new(initial.clone())
                })
                .unwrap();
            let mut value = serde_json::to_value(&result).unwrap();
            without_origins(&mut value);
            results.push(value);
        }
        results
    }
}

/// Remove the values derived from rule origins: diagnostics, leaf `detail` texts and
/// `contradictedTotal.origin`.
fn without_origins(value: &mut Value) {
    match value {
        Value::Object(object) => {
            object.remove("diagnostics");
            object.remove("detail");
            if let Some(Value::Object(contradicted)) = object.get_mut("contradictedTotal") {
                contradicted.remove("origin");
            }
            object.values_mut().for_each(without_origins);
        }
        Value::Array(items) => items.iter_mut().for_each(without_origins),
        _ => {}
    }
}

/// Layout and the resolver identity change only origins: equal digests and equal results. Rule
/// order is read, so swapping two rules of one priority changes both.
#[test]
fn equal_digests_execute_alike_and_rule_order_is_kept() {
    let text = source([LEFT, RIGHT, ANY_ONE, ZERO_TWO]);
    let base = compile("dig.k", &text);
    let shifted = compile(
        "/elsewhere/checkout/dig.k",
        &format!(
            "\n\n// moved\n{}",
            text.replacen("  rule <k> go", "\n\n  rule <k> go", 1)
        ),
    );
    assert_ne!(
        base.artifacts.definition_kore,
        shifted.artifacts.definition_kore
    );
    assert_eq!(base.digest(), shifted.digest());
    let mut left = Backend::new(
        &base.artifacts.definition_kore,
        "DIG",
        BackendOptions::default(),
    )
    .unwrap();
    let mut right = Backend::from_definition(
        parse_definition(&shifted.artifacts.definition_kore).unwrap(),
        "DIG",
        BackendOptions::default(),
    )
    .unwrap();
    for program in ["go", "calc"] {
        assert_eq!(
            base.results(&mut left, program),
            shifted.results(&mut right, program),
            "{program}"
        );
    }
    // The internalizing route gives the same results too.
    let mut internalized = Backend::from_internalized(
        Backend::internalize_definition(
            &parse_definition(&shifted.artifacts.definition_kore).unwrap(),
            "DIG",
        )
        .unwrap(),
        BackendOptions::default(),
    )
    .unwrap();
    assert_eq!(
        base.results(&mut left, "go"),
        shifted.results(&mut internalized, "go")
    );

    let swapped = compile("dig.k", &source([RIGHT, LEFT, ZERO_TWO, ANY_ONE]));
    assert_ne!(base.digest(), swapped.digest());
    let mut swapped_backend = Backend::new(
        &swapped.artifacts.definition_kore,
        "DIG",
        BackendOptions::default(),
    )
    .unwrap();
    let any = |results: Vec<Value>| results.into_iter().next().unwrap();
    assert_ne!(
        any(base.results(&mut left, "go")),
        any(swapped.results(&mut swapped_backend, "go"))
    );
}

/// Every compiled definition has a digest, which means its print parses back to it without
/// its origins, and the facade method agrees with the function.
#[test]
fn compiled_definitions_have_a_digest() {
    for rules in [
        [LEFT, RIGHT, ANY_ONE, ZERO_TWO],
        [RIGHT, LEFT, ZERO_TWO, ANY_ONE],
    ] {
        let compiled = compile("dig.k", &source(rules));
        let digest = compiled.digest();
        assert_eq!(digest.to_string().parse::<ExecutionDigest>(), Ok(digest));
    }
}

/// The UNIQUE_ID of the rewrite axiom whose right-hand side prints `name`.
fn rewrite_id(definition_kore: &str, name: &str) -> String {
    let definition = parse_definition(definition_kore).unwrap();
    let ids = definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            Sentence::Axiom {
                pattern,
                attributes,
                ..
            } if {
                let printed = Printer::compact().print_pattern(pattern);
                printed.starts_with("\\rewrites") && printed.contains(name)
            } =>
            {
                attributes
                    .string(KoreAttribute::UniqueId)
                    .unwrap()
                    .map(str::to_owned)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(ids.len(), 1, "{name}: {ids:?}");
    ids.into_iter().next().unwrap()
}

/// On the source route, `execution_rewrite_order` reorders the rewrites of a priority: one
/// definition, so one digest, runs differently under two orders. The digest does not cover that
/// route without the order.
#[test]
fn the_source_route_also_reads_the_rewrite_order() {
    let compiled = compile("dig.k", &source([LEFT, RIGHT, ANY_ONE, ZERO_TWO]));
    let kore = &compiled.artifacts.definition_kore;
    let syntax = parse_definition(kore).unwrap();
    let left = rewrite_id(kore, "Lblleft");
    let right = rewrite_id(kore, "Lblright");
    let order = compiled.artifacts.execution_rewrite_order.clone();
    let swapped = order
        .iter()
        .map(|id| {
            if *id == left {
                right.clone()
            } else if *id == right {
                left.clone()
            } else {
                id.clone()
            }
        })
        .collect::<Vec<_>>();
    assert_ne!(order, swapped);
    let mut results = Vec::new();
    for order in [order, swapped] {
        let definition = Backend::internalize_source_definition(&syntax, "DIG", &order).unwrap();
        assert_eq!(execution_digest(&syntax), Ok(compiled.digest()));
        let mut backend =
            Backend::from_internalized(definition, BackendOptions::default()).unwrap();
        results.push(compiled.results(&mut backend, "go").remove(0));
    }
    assert_ne!(results[0], results[1]);
}
