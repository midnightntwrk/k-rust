//! Narrow, explicitly provisional adapter to the current `k-rust` API.

use k_rust::{
    builtin,
    definition::{Attributes, ProductionItem, ResolvedDefinition, Sentence},
    kast::{Label, Sort, Term},
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::parser::parse_definition,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

use crate::{AnalyzedDefinition, Descriptor};

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

pub fn compile_smoke(definition: &AnalyzedDefinition) -> Result<String, String> {
    let entry = ResolvedSource::new(
        "krs://rust-hosted-entry.k",
        r#"
            module KRS-RUST-HOSTED
              syntax Bool ::= r"true" [token]
              syntax Exp ::= "seed" [symbol(seed)]
              configuration <k> seed </k>
            endmodule
        "#,
    );
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("missing source {required}"))
    };
    let options = LoadOptions {
        excluded_module_attributes: vec![
            CompilationBackend::Llvm.excluded_module_attribute().into(),
        ],
        ..LoadOptions::default()
    };
    let mut loaded = load_with_options(entry, "KRS-RUST-HOSTED", &mut resolver, &options)
        .map_err(|error| error.to_string())?;
    let module = loaded
        .definition
        .modules
        .iter_mut()
        .find(|module| module.name == "KRS-RUST-HOSTED")
        .ok_or_else(|| "prepared entry module is missing".to_owned())?;

    for registration in &definition.definition.registrations {
        match registration.descriptor {
            Descriptor::Constructor(constructor) if constructor.sort.spelling == "Expr" => {
                module.local_sentences.push(Sentence::Production {
                    label: Some(Label::new(constructor.name.to_ascii_lowercase())),
                    parameters: Vec::new(),
                    sort: Sort::new("Exp"),
                    items: vec![ProductionItem::Terminal(constructor.syntax.into())],
                    attributes: Attributes::default(),
                });
            }
            Descriptor::Rule(rule) if rule.parameter_pattern == "Foo" && rule.body == "Bar" => {
                module.local_sentences.push(Sentence::Rule {
                    body: Term::Rewrite {
                        left: Box::new(Term::apply("foo", Vec::new())),
                        right: Box::new(Term::apply("bar", Vec::new())),
                    },
                    requires: truth(),
                    ensures: truth(),
                    attributes: Attributes::default(),
                });
            }
            _ => {}
        }
    }

    loaded.resolved = ResolvedDefinition::resolve(&loaded.definition)
        .map_err(|error| error.to_string())?;
    let artifacts = compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Llvm,
            ..CompileOptions::default()
        },
    )
    .map_err(|error| error.to_string())?;
    parse_definition(&artifacts.definition_kore).map_err(|error| error.to_string())?;
    Ok(artifacts.definition_kore)
}

