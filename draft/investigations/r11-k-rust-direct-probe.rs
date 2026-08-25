//! Probe for injecting structured KRS output into k-rust without rendering
//! user syntax or rules as `.k` text first.

use k_rust::{
    builtin,
    definition::{
        Attributes, ProductionItem, ResolvedDefinition, Sentence,
    },
    kast::{Label, Sort, Term},
    kompile::{
        CompilationBackend, CompileOptions, compile_loaded_definition,
    },
    kore::parser::parse_definition,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

fn constructor(label: &str, terminal: &str) -> Sentence {
    Sentence::Production {
        label: Some(Label::new(label)),
        parameters: Vec::new(),
        sort: Sort::new("Exp"),
        items: vec![ProductionItem::Terminal(terminal.into())],
        attributes: Attributes::default(),
    }
}

fn direct_sentences() -> Vec<Sentence> {
    vec![
        constructor("bar", "bar"),
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::apply("foo", Vec::new())),
                right: Box::new(Term::apply("bar", Vec::new())),
            },
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        },
    ]
}

fn main() {
    // k-rust does not yet expose a public `prepare_definition(Definition)`
    // entry point. Use its loader only to prepare a minimal configuration, then
    // inject the KRS constructors and rule as structured AST nodes. This probe
    // deliberately avoids the prelude so it also runs in the portable build.
    let entry = ResolvedSource::new(
        "krs://entry.k",
        r#"
            module KRS-DIRECT
              syntax Bool ::= r"true" [token]
              syntax Exp ::= "foo" [symbol(foo)]
              configuration <k> foo </k>
            endmodule
        "#,
    );
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("missing source {required}"))
    };
    let options = LoadOptions {
        excluded_module_attributes: vec![
            CompilationBackend::Llvm
                .excluded_module_attribute()
                .into(),
        ],
        ..LoadOptions::default()
    };
    let mut loaded =
        load_with_options(entry, "KRS-DIRECT", &mut resolver, &options).unwrap();
    loaded
        .definition
        .modules
        .iter_mut()
        .find(|module| module.name == "KRS-DIRECT")
        .unwrap()
        .local_sentences
        .extend(direct_sentences());
    loaded.resolved = ResolvedDefinition::resolve(&loaded.definition).unwrap();

    let artifacts = compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Llvm,
            ..CompileOptions::default()
        },
    )
    .unwrap();

    parse_definition(&artifacts.definition_kore).unwrap();
    parse_definition(&artifacts.syntax_definition_kore).unwrap();
    assert!(artifacts.definition_kore.contains("foo"));
    assert!(artifacts.definition_kore.contains("bar"));
    println!("direct structured Definition -> KORE probe passed");
}
