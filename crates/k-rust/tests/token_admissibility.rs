use std::{collections::BTreeMap, sync::Arc};

use k_rust::{
    builtin::embedded,
    definition::{Attributes, Definition, FlatModule, ResolvedDefinition, Sentence, SortCatalog},
    diagnostic::DiagnosticCode,
    kast::{Sort, Term},
    kompile::{
        CompilationBackend, CompileError, CompileOptions, TermConversionError, TermConverter,
        compile_loaded_definition,
    },
    outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation, load_structured},
};
use serde_json::json;

#[test]
fn declared_domain_sorts_include_hooked_and_parametric_instances() {
    let parameter = Sort::new("T");
    let parametric = Sort::with_parameters("Boxed", vec![parameter.clone()]);
    let declarations = [
        Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("Hooked"),
            attributes: Attributes::new(BTreeMap::from([("hook".into(), json!("CUSTOM.Value"))])),
        },
        Sentence::SyntaxSort {
            parameters: vec![parameter],
            sort: parametric,
            attributes: Attributes::new(BTreeMap::from([("token".into(), json!(""))])),
        },
        Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("Nat"),
            attributes: Attributes::default(),
        },
    ];
    let catalog = SortCatalog::from_visible(declarations.iter());
    assert!(catalog.admits_domain_value(&Sort::new("Hooked")));
    assert!(catalog.admits_domain_value(&Sort::new("Bool")));
    assert!(catalog.admits_domain_value(&Sort::new("KConfigVar")));
    assert!(catalog.admits_domain_value(&Sort::with_parameters("Boxed", vec![Sort::new("Int")],)));
    assert!(!catalog.admits_domain_value(&Sort::new("Nat")));
}

#[test]
fn emission_rejects_an_undeclared_domain_value() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![Arc::new(Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::new("Nat"),
                attributes: Attributes::default(),
            })],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    };
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let error = TermConverter::new(&resolved, "MAIN")
        .unwrap()
        .convert(&token("7", "Nat"))
        .unwrap_err();
    assert!(matches!(error, TermConversionError::InvalidToken { .. }));
}

const SOURCE: &str = r#"
module MAIN
  imports BASIC-K
  imports INT-SYNTAX
  imports SORT-BOOL
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Name ::= r"[a-z]+" [token]
  syntax Counter ::= counter(Nat, Nat) [symbol(counter)]
                   | integer(Int) [symbol(integer)]
                   | named(Name) [symbol(named)]
  rule counter(z, z) => counter(z, z)
endmodule
"#;

fn options(backend: CompilationBackend) -> LoadOptions {
    LoadOptions {
        implicit_sources: vec![embedded("prelude.md").unwrap()],
        excluded_module_attributes: vec![backend.excluded_module_attribute().into()],
        ..LoadOptions::default()
    }
}

fn source_loaded(backend: CompilationBackend) -> LoadedDefinition {
    load_for_compilation(
        ResolvedSource::new("tokens.k", SOURCE),
        "MAIN",
        None,
        &mut |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        },
        &options(backend),
    )
    .unwrap()
    .0
}

fn replacement_loaded(mut loaded: LoadedDefinition, right: Term) -> LoadedDefinition {
    let module = loaded
        .definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap();
    let sentence = module
        .local_sentences
        .iter_mut()
        .find(|sentence| matches!(&***sentence, Sentence::Rule { .. }))
        .unwrap();
    let Sentence::Rule { body, .. } = Arc::make_mut(sentence) else {
        unreachable!()
    };
    *body = Term::Rewrite {
        left: Box::new(Term::apply(
            "counter",
            vec![Term::apply("z", vec![]), Term::apply("z", vec![])],
        )),
        right: Box::new(right),
    };
    loaded.resolved = ResolvedDefinition::resolve(&loaded.definition).unwrap();
    loaded
}

fn token(text: &str, sort: &str) -> Term {
    Term::Token {
        token: text.into(),
        sort: Sort::new(sort),
    }
}

fn compile(loaded: &LoadedDefinition, backend: CompilationBackend) -> Result<(), CompileError> {
    compile_loaded_definition(
        loaded,
        CompileOptions {
            backend,
            ..CompileOptions::default()
        },
    )
    .map(|_| ())
}

#[test]
fn loaded_token_terms_require_a_domain_sort() {
    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        let original = source_loaded(backend);
        compile(&original, backend).unwrap();

        let invalid = replacement_loaded(
            original.clone(),
            Term::apply("counter", vec![token("7", "Nat"), Term::apply("z", vec![])]),
        );
        let error = compile(&invalid, backend).unwrap_err();
        assert_eq!(error.stage, "definition checks");
        assert!(
            error.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == DiagnosticCode::InvalidDomainValue
                    && diagnostic.message.contains("Token \"7\" of sort Nat")
                    && diagnostic.message.contains("Rule")
            }),
            "{error:?}"
        );

        for right in [
            Term::apply("integer", vec![token("7", "Int")]),
            Term::apply("named", vec![token("alice", "Name")]),
            Term::apply(
                "counter",
                vec![Term::apply("z", vec![]), Term::apply("z", vec![])],
            ),
        ] {
            compile(&replacement_loaded(original.clone(), right), backend).unwrap();
        }

        let main = original
            .definition
            .modules
            .iter()
            .find(|module| module.name == "MAIN")
            .unwrap()
            .clone();
        let structured = load_structured(
            Definition {
                main_module: "MAIN".into(),
                modules: vec![main],
                attributes: Default::default(),
            },
            &options(backend),
        )
        .unwrap();
        compile(&structured, backend).unwrap();
        let invalid = replacement_loaded(
            structured,
            Term::apply("counter", vec![token("7", "Nat"), Term::apply("z", vec![])]),
        );
        let error = compile(&invalid, backend).unwrap_err();
        assert!(
            error.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == DiagnosticCode::InvalidDomainValue
                    && diagnostic.message.contains("Token \"7\" of sort Nat")
            }),
            "{error:?}"
        );
    }
}
