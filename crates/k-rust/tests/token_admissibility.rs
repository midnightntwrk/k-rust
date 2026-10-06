use std::{collections::BTreeMap, sync::Arc};

use k_rust::{
    builtin::embedded,
    definition::{
        Attributes, Definition, FlatModule, ResolvedDefinition, Sentence, SortCatalog, SortHead,
    },
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
fn declared_domain_sorts_include_token_and_parametric_instances_but_not_hooked_ones() {
    let parameter = Sort::new("T");
    let parametric = Sort::with_parameters("Boxed", vec![parameter.clone()]);
    let declarations = [
        Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("Hooked"),
            attributes: Attributes::new(BTreeMap::from([("hook".into(), json!("CUSTOM.Value"))])),
        },
        Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("HookedToken"),
            attributes: Attributes::new(BTreeMap::from([
                ("hook".into(), json!("CUSTOM.Value")),
                ("token".into(), json!("")),
            ])),
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
    // A hook fixes how the backend computes on a sort's values; it declares no literals.
    assert!(!catalog.admits_domain_value(&Sort::new("Hooked")));
    assert!(catalog.admits_domain_value(&Sort::new("HookedToken")));
    assert!(catalog.admits_domain_value(&Sort::new("Bool")));
    assert!(catalog.admits_domain_value(&Sort::new("KConfigVar")));
    assert!(catalog.admits_domain_value(&Sort::with_parameters("Boxed", vec![Sort::new("Int")],)));
    assert!(!catalog.admits_domain_value(&Sort::new("Nat")));

    // The heads that carry `hasDomainValues` are exactly the heads of the admitted sorts.
    assert!(!catalog.head_admits_domain_values(&SortHead::nullary("Hooked")));
    assert!(catalog.head_admits_domain_values(&SortHead::nullary("HookedToken")));
    assert!(catalog.head_admits_domain_values(&SortHead::nullary("Bool")));
    assert!(catalog.head_admits_domain_values(&SortHead::nullary("KConfigVar")));
    assert!(catalog.head_admits_domain_values(&SortHead::new("Boxed", 1)));
    assert!(!catalog.head_admits_domain_values(&SortHead::nullary("Boxed")));
    assert!(!catalog.head_admits_domain_values(&SortHead::nullary("Nat")));
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

/// A literal a compiler pass writes after the definition checks is admitted by the same
/// predicate: a hooked sort without a token declaration has no literal domain to convert into.
#[test]
fn emission_rejects_a_hooked_sort_literal_without_token_declaration() {
    let module = |attributes: Attributes| {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: vec![Arc::new(Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("String"),
                    attributes,
                })],
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        };
        ResolvedDefinition::resolve(&definition).unwrap()
    };
    let literal = token("\"x\"", "String");

    let hooked = module(Attributes::new(BTreeMap::from([(
        "hook".into(),
        json!("STRING.String"),
    )])));
    let error = TermConverter::new(&hooked, "MAIN")
        .unwrap()
        .convert(&literal)
        .unwrap_err();
    assert!(matches!(error, TermConversionError::InvalidToken { .. }));

    let hooked_token = module(Attributes::new(BTreeMap::from([
        ("hook".into(), json!("STRING.String")),
        ("token".into(), json!("")),
    ])));
    TermConverter::new(&hooked_token, "MAIN")
        .unwrap()
        .convert(&literal)
        .unwrap();
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

fn replacement_loaded(loaded: LoadedDefinition, right: Term) -> LoadedDefinition {
    let mut parts = loaded.into_parts();
    let module = parts
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
    LoadedDefinition::from_loaded_parts(parts).unwrap()
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

/// A token term whose sort is not a domain sort is rejected where the definition is checked, on
/// `backend`, whether the definition was loaded from source or from its structured main module;
/// tokens of domain sorts compile.
fn assert_loaded_token_terms_require_a_domain_sort(backend: CompilationBackend) {
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
        .definition()
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

mod loaded_token_terms_require_a_domain_sort {
    use super::{CompilationBackend, assert_loaded_token_terms_require_a_domain_sort};

    #[test]
    fn rust() {
        assert_loaded_token_terms_require_a_domain_sort(CompilationBackend::Rust);
    }

    #[test]
    fn llvm() {
        assert_loaded_token_terms_require_a_domain_sort(CompilationBackend::Llvm);
    }
}

const HOOKED_SOURCE: &str = r#"
module MAIN
  imports BASIC-K
  imports INT-SYNTAX
  imports MAP
  syntax KItem ::= go(Int) [symbol(go)] | keep(Map) [symbol(keep)]
  rule go(0) => RIGHT
endmodule
"#;

fn hooked_loaded(right: &str, backend: CompilationBackend) -> LoadedDefinition {
    load_for_compilation(
        ResolvedSource::new("hooked.k", HOOKED_SOURCE.replace("RIGHT", right)),
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

/// `MAP.Map` has a hook and no token declaration, so its values include no domain values: a
/// literal of that sort is rejected where the definition is checked rather than emitted under a
/// declaration without `hasDomainValues`.
#[test]
fn hooked_sort_literal_without_token_declaration_is_rejected() {
    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        compile(&hooked_loaded("keep(.Map)", backend), backend).unwrap();

        let error = compile(
            &hooked_loaded(r#"keep(#token("x", "Map"))"#, backend),
            backend,
        )
        .unwrap_err();
        assert_eq!(error.stage, "definition checks");
        assert!(
            error.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == DiagnosticCode::InvalidDomainValue
                    && diagnostic.message.contains("Token \"x\" of sort Map")
            }),
            "{error:?}"
        );
    }
}
