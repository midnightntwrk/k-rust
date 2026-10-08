//! Tests for the adapter boundary.
//!
//! `prepared_with_structured_injection_for_test` is deliberately test-only.
//! It proves that structured sentences can reach the compiler after a parsed
//! bootstrap has established `LoadedDefinition` invariants; it is not a
//! supported substitute for an upstream structured preparation API.

use k_rust::{
    builtin,
    definition::{Attributes, ProductionItem, Sentence},
    kast::{Label, Sort, Term},
    kompile::CompilationBackend,
    kore::parser::parse_definition,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use krs_ir::SentenceKind;

use crate::{
    Backend, CapabilityAvailability, CompileOptions, FRONTEND_CAPABILITIES, FRONTEND_PIN,
    LoadedDefinition, adapt_definition, compile_definition, compile_loaded_definition,
    prepare_definition,
    test_fixtures::{MODULE, smoke_definition, smoke_definition_with_cell},
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

fn transition(left: &str, right: &str) -> Sentence {
    Sentence::Rule {
        body: Term::Rewrite {
            left: Box::new(Term::apply(left, Vec::new())),
            right: Box::new(Term::apply(right, Vec::new())),
        },
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    }
}

fn prepared_with_structured_injection_for_test(
    sentences: impl IntoIterator<Item = Sentence>,
) -> LoadedDefinition {
    let entry = ResolvedSource::new(
        "krs://adapter-test.k",
        r#"
            requires "domains.md"

            module KRS-ADAPTER-TEST
              imports DOMAINS
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
            CompilationBackend::Llvm.excluded_module_attribute().into(),
        ],
        ..LoadOptions::default()
    };
    let mut parts = load_with_options(entry, MODULE, &mut resolver, &options)
        .expect("test bootstrap must be preparable")
        .into_parts();
    parts
        .definition
        .modules
        .iter_mut()
        .find(|module| module.name == MODULE)
        .expect("test bootstrap module must exist")
        .local_sentences
        .extend(sentences.into_iter().map(std::sync::Arc::new));
    LoadedDefinition::from_loaded_parts(parts).expect("structured test injection must resolve")
}

#[test]
fn pin_and_portable_capabilities_are_explicit() {
    let capabilities = std::hint::black_box(FRONTEND_CAPABILITIES);
    assert_eq!(FRONTEND_PIN.crate_version, "0.4.0");
    assert_eq!(FRONTEND_PIN.k_version, "7.1.337");
    assert!(capabilities.supports_backend(Backend::Llvm));
    assert!(capabilities.supports_backend(Backend::Haskell));
    assert!(matches!(
        capabilities.z3_inference,
        CapabilityAvailability::Available
    ));
    assert!(matches!(
        capabilities.mpfr_folding,
        CapabilityAvailability::Unavailable(_)
    ));
    assert!(matches!(
        capabilities.structured_definition_preparation,
        CapabilityAvailability::Available
    ));
}

#[test]
fn permanent_structured_compile_uses_the_pinned_compatibility_layer() {
    let artifacts = compile_definition(&smoke_definition(), CompileOptions::default())
        .expect("permanent compilation uses public pinned preparation primitives");
    assert!(!artifacts.definition_kore.is_empty());
    assert!(!artifacts.syntax_definition_kore.is_empty());
}

#[test]
fn only_the_haskell_backend_proves_claims() {
    for backend in Backend::ALL {
        assert_eq!(backend.proves_claims(), backend == Backend::Haskell);
    }
}

#[test]
fn permanent_structured_compile_replaces_the_bootstrap_default_configuration() {
    let definition = smoke_definition_with_cell(SentenceKind::Transition, "instrs");
    let adapted = adapt_definition(&definition).unwrap();
    let loaded = prepare_definition(adapted.definition, Backend::Llvm).unwrap();
    assert!(
        loaded
            .definition()
            .modules
            .iter()
            .all(|module| module.name != "DEFAULT-CONFIGURATION")
    );
    assert!(loaded.definition().modules.iter().all(|module| {
        module
            .imports
            .iter()
            .all(|import| import.name != "DEFAULT-CONFIGURATION")
    }));

    let artifacts = compile_definition(&definition, CompileOptions::default())
        .expect("the authored <instrs> configuration must replace the bootstrap <k> configuration");
    assert!(artifacts.definition_kore.contains("instrs"));
    assert!(!artifacts.definition_kore.contains("Lbl'-LT-'k'-GT-'"));
}

#[test]
fn compile_definition_reparses_both_kore_artifacts() {
    let artifacts = compile_definition(&smoke_definition(), CompileOptions::default())
        .expect("the smoke IR must compile through the native route");
    parse_definition(&artifacts.definition_kore).unwrap();
    parse_definition(&artifacts.syntax_definition_kore).unwrap();
    assert!(artifacts.definition_kore.contains("Lblfoo"));
    assert!(artifacts.definition_kore.contains("Lblbar"));
    assert!(artifacts.definition_kore.contains("initKCell"));
    let checkout = env!("CARGO_MANIFEST_DIR");
    assert!(!artifacts.definition_kore.contains(checkout));
    assert!(!artifacts.syntax_definition_kore.contains(checkout));
}

#[test]
fn structured_constructor_and_rule_reach_reparsable_kore() {
    let loaded = prepared_with_structured_injection_for_test([
        constructor("bar", "bar"),
        transition("foo", "bar"),
    ]);

    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .expect("structured sentences must compile");

    parse_definition(&artifacts.definition_kore).expect("definition KORE must reparse");
    parse_definition(&artifacts.syntax_definition_kore)
        .expect("syntax definition KORE must reparse");
    assert!(artifacts.definition_kore.contains("foo"));
    assert!(artifacts.definition_kore.contains("bar"));
}

#[test]
fn frontend_failures_retain_stage_and_structured_diagnostics() {
    let loaded = prepared_with_structured_injection_for_test([transition("foo", "missing")]);

    let error = compile_loaded_definition(&loaded, CompileOptions::default())
        .expect_err("an undefined label must be rejected");

    assert_eq!(error.stage(), "definition checks");
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code.as_str() == "UndefinedKLabel")
    );
    assert!(!error.message().is_empty());
}

#[test]
fn the_route_table_runs_ground_and_wide_floats_only_on_java_k() {
    for feature in ["GroundFloatFolding", "FloatPrecisionBeyondBinary64"] {
        for route in crate::Route::ALL {
            let availability = crate::route_capability(feature, route);
            assert_eq!(
                matches!(availability, CapabilityAvailability::Unavailable(_)),
                matches!(
                    route,
                    crate::Route::NativeRust | crate::Route::NativeLlvm | crate::Route::Browser
                ),
                "{feature} on {}",
                route.name()
            );
        }
    }
}

#[test]
fn the_route_table_refuses_anywhere_rules_only_on_the_java_haskell_reference() {
    for route in crate::Route::ALL {
        assert_eq!(crate::Route::from_name(route.name()), Some(route));
        let availability = crate::route_capability("AnywhereRule", route);
        assert_eq!(
            matches!(availability, CapabilityAvailability::Unavailable(_)),
            route == crate::Route::JavaHaskellReference,
            "{}",
            route.name()
        );
    }
    assert_eq!(
        crate::route_capability("NoSuchFeature", crate::Route::JavaHaskellReference),
        CapabilityAvailability::Available
    );
    assert_eq!(
        crate::Route::native(Backend::Llvm),
        crate::Route::NativeLlvm
    );
    assert_eq!(
        crate::Route::native(Backend::Haskell),
        crate::Route::NativeRust
    );
}
