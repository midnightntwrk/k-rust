//! Tests for the adapter boundary.
//!
//! `prepared_with_structured_injection_for_test` is deliberately test-only.
//! It proves that structured sentences can reach the compiler after a parsed
//! bootstrap has established `LoadedDefinition` invariants; it is not a
//! supported substitute for an upstream structured preparation API.

use k_rust::{
    builtin,
    definition::{Attributes, ProductionItem, ResolvedDefinition, Sentence},
    kast::{Label, Sort, Term},
    kompile::CompilationBackend,
    kore::parser::parse_definition,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use krs_ir::{
    CellDeclaration, ConfigurationSentence, DefinitionIr, DefinitionModule, DefinitionSentence,
    DefinitionSortRef, DefinitionTerm, InitializerDeclaration, LabelId, LabelIdentity, ModuleId,
    NodeOrigin, OriginStack, PackageId, ProductionItem as IrProductionItem, ProductionSentence,
    RuleSentence, SentenceKind, Sha256Digest, SourceFileId, SourceMapKey, SourceRange,
    SubsortSentence, SymbolId, SymbolIdentity, SymbolKind, SyntaxSortSentence,
};

use super::{
    AdapterError, Backend, CapabilityAvailability, CapabilityError, CompileOptions,
    DefinitionCompileError, FRONTEND_CAPABILITIES, FRONTEND_PIN, LoadedDefinition, NativeNodeRole,
    PORTABLE_PRELUDE_POLICY, PortablePreludePolicy, adapt_definition, compile_definition,
    compile_definition_provisional_oracle, compile_loaded_definition,
};

const MODULE: &str = "KRS-ADAPTER-TEST";

fn m2_definition() -> DefinitionIr {
    m2_definition_with(SentenceKind::Transition, "initKCell")
}

fn m2_definition_with_kind(rule_kind: SentenceKind) -> DefinitionIr {
    m2_definition_with(rule_kind, "initKCell")
}

#[allow(clippy::too_many_lines)]
fn m2_definition_with(rule_kind: SentenceKind, initializer_name: &str) -> DefinitionIr {
    let k_item = SymbolId::new("sort.kitem").unwrap();
    let k_result = SymbolId::new("sort.kresult").unwrap();
    let value = SymbolId::new("sort.value").unwrap();
    let foo = SymbolId::new("production.foo").unwrap();
    let bar = SymbolId::new("production.bar").unwrap();
    let syntax_id = ModuleId::new("SMOKE-SYNTAX").unwrap();
    let main_id = ModuleId::new("SMOKE").unwrap();
    let syntax = DefinitionModule::new(
        node("def.module.syntax"),
        syntax_id.clone(),
        Vec::new(),
        vec![
            DefinitionSentence::Production(
                ProductionSentence::new(
                    node("def.production.bar"),
                    symbol("production.bar", "Lblbar", SymbolKind::Production),
                    value.clone(),
                    vec![IrProductionItem::terminal("bar").unwrap()],
                )
                .unwrap(),
            ),
            DefinitionSentence::Production(
                ProductionSentence::new(
                    node("def.production.foo"),
                    symbol("production.foo", "Lblfoo", SymbolKind::Production),
                    value.clone(),
                    vec![IrProductionItem::terminal("foo").unwrap()],
                )
                .unwrap(),
            ),
            DefinitionSentence::SyntaxSort(
                SyntaxSortSentence::new(
                    node("def.sort.kitem"),
                    symbol("sort.kitem", "KItem", SymbolKind::Sort),
                )
                .unwrap(),
            ),
            DefinitionSentence::SyntaxSort(
                SyntaxSortSentence::new(
                    node("def.sort.kresult"),
                    symbol("sort.kresult", "KResult", SymbolKind::Sort),
                )
                .unwrap(),
            ),
            DefinitionSentence::SyntaxSort(
                SyntaxSortSentence::new(
                    node("def.sort.value"),
                    symbol("sort.value", "Value", SymbolKind::Sort),
                )
                .unwrap(),
            ),
            DefinitionSentence::Subsort(SubsortSentence::new(
                node("def.subsort.kresult-kitem"),
                k_result.clone(),
                k_item.clone(),
            )),
            DefinitionSentence::Subsort(SubsortSentence::new(
                node("def.subsort.value-kresult"),
                value.clone(),
                k_result,
            )),
        ],
    );
    let initializer = InitializerDeclaration::new(
        node("def.initializer"),
        symbol(
            "initializer.machine",
            initializer_name,
            SymbolKind::Initializer,
        ),
        Vec::new(),
        DefinitionTerm::k_sequence(
            node("def.term.init.sequence"),
            k_item,
            vec![DefinitionTerm::application(
                node("def.term.init.foo"),
                value.clone(),
                foo.clone(),
                Vec::new(),
            )],
        ),
    )
    .unwrap();
    let configuration = DefinitionSentence::Configuration(ConfigurationSentence::new(
        node("def.configuration"),
        CellDeclaration::new(
            node("def.cell.k"),
            symbol("cell.k", "k", SymbolKind::Cell),
            DefinitionSortRef::k_sequence(),
        )
        .unwrap(),
        initializer,
    ));
    let rewrite = DefinitionTerm::rewrite(
        node("def.term.rule.rewrite"),
        value.clone(),
        DefinitionTerm::application(
            node("def.term.rule.foo"),
            value.clone(),
            foo,
            Vec::new(),
        ),
        DefinitionTerm::application(
            node("def.term.rule.bar"),
            value.clone(),
            bar,
            Vec::new(),
        ),
    )
    .unwrap();
    let rule = DefinitionSentence::Rule(
        RuleSentence::new(
            node("def.rule.foo-to-bar"),
            LabelIdentity::new(
                LabelId::new("rule.foo-to-bar").unwrap(),
                "ORG-EXAMPLE-SMOKE.rules.foo-to-bar",
            )
            .unwrap(),
            rule_kind,
            Vec::new(),
            rewrite,
        )
        .unwrap(),
    );
    let main = DefinitionModule::new(
        node("def.module.main"),
        main_id.clone(),
        vec![syntax_id],
        vec![configuration, rule],
    );
    DefinitionIr::new(main_id, vec![main, syntax]).unwrap()
}

fn symbol(id: &str, emitted_name: &str, kind: SymbolKind) -> SymbolIdentity {
    SymbolIdentity::new(SymbolId::new(id).unwrap(), emitted_name, kind).unwrap()
}

fn node(key: &str) -> NodeOrigin {
    let package = PackageId::new(
        "ORG-EXAMPLE-SMOKE",
        "smoke-semantics",
        "0.1.0",
        "workspace",
    )
    .unwrap();
    let file = SourceFileId::new(
        package,
        "src/lib.rs",
        Sha256Digest::new("0123456789abcdef".repeat(4)).unwrap(),
    )
    .unwrap();
    NodeOrigin::new(
        SourceMapKey::new(key).unwrap(),
        OriginStack::authored(SourceRange::new(file, 0, 3).unwrap()),
    )
}

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
            module KRS-ADAPTER-TEST
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
    let mut loaded = load_with_options(entry, MODULE, &mut resolver, &options)
        .expect("test bootstrap must be preparable");
    loaded
        .definition
        .modules
        .iter_mut()
        .find(|module| module.name == MODULE)
        .expect("test bootstrap module must exist")
        .local_sentences
        .extend(sentences);
    loaded.resolved = ResolvedDefinition::resolve(&loaded.definition)
        .expect("structured test injection must resolve");
    loaded
}

#[test]
fn pin_and_portable_capabilities_are_explicit() {
    let capabilities = std::hint::black_box(FRONTEND_CAPABILITIES);
    assert_eq!(FRONTEND_PIN.crate_version, "0.3.0");
    assert_eq!(FRONTEND_PIN.k_version, "7.1.337");
    assert!(capabilities.supports_backend(Backend::Llvm));
    assert!(capabilities.supports_backend(Backend::Haskell));
    assert!(matches!(
        capabilities.z3_inference,
        CapabilityAvailability::Unavailable(_)
    ));
    assert!(matches!(
        capabilities.mpfr_folding,
        CapabilityAvailability::Unavailable(_)
    ));
    assert!(matches!(
        capabilities.structured_definition_preparation,
        CapabilityAvailability::Unavailable(_)
    ));
    assert_eq!(
        PORTABLE_PRELUDE_POLICY,
        PortablePreludePolicy::ExplicitImportsOnly
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn definition_ir_maps_structurally_without_frontend_metadata() {
    let adapted = adapt_definition(&m2_definition()).expect("M2 IR must adapt");
    let native = adapted.definition();
    assert_eq!(native.main_module, "SMOKE");
    assert_eq!(native.modules.len(), 2);

    let main = native
        .modules
        .iter()
        .find(|module| module.name == "SMOKE")
        .unwrap();
    assert_eq!(main.imports.len(), 1);
    assert_eq!(main.imports[0].name, "SMOKE-SYNTAX");
    assert!(main.imports[0].public);
    assert_eq!(
        main.attributes.source(),
        Some("src/lib.rs"),
        "only the portable package-relative source is attached"
    );
    assert_eq!(main.attributes.location(), None);

    let configuration = main
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Configuration { body, .. } => Some(body),
            _ => None,
        })
        .expect("configuration must remain structured");
    let Term::Apply { label, arguments } = configuration else {
        panic!("configuration must use the native structured cell form")
    };
    assert_eq!(label.name, "#configCell");
    assert!(matches!(
        arguments.as_slice(),
        [
            Term::Token { token: start, .. },
            Term::Apply { label: properties, .. },
            Term::Sequence(items),
            Term::Token { token: end, .. }
        ] if start == "k"
            && end == "k"
            && properties.name == "#cellPropertyListTerminator"
            && matches!(items.as_slice(), [Term::Apply { label, arguments }] if label.name == "Lblfoo" && arguments.is_empty())
    ));

    let rule = main
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } => Some((body, attributes)),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        rule.1.get_str("label"),
        Some("ORG-EXAMPLE-SMOKE.rules.foo-to-bar")
    );
    assert!(matches!(
        rule.0,
        Term::Rewrite { left, right }
            if matches!(left.unannotated(), Term::Apply { label, .. } if label.name == "Lblfoo")
                && matches!(right.unannotated(), Term::Apply { label, .. } if label.name == "Lblbar")
    ));

    let syntax = native
        .modules
        .iter()
        .find(|module| module.name == "SMOKE-SYNTAX")
        .unwrap();
    let subsorts = syntax
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: None,
                sort,
                items,
                ..
            } => match items.as_slice() {
                [ProductionItem::NonTerminal { sort: child, .. }] => {
                    Some((child.name.as_str(), sort.name.as_str()))
                }
                _ => None,
            },
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        subsorts,
        vec![("KResult", "KItem"), ("Value", "KResult")]
    );

    let keys = adapted
        .origins()
        .iter()
        .map(|mapping| mapping.key.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "def.module.main",
        "def.configuration",
        "def.cell.k",
        "def.initializer",
        "def.term.init.sequence",
        "def.term.init.foo",
        "def.rule.foo-to-bar",
        "def.term.rule.rewrite",
        "def.term.rule.foo",
        "def.term.rule.bar",
    ] {
        assert!(keys.contains(&expected), "missing origin seam for {expected}");
    }
    assert!(adapted.origins().iter().any(|mapping| {
        mapping.key.as_str() == "def.term.rule.bar"
            && matches!(mapping.role, NativeNodeRole::Term(ref path) if path == &[1])
    }));
}

#[test]
fn permanent_structured_compile_reports_the_upstream_api_blocker() {
    let error = compile_definition(&m2_definition(), CompileOptions::default())
        .expect_err("permanent compilation must not assemble LoadedDefinition fields");
    assert_eq!(
        error,
        DefinitionCompileError::Capability(
            CapabilityError::StructuredDefinitionPreparationUnavailable
        )
    );
}

#[test]
fn unsupported_sentence_kind_is_a_typed_capability_error() {
    let equation = m2_definition_with_kind(SentenceKind::Equation);
    assert!(matches!(
        adapt_definition(&equation),
        Err(AdapterError::Capability(
            CapabilityError::UnsupportedSentenceKind {
                kind: SentenceKind::Equation,
                ..
            }
        ))
    ));
}

#[test]
fn provisional_ir_oracle_compiles_and_reparses_both_kore_artifacts() {
    let artifacts = compile_definition_provisional_oracle(
        &m2_definition(),
        CompileOptions::default(),
    )
    .expect("frozen M2 IR must compile through the explicit provisional oracle");
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
fn provisional_oracle_rejects_initializer_identity_drift() {
    let error = compile_definition_provisional_oracle(
        &m2_definition_with(SentenceKind::Transition, "initMachine"),
        CompileOptions::default(),
    )
    .expect_err("frontend-derived initializer identity must not replace the IR identity");
    assert!(matches!(
        error,
        super::ProvisionalCompileError::InitializerIdentity { .. }
    ));
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
            .any(|diagnostic| diagnostic.code == "UndefinedKLabel")
    );
    assert!(!error.message().is_empty());
}
