//! Tests for the adapter boundary.
//!
//! `prepared_with_structured_injection_for_test` is deliberately test-only.
//! It proves that structured sentences can reach the compiler after a parsed
//! bootstrap has established `LoadedDefinition` invariants; it is not a
//! supported substitute for an upstream structured preparation API.

use k_rust::{
    backend::{Backend as NativeBackend, BackendOptions, ExecuteRequest},
    builtin,
    definition::{Attributes, ProductionItem, ResolvedDefinition, Sentence},
    kast::{Label, Sort, Term},
    kompile::CompilationBackend,
    kore::{
        ast::Pattern as KorePattern,
        parser::{parse_definition, parse_pattern},
    },
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use krs_ir::{
    ApplicationRef, BuiltinOperation, CellAttribute, CellContentFrame, CellPost, ClaimModality,
    ConfigurationRoot, ContextAliasSentence, DefinitionClaim, DefinitionClaimBinder, DefinitionIr,
    DefinitionModule, DefinitionProductionAttribute, DefinitionRuleCondition, DefinitionSentence,
    DefinitionSortRef, DefinitionTerm, FixedCell, FixedCellClause, FixedCellPattern,
    FixedConfiguration, FixedConfigurationPattern, FixedConfigurationRewrite,
    FixedConfigurationVariable, FixedInitializerCell, FormatFragment, GroupAssociativity,
    GroupAssociativitySentence, HookOperation, ItemKind, LabelId, LabelIdentity, ListOperation,
    MapOperation, ModuleId, NodeOrigin, PrecedenceRelation, ProductionFieldId,
    ProductionFieldReference, ProductionGroupId, ProductionItem as IrProductionItem,
    ProductionResultSort, ProductionSentence, RuleSentence, SemanticId, SentenceKind, SetOperation,
    SourceMapKey, StableItemId, StrictnessKind, SubsortSentence, SymbolId, SymbolIdentity,
    SymbolKind, SyntaxSortSentence,
};

use super::{
    Adapter, Author, Backend, CapabilityAvailability, CompileOptions, FRONTEND_CAPABILITIES,
    FRONTEND_PIN, GeneratingPass, InputAddress, InputSentenceKind, InputSpace, LoadedDefinition,
    NativeNodeRole, PORTABLE_PRELUDE_POLICY, PortablePreludePolicy, ProvenanceError, TermContext,
    adapt_definition, adapt_definition_for, compile_definition,
    compile_definition_provisional_oracle, compile_loaded_definition, module_builtin_imports,
    prepare_definition,
};

const MODULE: &str = "KRS-ADAPTER-TEST";

fn smoke_definition() -> DefinitionIr {
    smoke_definition_with_cell(SentenceKind::Transition, "k")
}

#[allow(clippy::too_many_lines)]
fn smoke_definition_with_cell(rule_kind: SentenceKind, cell_name: &str) -> DefinitionIr {
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
        Vec::new(),
        vec![
            DefinitionSentence::Production(
                ProductionSentence::new(
                    node("def.production.bar"),
                    symbol("production.bar", "Lblbar", SymbolKind::Production),
                    DefinitionSortRef::declared(value.clone()),
                    vec![
                        IrProductionItem::terminal(node("def.production.bar.item"), "bar").unwrap(),
                    ],
                    Vec::new(),
                )
                .unwrap(),
            ),
            DefinitionSentence::Production(
                ProductionSentence::new(
                    node("def.production.foo"),
                    symbol("production.foo", "Lblfoo", SymbolKind::Production),
                    DefinitionSortRef::declared(value.clone()),
                    vec![
                        IrProductionItem::terminal(node("def.production.foo.item"), "foo").unwrap(),
                    ],
                    Vec::new(),
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
                DefinitionSortRef::declared(k_result.clone()),
                DefinitionSortRef::declared(k_item.clone()),
            )),
            DefinitionSentence::Subsort(SubsortSentence::new(
                node("def.subsort.value-kresult"),
                DefinitionSortRef::declared(value.clone()),
                DefinitionSortRef::declared(k_result),
            )),
        ],
    );
    let configuration = {
        let cell = SymbolId::new("cell.k").unwrap();
        let program = semantic_id("program");
        let initializer_body = DefinitionTerm::k_sequence(
            node("def.term.init.sequence"),
            DefinitionSortRef::declared(k_item.clone()),
            vec![DefinitionTerm::variable(
                node("def.term.init.program"),
                DefinitionSortRef::declared(value.clone()),
                program.clone(),
            )],
        );
        DefinitionSentence::Configuration(
            FixedConfiguration::new(
                node("def.configuration"),
                semantic_id("configuration.machine"),
                ConfigurationRoot::GeneratedTop,
                vec![
                    FixedCell::leaf(
                        node("def.cell.k"),
                        cell.clone(),
                        cell_name,
                        Vec::new(),
                        DefinitionSortRef::k_sequence(),
                    )
                    .unwrap(),
                ],
                node("def.initializer"),
                semantic_id("initializer.machine"),
                vec![
                    FixedConfigurationVariable::new(
                        node("def.initializer.program"),
                        program,
                        "PGM",
                        DefinitionSortRef::declared(value.clone()),
                        true,
                    )
                    .unwrap(),
                ],
                vec![FixedInitializerCell::term(
                    node("def.initializer.cell"),
                    cell,
                    initializer_body,
                )],
            )
            .unwrap(),
        )
    };
    let rewrite = DefinitionTerm::rewrite(
        node("def.term.rule.rewrite"),
        DefinitionSortRef::declared(value.clone()),
        DefinitionTerm::application(
            node("def.term.rule.foo"),
            DefinitionSortRef::declared(value.clone()),
            ApplicationRef::Declared(foo),
            Vec::new(),
        ),
        DefinitionTerm::application(
            node("def.term.rule.bar"),
            DefinitionSortRef::declared(value.clone()),
            ApplicationRef::Declared(bar),
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
        Vec::new(),
        vec![configuration, rule],
    );
    DefinitionIr::new(main_id, vec![main, syntax]).unwrap()
}

fn symbol(id: &str, emitted_name: &str, kind: SymbolKind) -> SymbolIdentity {
    SymbolIdentity::new(SymbolId::new(id).unwrap(), emitted_name, kind).unwrap()
}

#[test]
fn native_rule_labels_match_the_source_frontend_namespace_policy() {
    assert_eq!(
        super::native_rule_label("SMOKE", "foo-to-bar"),
        "SMOKE.foo-to-bar"
    );
    assert_eq!(
        super::native_rule_label("SMOKE", "krsRule_725f2944b8a5a8eaf4b9fc6c"),
        "krsRule_725f2944b8a5a8eaf4b9fc6c"
    );
}

#[test]
fn native_claim_modalities_are_explicit() {
    assert_eq!(
        super::claim_modality_attribute(ClaimModality::OnePath),
        "one-path"
    );
    assert_eq!(
        super::claim_modality_attribute(ClaimModality::AllPaths),
        "all-path"
    );
}

#[test]
fn typed_hook_maps_to_the_exact_native_frontend_attribute() {
    let production = ProductionSentence::new(
        node("hook.production"),
        symbol(
            "production.keccak256raw",
            "Keccak256raw",
            SymbolKind::Production,
        ),
        DefinitionSortRef::bytes(),
        vec![
            IrProductionItem::terminal(node("hook.open"), "Keccak256raw(").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.value"),
                ProductionFieldId::new("value").unwrap(),
                DefinitionSortRef::bytes(),
            ),
            IrProductionItem::terminal(node("hook.close"), ")").unwrap(),
        ],
        vec![
            DefinitionProductionAttribute::Function {
                origin: node("hook.function"),
            },
            DefinitionProductionAttribute::Total {
                origin: node("hook.total"),
            },
            DefinitionProductionAttribute::Hook {
                origin: node("hook.attribute"),
                operation: HookOperation::KryptoKeccak256Raw,
            },
        ],
    )
    .unwrap();
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let native = adapter.production(&production, MODULE, 0).unwrap();
    let Sentence::Production { attributes, .. } = native else {
        panic!("hooked function must remain a native production")
    };
    assert_eq!(attributes.get_str("hook"), Some("KRYPTO.keccak256raw"));
    assert!(attributes.get("function").is_some());
    assert!(attributes.get("total").is_some());
}

#[test]
fn typed_sha256_hook_maps_to_the_exact_native_frontend_attribute() {
    let production = ProductionSentence::new(
        node("hook.sha256.production"),
        symbol("production.sha256raw", "Sha256raw", SymbolKind::Production),
        DefinitionSortRef::bytes(),
        vec![
            IrProductionItem::terminal(node("hook.sha256.open"), "Sha256raw(").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.sha256.value"),
                ProductionFieldId::new("value").unwrap(),
                DefinitionSortRef::bytes(),
            ),
            IrProductionItem::terminal(node("hook.sha256.close"), ")").unwrap(),
        ],
        vec![
            DefinitionProductionAttribute::Function {
                origin: node("hook.sha256.function"),
            },
            DefinitionProductionAttribute::Total {
                origin: node("hook.sha256.total"),
            },
            DefinitionProductionAttribute::Hook {
                origin: node("hook.sha256.attribute"),
                operation: HookOperation::KryptoSha256Raw,
            },
        ],
    )
    .unwrap();
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let native = adapter.production(&production, MODULE, 0).unwrap();
    let Sentence::Production { attributes, .. } = native else {
        panic!("hooked function must remain a native production")
    };
    assert_eq!(attributes.get_str("hook"), Some("KRYPTO.sha256raw"));
    assert!(attributes.get("function").is_some());
    assert!(attributes.get("total").is_some());
}

#[test]
fn typed_ripemd160_hook_maps_to_the_exact_native_frontend_attribute() {
    let production = ProductionSentence::new(
        node("hook.ripemd160.production"),
        symbol(
            "production.ripemd160raw",
            "Ripemd160raw",
            SymbolKind::Production,
        ),
        DefinitionSortRef::bytes(),
        vec![
            IrProductionItem::terminal(node("hook.ripemd160.open"), "Ripemd160raw(").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.ripemd160.value"),
                ProductionFieldId::new("value").unwrap(),
                DefinitionSortRef::bytes(),
            ),
            IrProductionItem::terminal(node("hook.ripemd160.close"), ")").unwrap(),
        ],
        vec![
            DefinitionProductionAttribute::Function {
                origin: node("hook.ripemd160.function"),
            },
            DefinitionProductionAttribute::Total {
                origin: node("hook.ripemd160.total"),
            },
            DefinitionProductionAttribute::Hook {
                origin: node("hook.ripemd160.attribute"),
                operation: HookOperation::KryptoRipemd160Raw,
            },
        ],
    )
    .unwrap();
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let native = adapter.production(&production, MODULE, 0).unwrap();
    let Sentence::Production { attributes, .. } = native else {
        panic!("hooked function must remain a native production")
    };
    assert_eq!(attributes.get_str("hook"), Some("KRYPTO.ripemd160raw"));
    assert!(attributes.get("function").is_some());
    assert!(attributes.get("total").is_some());
}

#[test]
fn typed_ecdsa_recover_hook_maps_to_the_exact_native_frontend_attribute() {
    let production = ProductionSentence::new(
        node("hook.ecdsa-recover.production"),
        symbol(
            "production.ecdsa-recover",
            "EcdsaRecover",
            SymbolKind::Production,
        ),
        DefinitionSortRef::bytes(),
        vec![
            IrProductionItem::terminal(node("hook.ecdsa-recover.open"), "EcdsaRecover(").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.ecdsa-recover.hash"),
                ProductionFieldId::new("hash").unwrap(),
                DefinitionSortRef::bytes(),
            ),
            IrProductionItem::terminal(node("hook.ecdsa-recover.comma-1"), ", ").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.ecdsa-recover.recovery"),
                ProductionFieldId::new("recovery").unwrap(),
                DefinitionSortRef::int(),
            ),
            IrProductionItem::terminal(node("hook.ecdsa-recover.comma-2"), ", ").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.ecdsa-recover.r"),
                ProductionFieldId::new("r").unwrap(),
                DefinitionSortRef::bytes(),
            ),
            IrProductionItem::terminal(node("hook.ecdsa-recover.comma-3"), ", ").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.ecdsa-recover.s"),
                ProductionFieldId::new("s").unwrap(),
                DefinitionSortRef::bytes(),
            ),
            IrProductionItem::terminal(node("hook.ecdsa-recover.close"), ")").unwrap(),
        ],
        vec![
            DefinitionProductionAttribute::Function {
                origin: node("hook.ecdsa-recover.function"),
            },
            DefinitionProductionAttribute::Total {
                origin: node("hook.ecdsa-recover.total"),
            },
            DefinitionProductionAttribute::Hook {
                origin: node("hook.ecdsa-recover.attribute"),
                operation: HookOperation::KryptoEcdsaRecover,
            },
        ],
    )
    .unwrap();
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let native = adapter.production(&production, MODULE, 0).unwrap();
    let Sentence::Production { attributes, .. } = native else {
        panic!("hooked function must remain a native production")
    };
    assert_eq!(attributes.get_str("hook"), Some("KRYPTO.ecdsaRecover"));
    assert!(attributes.get("function").is_some());
    assert!(attributes.get("total").is_some());
}

#[test]
#[allow(clippy::too_many_lines)] // Verifies the complete typed BN128 hook family.
fn typed_bn128_hooks_map_to_exact_native_frontend_attributes() {
    let point = DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap());
    let g2_point = point.clone();
    let attributes = |operation| {
        vec![
            DefinitionProductionAttribute::Function {
                origin: node("hook.bn128.function"),
            },
            DefinitionProductionAttribute::Total {
                origin: node("hook.bn128.total"),
            },
            DefinitionProductionAttribute::Hook {
                origin: node("hook.bn128.attribute"),
                operation,
            },
        ]
    };
    let valid = ProductionSentence::new(
        node("hook.bn128-valid.production"),
        symbol(
            "production.bn128-valid",
            "Bn128Valid",
            SymbolKind::Production,
        ),
        DefinitionSortRef::bool(),
        vec![
            IrProductionItem::terminal(node("hook.bn128-valid.open"), "Bn128Valid(").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.bn128-valid.point"),
                ProductionFieldId::new("point").unwrap(),
                point.clone(),
            ),
            IrProductionItem::terminal(node("hook.bn128-valid.close"), ")").unwrap(),
        ],
        attributes(HookOperation::KryptoBn128Valid),
    )
    .unwrap();
    let add = ProductionSentence::new(
        node("hook.bn128-add.production"),
        symbol("production.bn128-add", "Bn128Add", SymbolKind::Production),
        point.clone(),
        vec![
            IrProductionItem::terminal(node("hook.bn128-add.open"), "Bn128Add(").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.bn128-add.left"),
                ProductionFieldId::new("left").unwrap(),
                point.clone(),
            ),
            IrProductionItem::terminal(node("hook.bn128-add.comma"), ",").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.bn128-add.right"),
                ProductionFieldId::new("right").unwrap(),
                point.clone(),
            ),
            IrProductionItem::terminal(node("hook.bn128-add.close"), ")").unwrap(),
        ],
        attributes(HookOperation::KryptoBn128Add),
    )
    .unwrap();
    let mul = ProductionSentence::new(
        node("hook.bn128-mul.production"),
        symbol("production.bn128-mul", "Bn128Mul", SymbolKind::Production),
        point.clone(),
        vec![
            IrProductionItem::terminal(node("hook.bn128-mul.open"), "Bn128Mul(").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.bn128-mul.point"),
                ProductionFieldId::new("point").unwrap(),
                point.clone(),
            ),
            IrProductionItem::terminal(node("hook.bn128-mul.comma"), ",").unwrap(),
            IrProductionItem::non_terminal(
                node("hook.bn128-mul.scalar"),
                ProductionFieldId::new("scalar").unwrap(),
                DefinitionSortRef::int(),
            ),
            IrProductionItem::terminal(node("hook.bn128-mul.close"), ")").unwrap(),
        ],
        attributes(HookOperation::KryptoBn128Mul),
    )
    .unwrap();
    let g2_valid = ProductionSentence::new(
        node("hook.bn128-g2-valid.production"),
        symbol(
            "production.bn128-g2-valid",
            "Bn128G2Valid",
            SymbolKind::Production,
        ),
        DefinitionSortRef::bool(),
        vec![IrProductionItem::non_terminal(
            node("hook.bn128-g2-valid.point"),
            ProductionFieldId::new("point").unwrap(),
            g2_point,
        )],
        attributes(HookOperation::KryptoBn128G2Valid),
    )
    .unwrap();
    let ate = ProductionSentence::new(
        node("hook.bn128-ate.production"),
        symbol("production.bn128-ate", "Bn128Ate", SymbolKind::Production),
        DefinitionSortRef::bool(),
        vec![
            IrProductionItem::non_terminal(
                node("hook.bn128-ate.g1"),
                ProductionFieldId::new("g1").unwrap(),
                DefinitionSortRef::list(),
            ),
            IrProductionItem::non_terminal(
                node("hook.bn128-ate.g2"),
                ProductionFieldId::new("g2").unwrap(),
                DefinitionSortRef::list(),
            ),
        ],
        attributes(HookOperation::KryptoBn128Ate),
    )
    .unwrap();
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    for (index, (production, expected)) in [
        (&valid, "KRYPTO.bn128valid"),
        (&add, "KRYPTO.bn128add"),
        (&mul, "KRYPTO.bn128mul"),
        (&g2_valid, "KRYPTO.bn128g2valid"),
        (&ate, "KRYPTO.bn128ate"),
    ]
    .into_iter()
    .enumerate()
    {
        let native = adapter.production(production, MODULE, index).unwrap();
        let Sentence::Production { attributes, .. } = native else {
            panic!("hooked function must remain a native production")
        };
        assert_eq!(attributes.get_str("hook"), Some(expected));
        assert!(attributes.get("function").is_some());
        assert!(attributes.get("total").is_some());
    }
}

#[test]
fn native_claim_counter_is_a_fresh_rhs_internal() {
    let counter = super::native_claim_counter(7);
    let mut variables = Vec::new();
    counter.visit_preorder(&mut |term| {
        if let Term::Variable { name, sort } = term {
            variables.push((name.clone(), sort.as_ref().map(|sort| sort.name.clone())));
        }
    });
    assert_eq!(
        variables,
        vec![
            ("_KrsCounter7".to_owned(), Some("Int".to_owned())),
            ("?KrsCounter7".to_owned(), Some("Int".to_owned())),
        ]
    );
}

fn node(key: &str) -> NodeOrigin {
    krs_ir::testing::origin(key)
}

fn semantic_id(value: &str) -> SemanticId {
    SemanticId::new(value).unwrap()
}

fn context_alias_id() -> StableItemId {
    krs_ir::testing::item("contexts", "eval", ItemKind::ContextAlias)
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
    let mut loaded = load_with_options(entry, MODULE, &mut resolver, &options)
        .expect("test bootstrap must be preparable");
    loaded
        .definition
        .modules
        .iter_mut()
        .find(|module| module.name == MODULE)
        .expect("test bootstrap module must exist")
        .local_sentences
        .extend(sentences.into_iter().map(std::sync::Arc::new));
    loaded.resolved = ResolvedDefinition::resolve(&loaded.definition)
        .expect("structured test injection must resolve");
    loaded
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
    assert_eq!(
        PORTABLE_PRELUDE_POLICY,
        PortablePreludePolicy::PinnedBuiltinClosure
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Qualifies all structured builtin families in one definition.
fn builtin_map_list_set_and_bytes_terms_map_structurally_and_infer_imports() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let int =
        |key, value| DefinitionTerm::token(node(key), DefinitionSortRef::int(), value).unwrap();
    let id = |key, value| DefinitionTerm::token(node(key), DefinitionSortRef::id(), value).unwrap();
    let addition = DefinitionTerm::application(
        node("schema9.term.add"),
        DefinitionSortRef::int(),
        ApplicationRef::Builtin(BuiltinOperation::IntAdd),
        vec![int("schema9.term.one", "1"), int("schema9.term.two", "2")],
    );
    let item = DefinitionTerm::map(
        node("schema9.term.map-item"),
        MapOperation::Item,
        vec![
            id("schema9.term.key-a", "a"),
            addition.clone(),
            id("schema9.term.key-b", "b"),
            int("schema9.term.three", "3"),
        ],
    );
    let update = DefinitionTerm::map(
        node("schema9.term.map-update"),
        MapOperation::Update,
        vec![
            DefinitionTerm::map(node("schema9.term.empty-map"), MapOperation::Empty, vec![]),
            id("schema9.term.update-key", "a"),
            int("schema9.term.update-value", "4"),
        ],
    );

    let native_addition = adapter
        .term(&addition, MODULE, 0, Vec::new(), TermContext::Normal, None)
        .unwrap();
    assert!(matches!(native_addition, Term::Apply { label, arguments }
        if label.name == "_+Int_" && arguments.len() == 2));
    let empty_bytes = DefinitionTerm::application(
        node("schema14.term.empty-bytes"),
        DefinitionSortRef::bytes(),
        ApplicationRef::Builtin(BuiltinOperation::BytesEmpty),
        vec![],
    );
    let native_empty_bytes = adapter
        .term(
            &empty_bytes,
            MODULE,
            0,
            Vec::new(),
            TermContext::Normal,
            None,
        )
        .unwrap();
    assert!(
        matches!(native_empty_bytes, Term::Apply { label, arguments }
        if label.name == ".Bytes_BYTES-HOOKED_Bytes" && arguments.is_empty())
    );
    let bytes_update = DefinitionTerm::application(
        node("schema15.term.bytes-update"),
        DefinitionSortRef::bytes(),
        ApplicationRef::Builtin(BuiltinOperation::BytesUpdate),
        vec![
            empty_bytes.clone(),
            DefinitionTerm::token(
                node("schema15.term.bytes-update.index"),
                DefinitionSortRef::int(),
                "0",
            )
            .unwrap(),
            DefinitionTerm::token(
                node("schema15.term.bytes-update.value"),
                DefinitionSortRef::int(),
                "255",
            )
            .unwrap(),
        ],
    );
    let native_bytes_update = adapter
        .term(
            &bytes_update,
            MODULE,
            0,
            Vec::new(),
            TermContext::Normal,
            None,
        )
        .unwrap();
    assert!(
        matches!(native_bytes_update, Term::Apply { label, arguments }
        if label.name == "_[_<-_]_BYTES-HOOKED_Bytes_Bytes_Int_Int" && arguments.len() == 3)
    );
    let bytes_pad_right = DefinitionTerm::application(
        node("schema15.term.bytes-pad-right"),
        DefinitionSortRef::bytes(),
        ApplicationRef::Builtin(BuiltinOperation::BytesPadRight),
        vec![
            empty_bytes,
            DefinitionTerm::token(
                node("schema15.term.bytes-pad-right.length"),
                DefinitionSortRef::int(),
                "32",
            )
            .unwrap(),
            DefinitionTerm::token(
                node("schema15.term.bytes-pad-right.value"),
                DefinitionSortRef::int(),
                "0",
            )
            .unwrap(),
        ],
    );
    let native_bytes_pad_right = adapter
        .term(
            &bytes_pad_right,
            MODULE,
            0,
            Vec::new(),
            TermContext::Normal,
            None,
        )
        .unwrap();
    assert!(
        matches!(native_bytes_pad_right, Term::Apply { label, arguments }
        if label.name == "padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int" && arguments.len() == 3)
    );
    let bytes_substring = DefinitionTerm::application(
        node("schema26.term.bytes-substring"),
        DefinitionSortRef::bytes(),
        ApplicationRef::Builtin(BuiltinOperation::BytesSubstring),
        vec![
            DefinitionTerm::application(
                node("schema26.term.bytes-substring.value"),
                DefinitionSortRef::bytes(),
                ApplicationRef::Builtin(BuiltinOperation::BytesEmpty),
                vec![],
            ),
            int("schema26.term.bytes-substring.start", "1"),
            int("schema26.term.bytes-substring.end", "3"),
        ],
    );
    let native_bytes_substring = adapter
        .term(
            &bytes_substring,
            MODULE,
            0,
            Vec::new(),
            TermContext::Normal,
            None,
        )
        .unwrap();
    assert!(
        matches!(native_bytes_substring, Term::Apply { label, arguments }
        if label.name == "substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int" && arguments.len() == 3)
    );
    let native_item = adapter
        .term(&item, MODULE, 0, Vec::new(), TermContext::Normal, None)
        .unwrap();
    assert!(matches!(native_item, Term::Apply { label, arguments }
        if label.name == "_Map_"
            && matches!(arguments.as_slice(), [Term::Apply { label: left, .. }, Term::Apply { label: right, .. }]
                if left.name == "_|->_" && right.name == "_|->_")));
    let native_update = adapter
        .term(&update, MODULE, 0, Vec::new(), TermContext::Normal, None)
        .unwrap();
    assert!(matches!(native_update, Term::Apply { label, arguments }
        if label.name == "Map:update"
            && matches!(arguments.first(), Some(Term::Apply { label, arguments })
                if label.name == ".Map" && arguments.is_empty())));
    let map_get = DefinitionTerm::typed_map(
        node("schema16.term.map-get"),
        DefinitionSortRef::int(),
        MapOperation::Get,
        vec![
            DefinitionTerm::map(node("schema16.term.get-map"), MapOperation::Empty, vec![]),
            id("schema16.term.get-key", "a"),
        ],
    );
    let native_map_get = adapter
        .term(&map_get, MODULE, 0, Vec::new(), TermContext::Normal, None)
        .unwrap();
    assert!(matches!(native_map_get, Term::Apply { label, arguments }
        if label.name == "project:Int"
            && matches!(arguments.as_slice(), [Term::Apply { label, arguments }]
                if label.name == "Map:lookup" && arguments.len() == 2)));
    let map_in_keys = DefinitionTerm::typed_map(
        node("schema16.term.map-in-keys"),
        DefinitionSortRef::bool(),
        MapOperation::InKeys,
        vec![
            id("schema16.term.in-keys-key", "a"),
            DefinitionTerm::map(
                node("schema16.term.in-keys-map"),
                MapOperation::Empty,
                vec![],
            ),
        ],
    );
    let native_map_in_keys = adapter
        .term(
            &map_in_keys,
            MODULE,
            0,
            Vec::new(),
            TermContext::Normal,
            None,
        )
        .unwrap();
    assert!(
        matches!(native_map_in_keys, Term::Apply { label, arguments }
        if label.name == "_in_keys(_)_MAP_Bool_KItem_Map" && arguments.len() == 2)
    );

    let set_empty = DefinitionTerm::set(
        node("schema16.term.empty-set"),
        DefinitionSortRef::set(),
        SetOperation::Empty,
        vec![],
    );
    let set_item = DefinitionTerm::set(
        node("schema16.term.set-item"),
        DefinitionSortRef::set(),
        SetOperation::Item,
        vec![int("schema16.term.set-value", "7")],
    );
    let set_concat = DefinitionTerm::set(
        node("schema16.term.set-concat"),
        DefinitionSortRef::set(),
        SetOperation::Concat,
        vec![set_item, set_empty],
    );
    let set_contains = DefinitionTerm::set(
        node("schema16.term.set-contains"),
        DefinitionSortRef::bool(),
        SetOperation::Contains,
        vec![int("schema16.term.set-member", "7"), set_concat],
    );
    let native_set_contains = adapter
        .term(
            &set_contains,
            MODULE,
            0,
            Vec::new(),
            TermContext::Normal,
            None,
        )
        .unwrap();
    assert!(
        matches!(native_set_contains, Term::Apply { label, arguments }
        if label.name == "Set:in"
            && matches!(arguments.get(1), Some(Term::Apply { label, .. }) if label.name == "_Set_"))
    );

    let list_empty = DefinitionTerm::list(
        node("schema11.term.empty-list"),
        DefinitionSortRef::list(),
        ListOperation::Empty,
        vec![],
    );
    let list_item = DefinitionTerm::list(
        node("schema11.term.list-item"),
        DefinitionSortRef::list(),
        ListOperation::Item,
        vec![int("schema11.term.list-value", "7")],
    );
    let list_concat = DefinitionTerm::list(
        node("schema11.term.list-concat"),
        DefinitionSortRef::list(),
        ListOperation::Concat,
        vec![list_item.clone(), list_empty.clone()],
    );
    let list_get = DefinitionTerm::list(
        node("schema11.term.list-get"),
        DefinitionSortRef::int(),
        ListOperation::Get,
        vec![list_concat.clone(), int("schema11.term.list-index", "0")],
    );
    let list_update = DefinitionTerm::list(
        node("schema11.term.list-update"),
        DefinitionSortRef::list(),
        ListOperation::Update,
        vec![
            list_concat.clone(),
            int("schema11.term.list-update-index", "0"),
            int("schema11.term.list-update-value", "8"),
        ],
    );
    let list_size = DefinitionTerm::list(
        node("schema11.term.list-size"),
        DefinitionSortRef::int(),
        ListOperation::Size,
        vec![list_concat],
    );
    let list_make = DefinitionTerm::list(
        node("schema27.term.list-make"),
        DefinitionSortRef::list(),
        ListOperation::Make,
        vec![
            int("schema27.term.list-make-length", "3"),
            int("schema27.term.list-make-value", "7"),
        ],
    );
    let list_range = DefinitionTerm::list(
        node("schema25.term.list-range"),
        DefinitionSortRef::list(),
        ListOperation::Range,
        vec![
            list_empty.clone(),
            int("schema25.term.list-range-front", "1"),
            int("schema25.term.list-range-back", "2"),
        ],
    );
    let list_update_all = DefinitionTerm::list(
        node("schema25.term.list-update-all"),
        DefinitionSortRef::list(),
        ListOperation::UpdateAll,
        vec![
            list_empty.clone(),
            int("schema25.term.list-update-all-index", "1"),
            list_empty,
        ],
    );
    let native_list_get = adapter
        .term(&list_get, MODULE, 0, Vec::new(), TermContext::Normal, None)
        .unwrap();
    assert!(matches!(native_list_get, Term::Apply { label, arguments }
        if label.name == "project:Int"
            && matches!(arguments.as_slice(), [Term::Apply { label, arguments }]
                if label.name == "List:get"
                    && matches!(arguments.first(), Some(Term::Apply { label, .. })
                        if label.name == "_List_"))));
    let native_list_update = adapter
        .term(
            &list_update,
            MODULE,
            0,
            Vec::new(),
            TermContext::Normal,
            None,
        )
        .unwrap();
    assert!(
        matches!(native_list_update, Term::Apply { label, arguments }
        if label.name == "List:set" && arguments.len() == 3)
    );
    let native_list_size = adapter
        .term(&list_size, MODULE, 0, Vec::new(), TermContext::Normal, None)
        .unwrap();
    assert!(matches!(native_list_size, Term::Apply { label, arguments }
        if label.name == "sizeList" && arguments.len() == 1));
    let native_list_make = adapter
        .term(&list_make, MODULE, 0, Vec::new(), TermContext::Normal, None)
        .unwrap();
    assert!(matches!(native_list_make, Term::Apply { label, arguments }
        if label.name == "makeList(_,_)_LIST_List_Int_KItem" && arguments.len() == 2));
    let native_list_range = adapter
        .term(
            &list_range,
            MODULE,
            0,
            Vec::new(),
            TermContext::Normal,
            None,
        )
        .unwrap();
    assert!(matches!(native_list_range, Term::Apply { label, arguments }
        if label.name == "List:range" && arguments.len() == 3));
    let native_list_update_all = adapter
        .term(
            &list_update_all,
            MODULE,
            0,
            Vec::new(),
            TermContext::Normal,
            None,
        )
        .unwrap();
    assert!(
        matches!(native_list_update_all, Term::Apply { label, arguments }
        if label.name == "updateList(_,_,_)_LIST_List_List_Int_List"
            && arguments.len() == 3)
    );

    let rewrite = DefinitionTerm::rewrite(
        node("schema9.term.map-rewrite"),
        DefinitionSortRef::map(),
        item,
        update,
    )
    .unwrap();
    let condition = DefinitionTerm::application(
        node("schema9.term.not"),
        DefinitionSortRef::bool(),
        ApplicationRef::Builtin(BuiltinOperation::BoolNot),
        vec![
            DefinitionTerm::token(node("schema9.term.true"), DefinitionSortRef::bool(), "true")
                .unwrap(),
        ],
    );
    let rule = RuleSentence::new(
        node("schema9.rule.map"),
        LabelIdentity::new(LabelId::new("schema9.rule.map").unwrap(), "schema9-map").unwrap(),
        SentenceKind::Transition,
        Vec::new(),
        rewrite,
    )
    .unwrap()
    .with_requires(Some(DefinitionRuleCondition::new(
        node("schema9.rule.map.requires"),
        condition,
    )))
    .unwrap();
    let module = DefinitionModule::new(
        node("schema9.module.builtins"),
        ModuleId::new("SCHEMA9-BUILTINS").unwrap(),
        Vec::new(),
        Vec::new(),
        vec![DefinitionSentence::Rule(rule)],
    );
    assert_eq!(
        module_builtin_imports(&module),
        ["BOOL", "ID-SYNTAX", "INT", "MAP"]
            .into_iter()
            .map(str::to_owned)
            .collect()
    );
}

#[test]
fn pinned_native_prelude_exposes_the_collection_labels_used_by_the_adapter() {
    let adapted = adapt_definition(&smoke_definition()).unwrap();
    let loaded = prepare_definition(adapted.definition, Backend::Llvm).unwrap();
    let labels = loaded
        .definition
        .modules
        .iter()
        .flat_map(|module| module.local_sentences.iter())
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.as_str()),
            _ => None,
        })
        .collect::<std::collections::BTreeSet<_>>();
    for expected in [
        "Map:lookup",
        "_in_keys(_)_MAP_Bool_KItem_Map",
        ".Set",
        "SetItem",
        "_Set_",
        "_|Set__SET_Set_Set_Set",
        "Set:in",
        "makeList(_,_)_LIST_List_Int_KItem",
    ] {
        assert!(
            labels.contains(expected),
            "missing native prelude label {expected}"
        );
    }
    let update_all_labels = loaded
        .definition
        .modules
        .iter()
        .flat_map(|module| module.local_sentences.iter())
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if attributes.get_str("hook") == Some("LIST.updateAll") => Some(label.name.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        update_all_labels,
        ["updateList(_,_,_)_LIST_List_List_Int_List"]
    );
}

#[test]
fn pinned_native_prelude_evaluates_set_union() {
    let artifacts = compile_definition(&smoke_definition(), CompileOptions::default()).unwrap();
    let mut backend = NativeBackend::new(
        &artifacts.definition_kore,
        "SMOKE",
        BackendOptions::default(),
    )
    .unwrap();
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let item = |value: i32| {
        format!(
            "LblSetItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(\\dv{{SortInt{{}}}}(\"{value}\")))"
        )
    };
    for (right, expected_items) in [(1, 1), (2, 2)] {
        let union = DefinitionTerm::set(
            node("set.union.execution"),
            DefinitionSortRef::set(),
            SetOperation::Union,
            [1, right]
                .into_iter()
                .map(|value| {
                    DefinitionTerm::set(
                        node("set.item.execution"),
                        DefinitionSortRef::set(),
                        SetOperation::Item,
                        vec![
                            DefinitionTerm::token(
                                node("set.value.execution"),
                                DefinitionSortRef::int(),
                                value.to_string(),
                            )
                            .unwrap(),
                        ],
                    )
                })
                .collect(),
        );
        let lowered = adapter
            .term(&union, MODULE, 0, Vec::new(), TermContext::Normal, None)
            .unwrap();
        assert!(
            matches!(lowered, Term::Apply { label, .. } if label.name == "_|Set__SET_Set_Set_Set")
        );
        let pattern = format!(
            "Lbl'UndsPipe'Set'UndsUnds'SET'Unds'Set'Unds'Set'Unds'Set{{}}({}, {})",
            item(1),
            item(right)
        );
        let state: serde_json::Value = serde_json::from_str(
            &k_rust::kore::json::to_string(&parse_pattern(&pattern).unwrap()).unwrap(),
        )
        .unwrap();
        let result = backend
            .execute(ExecuteRequest {
                state,
                ..ExecuteRequest::default()
            })
            .unwrap();
        assert_eq!(result.leaves.len(), 1, "{result:#?}");
        let rendered = result.leaves[0].state.to_string();
        assert!(
            !rendered.contains("Pipe"),
            "union remained unevaluated: {rendered}"
        );
        assert_eq!(
            rendered.matches("LblSetItem").count(),
            expected_items,
            "{rendered}"
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn grammar_items_attributes_and_group_sentences_map_structurally() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let application_group = ProductionGroupId::new("group.application").unwrap();
    let atom_group = ProductionGroupId::new("group.atom").unwrap();
    adapter
        .groups
        .insert(application_group.clone(), "application".to_owned());
    adapter.groups.insert(atom_group.clone(), "atom".to_owned());
    let left = ProductionFieldId::new("left").unwrap();
    let right = ProductionFieldId::new("right").unwrap();
    let production = ProductionSentence::new(
        node("schema9.production.apply"),
        symbol(
            "schema9.production.apply",
            "applyTwice",
            SymbolKind::Production,
        ),
        DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
        vec![
            IrProductionItem::terminal(node("schema9.production.apply.open"), "twice(").unwrap(),
            IrProductionItem::non_terminal(
                node("schema9.production.apply.left"),
                left,
                DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
            ),
            IrProductionItem::terminal(node("schema9.production.apply.comma"), ",").unwrap(),
            IrProductionItem::non_terminal(
                node("schema9.production.apply.right"),
                right.clone(),
                DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
            ),
            IrProductionItem::terminal(node("schema9.production.apply.close"), ")").unwrap(),
        ],
        vec![
            DefinitionProductionAttribute::Group {
                origin: node("schema9.production.apply.group"),
                group: application_group.clone(),
            },
            DefinitionProductionAttribute::Format {
                origin: node("schema9.production.apply.format"),
                fragments: vec![
                    FormatFragment::Item(1),
                    FormatFragment::Item(2),
                    FormatFragment::Literal(" ".to_owned()),
                    FormatFragment::Item(4),
                    FormatFragment::Item(5),
                ],
            },
            DefinitionProductionAttribute::Strictness {
                origin: node("schema9.production.apply.strictness"),
                kind: StrictnessKind::SeqStrict,
                using: None,
                fields: vec![ProductionFieldReference::new(
                    node("schema9.production.apply.strict-field"),
                    right,
                )],
                result_sort: ProductionResultSort::new(
                    node("schema9.production.apply.result-sort"),
                    DefinitionSortRef::declared(SymbolId::new("sort.kresult").unwrap()),
                ),
            },
        ],
    )
    .unwrap();
    let native = adapter.production(&production, MODULE, 0).unwrap();
    let Sentence::Production {
        label: Some(label),
        items,
        attributes,
        ..
    } = native
    else {
        panic!("grammar production must remain native")
    };
    assert_eq!(label.name, "applyTwice");
    assert!(
        matches!(items[1], ProductionItem::NonTerminal { ref name, .. }
        if name.as_deref() == Some("left"))
    );
    assert!(
        matches!(items[3], ProductionItem::NonTerminal { ref name, .. }
        if name.as_deref() == Some("right"))
    );
    assert_eq!(attributes.get_str("group"), Some("application"));
    assert_eq!(attributes.get_str("format"), Some("%1%2 %4%5"));
    assert_eq!(attributes.get_str("seqstrict"), Some("2"));
    assert_eq!(attributes.get_str("result"), Some("KResult"));

    let token = ProductionSentence::new(
        node("schema9.production.integer-token"),
        symbol(
            "schema9.production.integer-token",
            "integerToken",
            SymbolKind::Production,
        ),
        DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
        vec![
            IrProductionItem::regex_terminal(
                node("schema9.production.integer-token.regex"),
                Some("[A-Za-z0-9_]".to_owned()),
                "[0-9]+",
                None,
            )
            .unwrap(),
        ],
        vec![DefinitionProductionAttribute::Token {
            origin: node("schema9.production.integer-token.attribute"),
            lexical_precedence: Some(120),
        }],
    )
    .unwrap();
    let native_token = adapter.production(&token, MODULE, 1).unwrap();
    assert!(
        matches!(native_token, Sentence::Production { label: None, items, attributes, .. }
        if matches!(items.as_slice(), [ProductionItem::RegexTerminal { regex, .. }] if regex == "[0-9]+")
            && attributes.get("token").is_some()
            && attributes.get_str("prec") == Some("120"))
    );

    let precedence = DefinitionSentence::Precedence(
        PrecedenceRelation::new(
            node("schema9.precedence"),
            vec![atom_group.clone()],
            vec![application_group.clone()],
        )
        .unwrap(),
    );
    assert!(matches!(adapter.sentence(&precedence, MODULE, 2).unwrap(),
        Sentence::SyntaxPriority { priorities, .. }
            if priorities == vec![vec!["atom".to_owned()], vec!["application".to_owned()]]));
    let associativity = DefinitionSentence::Associativity(
        GroupAssociativitySentence::new(
            node("schema9.associativity"),
            GroupAssociativity::Left,
            vec![application_group],
        )
        .unwrap(),
    );
    assert!(
        matches!(adapter.sentence(&associativity, MODULE, 3).unwrap(),
        Sentence::SyntaxAssociativity { tags, .. } if tags == vec!["application"])
    );
}

#[test]
fn fixed_configuration_preserves_config_variables_and_cell_properties() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let cell = SymbolId::new("schema9.cell.k").unwrap();
    let program = semantic_id("program");
    let value_sort = DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap());
    let initializer = DefinitionTerm::k_sequence(
        node("schema9.configuration.initializer.sequence"),
        value_sort.clone(),
        vec![DefinitionTerm::variable(
            node("schema9.configuration.initializer.program"),
            value_sort.clone(),
            program.clone(),
        )],
    );
    let fixed = FixedConfiguration::new(
        node("schema9.configuration"),
        semantic_id("configuration.machine"),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                node("schema9.configuration.cell.k"),
                cell.clone(),
                "k",
                vec![
                    CellAttribute::color(node("schema9.configuration.cell.k.color"), "yellow")
                        .unwrap(),
                ],
                DefinitionSortRef::k_sequence(),
            )
            .unwrap(),
        ],
        node("schema9.configuration.initializer"),
        semantic_id("initializer.machine"),
        vec![
            FixedConfigurationVariable::new(
                node("schema9.configuration.variable.program"),
                program,
                "PGM",
                value_sort,
                true,
            )
            .unwrap(),
        ],
        vec![FixedInitializerCell::term(
            node("schema9.configuration.initializer.cell.k"),
            cell,
            initializer,
        )],
    )
    .unwrap();
    let native = adapter.configuration(&fixed, MODULE, 0).unwrap();
    let Sentence::Configuration { body, .. } = native else {
        panic!("fixed configuration must remain native")
    };
    let mut saw_program = false;
    let mut saw_program_cast = false;
    let mut property_names = Vec::new();
    body.visit_preorder(&mut |term| {
        if matches!(term, Term::Apply { label, .. } if label.name == "#SemanticCastToValue") {
            saw_program_cast = true;
        }
        if let Term::Token { token, sort } = term {
            if token == "$PGM" && sort.name == "KConfigVar" {
                saw_program = true;
            }
            if sort.name == "#CellName" {
                property_names.push(token.clone());
            }
        }
    });
    assert!(
        saw_program,
        "configuration variables remain native KConfigVar tokens"
    );
    assert!(
        saw_program_cast,
        "configuration variables retain their authored term sort"
    );
    assert!(property_names.iter().any(|name| name == "color"));
    assert!(property_names.iter().any(|name| name == "maincell"));
    assert!(adapter.origins.iter().any(|mapping| {
        mapping.key.as_str() == "schema9.configuration.cell.k"
            && mapping.role == NativeNodeRole::ConfigurationCell
    }));
}

#[test]
fn complete_cell_terms_use_the_pinned_frontend_structured_shape() {
    fn cell_body<'a>(term: &'a Term, expected_label: &str) -> &'a Term {
        let Term::Apply { label, arguments } = term else {
            panic!("cell term must remain an application")
        };
        assert_eq!(label.name, expected_label);
        let [body] = arguments.as_slice() else {
            panic!("leaf cell must carry its complete structured body")
        };
        body
    }

    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let parent = SymbolId::new("schema26.cell.parent").unwrap();
    let left = SymbolId::new("schema26.cell.left").unwrap();
    let right = SymbolId::new("schema26.cell.right").unwrap();
    adapter.cells.extend([
        (parent.clone(), "parent".to_owned()),
        (left.clone(), "left".to_owned()),
        (right.clone(), "right".to_owned()),
    ]);
    let leaf = |key: &str, cell: SymbolId, value: &str| {
        DefinitionTerm::cell(
            node(key),
            DefinitionSortRef::int(),
            cell,
            vec![
                DefinitionTerm::token(
                    node(&format!("{key}.body")),
                    DefinitionSortRef::int(),
                    value,
                )
                .unwrap(),
            ],
        )
    };
    let term = DefinitionTerm::cell(
        node("schema26.cell.parent.term"),
        DefinitionSortRef::int(),
        parent,
        vec![
            leaf("schema26.cell.left.term", left, "1"),
            leaf("schema26.cell.right.term", right, "2"),
        ],
    );
    let native = adapter
        .term(&term, MODULE, 0, Vec::new(), TermContext::Normal, None)
        .unwrap();
    let Term::Apply { label, arguments } = native else {
        panic!("a multi-child parent must remain a complete application")
    };
    assert_eq!(label.name, "<parent>");
    let [left, right] = arguments.as_slice() else {
        panic!("the parent must retain both ordered children")
    };
    assert!(matches!(cell_body(left, "<left>"), Term::Token { token, .. } if token == "1"));
    assert!(matches!(cell_body(right, "<right>"), Term::Token { token, .. } if token == "2"));
}

#[test]
#[allow(clippy::too_many_lines)]
fn claims_and_context_aliases_preserve_native_forms_and_origin_roles() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let universal = semantic_id("_B__krs_0");
    let existential = semantic_id("n");
    let body = DefinitionTerm::rewrite(
        node("schema9.claim.body"),
        DefinitionSortRef::int(),
        DefinitionTerm::token(node("schema9.claim.zero"), DefinitionSortRef::int(), "0").unwrap(),
        DefinitionTerm::variable(
            node("schema9.claim.existential-use"),
            DefinitionSortRef::int(),
            existential.clone(),
        ),
    )
    .unwrap();
    let claim = DefinitionClaim::new(
        node("schema9.claim.modality"),
        ClaimModality::OnePath,
        Some(node("schema9.claim.circularity")),
        vec![DefinitionClaimBinder::new(
            node("schema9.claim.universal"),
            node("schema9.claim.universal.name"),
            universal.clone(),
            node("schema9.claim.universal.sort"),
            DefinitionSortRef::bool(),
        )],
        vec![DefinitionClaimBinder::new(
            node("schema9.claim.existential"),
            node("schema9.claim.existential.name"),
            existential.clone(),
            node("schema9.claim.existential.sort"),
            DefinitionSortRef::int(),
        )],
        Some(DefinitionRuleCondition::new(
            node("schema9.claim.ensures"),
            DefinitionTerm::variable(
                node("schema9.claim.anonymous-use"),
                DefinitionSortRef::bool(),
                universal,
            ),
        )),
    );
    let rule = RuleSentence::new(
        node("schema9.claim"),
        LabelIdentity::new(LabelId::new("schema9.claim").unwrap(), "schema9-claim").unwrap(),
        SentenceKind::Claim,
        Vec::new(),
        body,
    )
    .unwrap()
    .with_claim(Some(claim));
    let native_claim = adapter.rule(&rule, MODULE, 0).unwrap();
    let Sentence::Claim {
        body,
        ensures,
        attributes,
        ..
    } = native_claim
    else {
        panic!("claims must not be downgraded to rules")
    };
    let mut variables = Vec::new();
    body.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term {
            variables.push(name.clone());
        }
    });
    ensures.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term {
            variables.push(name.clone());
        }
    });
    assert!(variables.contains(&"?V6E".to_owned()));
    assert!(variables.contains(&"_B".to_owned()));
    assert!(attributes.get("one-path").is_some());
    assert!(attributes.get("circularity").is_some());
    for role in [
        NativeNodeRole::ClaimBinder(0),
        NativeNodeRole::ClaimBinderName(0),
        NativeNodeRole::ClaimBinderSort(0),
        NativeNodeRole::ClaimBinder(1),
        NativeNodeRole::ClaimModality,
        NativeNodeRole::ClaimCircularity,
        NativeNodeRole::Ensures,
    ] {
        assert!(adapter.origins.iter().any(|mapping| mapping.role == role));
    }

    let here = semantic_id("here");
    let context = ContextAliasSentence::new(
        node("schema9.context"),
        context_alias_id(),
        node("schema9.context.name"),
        "schema9_eval".to_owned(),
        node("schema9.context.here"),
        here.clone(),
        Vec::new(),
        FixedConfigurationPattern::new(
            node("schema9.context.pattern"),
            semantic_id("configuration.machine"),
            vec![FixedCellPattern::new(
                node("schema9.context.cell.k"),
                SymbolId::new("cell.k").unwrap(),
                DefinitionTerm::variable(
                    node("schema9.context.here-use"),
                    DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
                    here,
                ),
                CellContentFrame::KSequenceTail {
                    origin: node("schema9.context.frame"),
                    binding: Some(semantic_id("tail")),
                },
            )],
            Vec::new(),
        )
        .unwrap(),
    );
    let native_context = adapter.context_alias(&context, MODULE, 1).unwrap();
    let Sentence::ContextAlias {
        body, attributes, ..
    } = native_context
    else {
        panic!("context aliases must remain native")
    };
    let mut saw_here = false;
    let mut saw_k_tail = false;
    body.visit_preorder(&mut |term| {
        if matches!(term, Term::Variable { name, .. } if name == "HERE") {
            saw_here = true;
        }
        if matches!(term, Term::Variable { name, sort: Some(sort) }
            if name == &super::variable_name(&semantic_id("tail")) && sort.name == "K")
        {
            saw_k_tail = true;
        }
    });
    assert!(saw_here);
    assert!(saw_k_tail);
    assert_eq!(attributes.get_str("label"), Some("schema9_eval"));
    assert!(attributes.get("cool-like").is_some());
    for role in [
        NativeNodeRole::ContextAliasName,
        NativeNodeRole::ContextAliasHere,
        NativeNodeRole::ContextAliasCell(0),
        NativeNodeRole::ContextAliasFrame(0),
    ] {
        assert!(adapter.origins.iter().any(|mapping| mapping.role == role));
    }
}

#[test]
fn alias_clause_relies_on_aliased_production_propagation() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let body = DefinitionTerm::rewrite(
        node("schema9.alias.body"),
        DefinitionSortRef::int(),
        DefinitionTerm::token(node("schema9.alias.left"), DefinitionSortRef::int(), "0").unwrap(),
        DefinitionTerm::token(node("schema9.alias.right"), DefinitionSortRef::int(), "1").unwrap(),
    )
    .unwrap();
    let rule = RuleSentence::new(
        node("schema9.alias"),
        LabelIdentity::new(LabelId::new("schema9.alias").unwrap(), "schema9-alias").unwrap(),
        SentenceKind::Alias,
        Vec::new(),
        body,
    )
    .unwrap();
    let native = adapter.rule(&rule, MODULE, 0).unwrap();
    let Sentence::Rule { attributes, .. } = native else {
        panic!("static alias clauses remain ordinary native rules")
    };
    assert!(
        attributes.get("alias").is_none(),
        "the frontend propagates alias mode from the root production"
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn definition_ir_maps_structurally_without_frontend_metadata() {
    let adapted = adapt_definition(&smoke_definition()).expect("the smoke IR must adapt");
    let native = adapted.definition();
    assert_eq!(native.main_module, "SMOKE");
    assert_eq!(native.modules.len(), 2);

    let main = native
        .modules
        .iter()
        .find(|module| module.name == "SMOKE")
        .unwrap();
    assert_eq!(main.imports.len(), 2);
    assert!(
        main.imports
            .iter()
            .any(|import| import.name == "MAP" && import.public)
    );
    assert!(
        main.imports
            .iter()
            .any(|import| import.name == "SMOKE-SYNTAX" && import.public)
    );
    assert_eq!(main.attributes.location(), None);

    let configuration = main
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
            && properties.name == "#cellPropertyList"
            && matches!(
                items.as_slice(),
                [Term::Apply { label, arguments }]
                    if label.name == "#SemanticCastToValue"
                        && matches!(arguments.as_slice(), [Term::Token { token, .. }] if token == "$PGM")
            )
    ));

    let rule = main
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule {
                body, attributes, ..
            } => Some((body, attributes)),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        rule.1.get_str("label"),
        Some("SMOKE.ORG-EXAMPLE-SMOKE.rules.foo-to-bar")
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
        .filter_map(|sentence| match &**sentence {
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
    assert_eq!(subsorts, vec![("KResult", "KItem"), ("Value", "KResult")]);

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
        "def.term.init.program",
        "def.rule.foo-to-bar",
        "def.term.rule.rewrite",
        "def.term.rule.foo",
        "def.term.rule.bar",
    ] {
        assert!(
            keys.contains(&expected),
            "missing origin seam for {expected}"
        );
    }
    assert!(adapted.origins().iter().any(|mapping| {
        mapping.key.as_str() == "def.term.rule.bar"
            && matches!(mapping.role, NativeNodeRole::Term(ref path) if path == &[1])
    }));
}

#[test]
fn permanent_structured_compile_uses_the_pinned_compatibility_layer() {
    let artifacts = compile_definition(&smoke_definition(), CompileOptions::default())
        .expect("permanent compilation uses public pinned preparation primitives");
    assert!(!artifacts.definition_kore.is_empty());
    assert!(!artifacts.syntax_definition_kore.is_empty());
}

fn unique_ids(kore: &str) -> std::collections::BTreeSet<String> {
    let definition = parse_definition(kore).expect("compiled KORE must reparse");
    definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            k_rust::kore::ast::Sentence::Axiom { attributes, .. }
            | k_rust::kore::ast::Sentence::Claim { attributes, .. } => Some(attributes),
            _ => None,
        })
        .flat_map(|attributes| &attributes.0)
        .filter_map(|pattern| match pattern {
            KorePattern::Application { symbol, arguments } if symbol.name == "UNIQUE'Unds'ID" => {
                let [KorePattern::String(id)] = arguments.as_slice() else {
                    panic!("UNIQUE_ID must have one string argument")
                };
                Some(id.as_utf8().expect("UNIQUE_ID must be UTF-8").to_owned())
            }
            _ => None,
        })
        .collect()
}

fn macro_unique_ids(macros: &str) -> std::collections::BTreeSet<String> {
    if macros.trim().is_empty() {
        return std::collections::BTreeSet::new();
    }
    unique_ids(&format!("module MACROS []\n{macros}\nendmodule []"))
}

#[test]
fn smoke_relation_covers_emitted_ids_and_authors() {
    let ir = smoke_definition();
    let artifacts = compile_definition(&ir, CompileOptions::default()).unwrap();
    for emitted in [
        &artifacts.definition_kore,
        &artifacts.syntax_definition_kore,
        &artifacts.macros_kore,
    ] {
        assert!(!emitted.contains("krs-source-map"));
    }
    let ids = artifacts
        .sentence_provenance
        .iter()
        .map(|(id, _)| id.to_owned())
        .collect::<std::collections::BTreeSet<_>>();
    let mut emitted_ids = unique_ids(&artifacts.definition_kore);
    emitted_ids.extend(macro_unique_ids(&artifacts.macros_kore));
    assert_eq!(emitted_ids, ids);
    let rule = &ir.modules()[0].sentences()[1];
    let key = rule.origin().key();
    let emitted = artifacts.sentence_provenance.emitted_by(key);
    assert!(!emitted.is_empty());
    for id in emitted {
        let provenance = artifacts.sentence_provenance.get(id).unwrap();
        assert!(provenance.authors().iter().any(|author| matches!(author,
            Author::Krs { origin, .. } if origin == rule.origin()
        )));
    }
    assert!(artifacts.sentence_provenance.iter().any(|(_, provenance)| {
        provenance.authors().is_empty()
            && provenance.generated_by() == Some(GeneratingPass::GenerateSortPredicateRules)
    }));
    assert!(artifacts.sentence_provenance.iter().any(|(_, provenance)| {
        provenance
            .authors()
            .iter()
            .any(|author| matches!(author, Author::Builtin { .. }))
    }));
}

/// The smoke definition with one authored one-path claim, and that claim's origin.
fn smoke_definition_with_claim() -> (DefinitionIr, NodeOrigin) {
    let ir = smoke_definition();
    let main = &ir.modules()[0];
    let value = DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap());
    let term = |key: &str, production: &str| {
        DefinitionTerm::k_sequence(
            node(&format!("{key}.sequence")),
            DefinitionSortRef::declared(SymbolId::new("sort.kitem").unwrap()),
            vec![DefinitionTerm::application(
                node(key),
                value.clone(),
                ApplicationRef::Declared(SymbolId::new(production).unwrap()),
                Vec::new(),
            )],
        )
    };
    let body = FixedConfigurationRewrite::new(
        node("def.claim.rewrite"),
        semantic_id("configuration.machine"),
        vec![FixedCellClause::new(
            node("def.claim.cell"),
            SymbolId::new("cell.k").unwrap(),
            term("def.claim.foo", "production.foo"),
            CellPost::Replace {
                term: term("def.claim.bar", "production.bar"),
            },
            CellContentFrame::Exact,
        )],
        Vec::new(),
    )
    .unwrap();
    let claim = DefinitionSentence::Rule(
        RuleSentence::new_configuration(
            node("def.claim"),
            LabelIdentity::new(
                LabelId::new("claim.foo-to-bar").unwrap(),
                "ORG-EXAMPLE-SMOKE.claims.foo-to-bar",
            )
            .unwrap(),
            SentenceKind::Claim,
            Vec::new(),
            body,
        )
        .with_claim(Some(DefinitionClaim::new(
            node("def.claim.modality"),
            ClaimModality::OnePath,
            None,
            Vec::new(),
            Vec::new(),
            None,
        ))),
    );
    let origin = claim.origin().clone();
    let mut sentences = main.sentences().to_vec();
    sentences.push(claim);
    let main = DefinitionModule::new(
        main.origin().clone(),
        main.id().clone(),
        main.imports().iter().cloned().collect(),
        main.production_groups().to_vec(),
        sentences,
    );
    let ir = DefinitionIr::new(
        ir.main_module().clone(),
        vec![main, ir.modules()[1].clone()],
    )
    .unwrap();
    (ir, origin)
}

#[test]
fn authored_claim_has_an_emitted_identity_with_its_origin() {
    let (ir, origin) = smoke_definition_with_claim();
    let artifacts = compile_definition(
        &ir,
        CompileOptions {
            backend: Backend::Haskell,
            ..CompileOptions::default()
        },
    )
    .unwrap();
    assert_eq!(artifacts.omitted_claims, 0);
    let relation_ids = artifacts
        .sentence_provenance
        .iter()
        .map(|(id, _)| id.to_owned())
        .collect::<std::collections::BTreeSet<_>>();
    let mut emitted_ids = unique_ids(&artifacts.definition_kore);
    emitted_ids.extend(macro_unique_ids(&artifacts.macros_kore));
    assert_eq!(relation_ids, emitted_ids);
    let ids = artifacts.sentence_provenance.emitted_by(origin.key());
    assert!(!ids.is_empty());
    for id in ids {
        assert!(artifacts.sentence_provenance.get(id).unwrap().authors().iter().any(|author| {
            matches!(author, Author::Krs { kind: InputSentenceKind::Claim, origin: actual, .. } if actual == &origin)
        }));
    }
}

#[test]
fn only_the_haskell_backend_proves_claims() {
    for backend in Backend::ALL {
        assert_eq!(backend.proves_claims(), backend == Backend::Haskell);
    }
}

#[test]
fn llvm_compilation_omits_claims_and_keeps_provenance_consistent() {
    let (ir, origin) = smoke_definition_with_claim();
    let adapted = adapt_definition_for(&ir, Backend::Llvm).unwrap();
    assert_eq!(adapted.omitted_claims(), 1);
    assert!(adapted.definition().modules.iter().all(|module| {
        module
            .local_sentences
            .iter()
            .all(|sentence| !matches!(**sentence, Sentence::Claim { .. }))
    }));
    assert!(
        adapted
            .origins()
            .iter()
            .all(|mapping| mapping.key != *origin.key())
    );

    let artifacts = compile_definition(&ir, CompileOptions::default())
        .expect("a claim does not prevent concrete compilation");
    assert_eq!(artifacts.omitted_claims, 1);
    assert!(
        artifacts
            .sentence_provenance
            .emitted_by(origin.key())
            .is_empty()
    );
    let relation_ids = artifacts
        .sentence_provenance
        .iter()
        .map(|(id, _)| id.to_owned())
        .collect::<std::collections::BTreeSet<_>>();
    let mut emitted_ids = unique_ids(&artifacts.definition_kore);
    emitted_ids.extend(macro_unique_ids(&artifacts.macros_kore));
    assert_eq!(relation_ids, emitted_ids);
}

#[test]
fn equal_content_rules_share_identity_and_keep_both_authors() {
    let ir = smoke_definition();
    let main = &ir.modules()[0];
    let DefinitionSentence::Rule(first) = &main.sentences()[1] else {
        panic!("smoke main must contain a rule")
    };
    let second = DefinitionSentence::Rule(
        RuleSentence::new(
            node("def.rule.foo-to-bar-again"),
            LabelIdentity::new(
                LabelId::new("rule.foo-to-bar-again").unwrap(),
                "ORG-EXAMPLE-SMOKE.rules.foo-to-bar-again",
            )
            .unwrap(),
            first.kind(),
            Vec::new(),
            DefinitionTerm::rewrite(
                node("def.term.rule.rewrite-again"),
                DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
                DefinitionTerm::application(
                    node("def.term.rule.foo-again"),
                    DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
                    ApplicationRef::Declared(SymbolId::new("production.foo").unwrap()),
                    Vec::new(),
                ),
                DefinitionTerm::application(
                    node("def.term.rule.bar-again"),
                    DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
                    ApplicationRef::Declared(SymbolId::new("production.bar").unwrap()),
                    Vec::new(),
                ),
            )
            .unwrap(),
        )
        .unwrap(),
    );
    let mut main_sentences = main.sentences().to_vec();
    main_sentences.push(second);
    let main = DefinitionModule::new(
        main.origin().clone(),
        main.id().clone(),
        main.imports().iter().cloned().collect(),
        main.production_groups().to_vec(),
        main_sentences,
    );
    let ir = DefinitionIr::new(
        ir.main_module().clone(),
        vec![main, ir.modules()[1].clone()],
    )
    .unwrap();
    let artifacts = compile_definition(&ir, CompileOptions::default()).unwrap();
    let first_key = SourceMapKey::new("def.rule.foo-to-bar").unwrap();
    let second_key = SourceMapKey::new("def.rule.foo-to-bar-again").unwrap();
    let first_ids = artifacts.sentence_provenance.emitted_by(&first_key);
    let second_ids = artifacts.sentence_provenance.emitted_by(&second_key);
    assert_eq!(first_ids, second_ids);
    assert_eq!(first_ids.len(), 1);
    let authors = artifacts
        .sentence_provenance
        .get(&first_ids[0])
        .unwrap()
        .authors();
    let krs_keys = authors
        .iter()
        .filter_map(|author| match author {
            Author::Krs { origin, .. } => Some(origin.key().as_str()),
            Author::Builtin { .. } => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(krs_keys, [first_key.as_str(), second_key.as_str()]);
}

#[test]
fn strict_production_has_multiple_emitted_ids() {
    let ir = smoke_definition();
    let syntax = &ir.modules()[1];
    let value = DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap());
    let strict = DefinitionSentence::Production(
        ProductionSentence::new(
            node("def.production.strict"),
            symbol("production.strict", "Lblstrict", SymbolKind::Production),
            value.clone(),
            vec![
                IrProductionItem::terminal(node("def.production.strict.open"), "strict(").unwrap(),
                IrProductionItem::non_terminal(
                    node("def.production.strict.field"),
                    ProductionFieldId::new("argument").unwrap(),
                    value,
                ),
                IrProductionItem::terminal(node("def.production.strict.close"), ")").unwrap(),
            ],
            vec![DefinitionProductionAttribute::Strictness {
                origin: node("def.production.strict.attribute"),
                kind: StrictnessKind::Strict,
                using: None,
                fields: vec![ProductionFieldReference::new(
                    node("def.production.strict.selected"),
                    ProductionFieldId::new("argument").unwrap(),
                )],
                result_sort: ProductionResultSort::new(
                    node("def.production.strict.result"),
                    DefinitionSortRef::declared(SymbolId::new("sort.kresult").unwrap()),
                ),
            }],
        )
        .unwrap(),
    );
    let strict_origin = strict.origin().clone();
    let mut syntax_sentences = syntax.sentences().to_vec();
    syntax_sentences.push(strict);
    let syntax = DefinitionModule::new(
        syntax.origin().clone(),
        syntax.id().clone(),
        syntax.imports().iter().cloned().collect(),
        syntax.production_groups().to_vec(),
        syntax_sentences,
    );
    let ir = DefinitionIr::new(
        ir.main_module().clone(),
        vec![ir.modules()[0].clone(), syntax],
    )
    .unwrap();
    let artifacts = compile_definition(&ir, CompileOptions::default()).unwrap();
    let ids = artifacts
        .sentence_provenance
        .emitted_by(strict_origin.key());
    assert!(ids.len() >= 2);
    for id in ids {
        assert!(artifacts.sentence_provenance.get(id).unwrap().authors().iter().any(|author| {
            matches!(author, Author::Krs { origin, kind: InputSentenceKind::Production, .. } if origin == &strict_origin)
        }));
    }
}

#[test]
fn two_cell_configuration_has_multiple_emitted_ids() {
    let ir = smoke_definition();
    let main = &ir.modules()[0];
    let program = semantic_id("program");
    let k_cell = SymbolId::new("cell.k").unwrap();
    let state_cell = SymbolId::new("cell.state").unwrap();
    let value = DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap());
    let configuration = DefinitionSentence::Configuration(
        FixedConfiguration::new(
            node("def.configuration.two-cell"),
            semantic_id("configuration.machine"),
            ConfigurationRoot::GeneratedTop,
            vec![
                FixedCell::leaf(
                    node("def.cell.k.two-cell"),
                    k_cell.clone(),
                    "k",
                    Vec::new(),
                    DefinitionSortRef::k_sequence(),
                )
                .unwrap(),
                FixedCell::leaf(
                    node("def.cell.state"),
                    state_cell.clone(),
                    "state",
                    Vec::new(),
                    value.clone(),
                )
                .unwrap(),
            ],
            node("def.initializer.two-cell"),
            semantic_id("initializer.machine"),
            vec![
                FixedConfigurationVariable::new(
                    node("def.initializer.program.two-cell"),
                    program.clone(),
                    "PGM",
                    value.clone(),
                    true,
                )
                .unwrap(),
            ],
            vec![
                FixedInitializerCell::term(
                    node("def.initializer.k.two-cell"),
                    k_cell,
                    DefinitionTerm::k_sequence(
                        node("def.initializer.k.sequence.two-cell"),
                        DefinitionSortRef::declared(SymbolId::new("sort.kitem").unwrap()),
                        vec![DefinitionTerm::variable(
                            node("def.initializer.program.term.two-cell"),
                            value.clone(),
                            program,
                        )],
                    ),
                ),
                FixedInitializerCell::term(
                    node("def.initializer.state"),
                    state_cell,
                    DefinitionTerm::application(
                        node("def.initializer.state.foo"),
                        value,
                        ApplicationRef::Declared(SymbolId::new("production.foo").unwrap()),
                        Vec::new(),
                    ),
                ),
            ],
        )
        .unwrap(),
    );
    let origin = configuration.origin().clone();
    let mut sentences = main.sentences().to_vec();
    sentences[0] = configuration;
    let main = DefinitionModule::new(
        main.origin().clone(),
        main.id().clone(),
        main.imports().iter().cloned().collect(),
        main.production_groups().to_vec(),
        sentences,
    );
    let ir = DefinitionIr::new(
        ir.main_module().clone(),
        vec![main, ir.modules()[1].clone()],
    )
    .unwrap();
    let artifacts = compile_definition(&ir, CompileOptions::default()).unwrap();
    let ids = artifacts.sentence_provenance.emitted_by(origin.key());
    assert!(ids.len() >= 2);
    for id in ids {
        assert!(artifacts.sentence_provenance.get(id).unwrap().authors().iter().any(|author| {
            matches!(author, Author::Krs { origin: actual, kind: InputSentenceKind::Configuration, .. } if actual == &origin)
        }));
    }
}

#[test]
fn provenance_join_rejects_broken_input_addresses() {
    use std::collections::BTreeMap;

    use k_rust::kompile::EmittedSentenceProvenance;

    let ir = smoke_definition();
    let adapted = adapt_definition(&ir).unwrap();
    let loaded = prepare_definition(adapted.definition().clone(), Backend::Llvm).unwrap();
    let address = InputAddress {
        input: InputSpace::Structured,
        module: "SMOKE".to_owned(),
        index: 1,
    };
    let relation = |address: InputAddress, kind: InputSentenceKind| {
        BTreeMap::from([(
            "rule-id".to_owned(),
            EmittedSentenceProvenance {
                input_addresses: vec![address.clone()],
                input_sentence_kinds: BTreeMap::from([(address, kind)]),
                generated_by: None,
            },
        )])
    };
    let valid = relation(address.clone(), InputSentenceKind::Rule);
    assert!(super::join_sentence_provenance(&ir, &adapted, &loaded, &valid).is_ok());

    let mut missing = adapted.clone();
    missing.origins.retain(|mapping| {
        !(mapping.module == "SMOKE"
            && mapping.sentence_index == Some(1)
            && mapping.role == NativeNodeRole::Sentence)
    });
    assert_eq!(
        super::join_sentence_provenance(&ir, &missing, &loaded, &valid),
        Err(ProvenanceError::MissingSentenceMapping(address.clone()))
    );

    let mut duplicate = adapted.clone();
    let mapping = duplicate
        .origins
        .iter()
        .find(|mapping| {
            mapping.module == "SMOKE"
                && mapping.sentence_index == Some(1)
                && mapping.role == NativeNodeRole::Sentence
        })
        .unwrap()
        .clone();
    duplicate.origins.push(mapping);
    assert_eq!(
        super::join_sentence_provenance(&ir, &duplicate, &loaded, &valid),
        Err(ProvenanceError::DuplicateSentenceMapping {
            module: "SMOKE".to_owned(),
            index: 1,
        })
    );

    let compile_address = InputAddress {
        input: InputSpace::Compile,
        ..address.clone()
    };
    assert_eq!(
        super::join_sentence_provenance(
            &ir,
            &adapted,
            &loaded,
            &relation(compile_address.clone(), InputSentenceKind::Rule),
        ),
        Err(ProvenanceError::LossyCompileAddress(compile_address))
    );

    assert_eq!(
        super::join_sentence_provenance(
            &ir,
            &adapted,
            &loaded,
            &relation(address.clone(), InputSentenceKind::Production),
        ),
        Err(ProvenanceError::KindMismatch {
            address: address.clone(),
            expected: InputSentenceKind::Rule,
            actual: InputSentenceKind::Production,
        })
    );

    let out_of_range = InputAddress {
        index: 100,
        ..address
    };
    assert_eq!(
        super::join_sentence_provenance(
            &ir,
            &adapted,
            &loaded,
            &relation(out_of_range.clone(), InputSentenceKind::Rule),
        ),
        Err(ProvenanceError::IndexOutOfRange(out_of_range))
    );
}

#[test]
fn provenance_join_uses_mapping_key_for_ir_sentence_kind() {
    use std::collections::BTreeMap;

    use k_rust::kompile::EmittedSentenceProvenance;

    let ir = smoke_definition();
    let adapted = adapt_definition(&ir).unwrap();
    let loaded = prepare_definition(adapted.definition().clone(), Backend::Llvm).unwrap();
    let main = &ir.modules()[0];
    let mut shifted_sentences = main.sentences().to_vec();
    shifted_sentences.push(DefinitionSentence::SyntaxSort(
        SyntaxSortSentence::new(
            node("def.middle"),
            symbol("sort.middle", "Middle", SymbolKind::Sort),
        )
        .unwrap(),
    ));
    let shifted_main = DefinitionModule::new(
        main.origin().clone(),
        main.id().clone(),
        main.imports().iter().cloned().collect(),
        main.production_groups().to_vec(),
        shifted_sentences,
    );
    let shifted_ir = DefinitionIr::new(
        ir.main_module().clone(),
        vec![shifted_main, ir.modules()[1].clone()],
    )
    .unwrap();
    assert_eq!(
        shifted_ir.modules()[0].sentences()[2].origin().key(),
        main.sentences()[1].origin().key()
    );
    let address = InputAddress {
        input: InputSpace::Structured,
        module: "SMOKE".to_owned(),
        index: 1,
    };
    let relation = BTreeMap::from([(
        "rule-id".to_owned(),
        EmittedSentenceProvenance {
            input_addresses: vec![address.clone()],
            input_sentence_kinds: BTreeMap::from([(address, InputSentenceKind::Rule)]),
            generated_by: None,
        },
    )]);
    assert!(super::join_sentence_provenance(&shifted_ir, &adapted, &loaded, &relation).is_ok());
}

#[test]
fn permanent_structured_compile_replaces_the_bootstrap_default_configuration() {
    let definition = smoke_definition_with_cell(SentenceKind::Transition, "instrs");
    let adapted = adapt_definition(&definition).unwrap();
    let loaded = prepare_definition(adapted.definition, Backend::Llvm).unwrap();
    assert!(
        loaded
            .definition
            .modules
            .iter()
            .all(|module| module.name != "DEFAULT-CONFIGURATION")
    );
    assert!(loaded.definition.modules.iter().all(|module| {
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
fn transition_sentence_is_preserved_as_a_native_rule() {
    let adapted = adapt_definition(&smoke_definition()).expect("transitions adapt natively");
    assert!(adapted.definition().modules.iter().any(|module| {
        module
            .local_sentences
            .iter()
            .any(|sentence| matches!(**sentence, Sentence::Rule { .. }))
    }));
}

#[test]
fn provisional_ir_oracle_compiles_and_reparses_both_kore_artifacts() {
    let artifacts =
        compile_definition_provisional_oracle(&smoke_definition(), CompileOptions::default())
            .expect("the smoke IR must compile through the explicit provisional oracle");
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
            .any(|diagnostic| diagnostic.code == "UndefinedKLabel")
    );
    assert!(!error.message().is_empty());
}
