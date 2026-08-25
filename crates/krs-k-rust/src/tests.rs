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
    kore::{
        ast::{
            Attributes as KoreAttributes, Pattern as KorePattern, Sentence as KoreSentence,
            Sort as KoreSort, Variable as KoreVariable, VariableKind as KoreVariableKind,
        },
        parser::parse_definition,
    },
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use krs_ir::{
    ApplicationRef, BuiltinOperation, CellAttribute, CellContentFrame, CellDeclaration,
    ClaimModality, ConfigurationRoot, ConfigurationSentence, ContextAliasSentence, DefinitionClaim,
    DefinitionClaimBinder, DefinitionIr, DefinitionModule, DefinitionProductionAttribute,
    DefinitionRuleCondition, DefinitionSentence, DefinitionSortRef, DefinitionTerm, FixedCell,
    FixedCellPattern, FixedConfiguration, FixedConfigurationPattern, FixedConfigurationVariable,
    FixedInitializerCell, FormatFragment, GroupAssociativity, GroupAssociativitySentence,
    InitializerDeclaration, ItemKind, LabelId, LabelIdentity, MapOperation, ModuleId, NodeOrigin,
    OriginStack, PackageId, PrecedenceRelation, ProductionFieldId, ProductionFieldReference,
    ProductionGroupId, ProductionItem as IrProductionItem, ProductionResultSort,
    ProductionSentence, RuleSentence, SemanticId, SentenceKind, Sha256Digest, SourceFileId,
    SourceMapKey, SourceRange, StableItemId, StrictnessKind, SubsortSentence, SymbolId,
    SymbolIdentity, SymbolKind, SyntaxSortSentence,
};

use super::{
    Adapter, Backend, CapabilityAvailability, CompileOptions, FRONTEND_CAPABILITIES, FRONTEND_PIN,
    LoadedDefinition, NativeNodeRole, PORTABLE_PRELUDE_POLICY, PortablePreludePolicy, TermContext,
    adapt_definition, compile_definition, compile_definition_provisional_oracle,
    compile_loaded_definition, module_builtin_imports,
};

const MODULE: &str = "KRS-ADAPTER-TEST";

fn m2_definition() -> DefinitionIr {
    m2_definition_with(SentenceKind::Transition, "initKCell")
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
            DefinitionSortRef::declared(k_item),
            vec![DefinitionTerm::application(
                node("def.term.init.foo"),
                DefinitionSortRef::declared(value.clone()),
                ApplicationRef::Declared(foo.clone()),
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
            ("?KRSCOUNTER7".to_owned(), Some("Int".to_owned())),
        ]
    );
}

fn node(key: &str) -> NodeOrigin {
    let package = test_package();
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

fn test_package() -> PackageId {
    PackageId::new("ORG-EXAMPLE-SMOKE", "smoke-semantics", "0.1.0", "workspace").unwrap()
}

fn semantic_id(value: &str) -> SemanticId {
    SemanticId::new(value).unwrap()
}

fn context_alias_id() -> StableItemId {
    StableItemId::new(
        test_package(),
        ["contexts"],
        "eval",
        ItemKind::ContextAlias,
        "",
    )
    .unwrap()
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
        PortablePreludePolicy::ExplicitImportsOnly
    );
}

#[test]
fn builtin_and_map_terms_map_structurally_and_infer_imports() {
    let definition = m2_definition();
    let mut adapter = Adapter::new(&definition);
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
#[allow(clippy::too_many_lines)]
fn grammar_items_attributes_and_group_sentences_map_structurally() {
    let definition = m2_definition();
    let mut adapter = Adapter::new(&definition);
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
        matches!(native_token, Sentence::Production { items, attributes, .. }
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
    let definition = m2_definition();
    let mut adapter = Adapter::new(&definition);
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
    let sentence = ConfigurationSentence::fixed(fixed);
    let native = adapter.configuration(&sentence, MODULE, 0).unwrap();
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
#[allow(clippy::too_many_lines)]
fn claims_and_context_aliases_preserve_native_forms_and_origin_roles() {
    let definition = m2_definition();
    let mut adapter = Adapter::new(&definition);
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
    assert!(variables.contains(&"?N".to_owned()));
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
    let definition = m2_definition();
    let mut adapter = Adapter::new(&definition);
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
        Some("src/lib.rs#krs-source-map=def.module.main"),
        "the portable source path retains the exact IR origin key"
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
        "def.term.init.foo",
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
    let artifacts = compile_definition(&m2_definition(), CompileOptions::default())
        .expect("permanent compilation uses public pinned preparation primitives");
    assert!(!artifacts.definition_kore.is_empty());
    assert!(!artifacts.syntax_definition_kore.is_empty());
}

#[test]
fn permanent_compile_disambiguates_generated_names_reused_at_different_sorts() {
    let sort = |name: &str| KoreSort::Application {
        name: name.to_owned(),
        arguments: Vec::new(),
    };
    let variable = |sort: KoreSort| {
        KorePattern::Variable(KoreVariable {
            kind: KoreVariableKind::Element,
            name: "_Gen2".to_owned(),
            sort,
        })
    };
    let mut sentence = KoreSentence::Axiom {
        parameters: Vec::new(),
        pattern: Box::new(KorePattern::And {
            sort: sort("SortGeneratedTopCell"),
            arguments: vec![
                variable(sort("SortKItem")),
                variable(sort("SortGeneratedCounterCell")),
            ],
        }),
        attributes: KoreAttributes::default(),
    };

    assert_eq!(super::disambiguate_kore_sentence(&mut sentence), 1);
    let KoreSentence::Axiom { pattern, .. } = sentence else {
        unreachable!()
    };
    let KorePattern::And { arguments, .. } = *pattern else {
        unreachable!()
    };
    let names = arguments
        .iter()
        .map(|pattern| match pattern {
            KorePattern::Variable(variable) => variable.name.as_str(),
            _ => unreachable!(),
        })
        .collect::<Vec<_>>();
    assert_eq!(names.iter().filter(|name| **name == "_Gen2").count(), 1);
    assert_eq!(
        names
            .iter()
            .filter(|name| name.starts_with("KRSVar"))
            .count(),
        1
    );
}

#[test]
fn transition_sentence_is_preserved_as_a_native_rule() {
    let adapted = adapt_definition(&m2_definition()).expect("transitions adapt natively");
    assert!(adapted.definition().modules.iter().any(|module| {
        module
            .local_sentences
            .iter()
            .any(|sentence| matches!(sentence, Sentence::Rule { .. }))
    }));
}

#[test]
fn provisional_ir_oracle_compiles_and_reparses_both_kore_artifacts() {
    let artifacts =
        compile_definition_provisional_oracle(&m2_definition(), CompileOptions::default())
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
