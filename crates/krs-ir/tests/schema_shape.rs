//! Pin the serde-reflection registry for the supported KRS IR shapes.
//! Types that reflection cannot trace are asserted below; their wire shapes are pinned only by
//! `tests/golden/*.json` and the port gates.
//! After bumping `SchemaVersion::CURRENT` and `Krs.lock`, set `KRS_IR_SCHEMA_RECORD=1` to record
//! the new registry file.

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use krs_ir::measure::*;
use krs_ir::wire::*;
use krs_ir::*;
use serde_reflection::{Error, Registry, Samples, Tracer, TracerConfig};

const RECORD: &str = "KRS_IR_SCHEMA_RECORD";

// Internally and adjacently tagged enums must remain outside reflection.
const UNSUPPORTED_TAGGED: &[&str] = &[
    "ApplicationRef",
    "CellAttribute",
    "CellContentFrame",
    "CellPost",
    "ConfigurationRoot",
    "DefinitionSentence",
    "DefinitionSortRef",
    "DefinitionTermKind",
    "DescriptorApplicationRef",
    "DescriptorConfigurationRoot",
    "DescriptorLiteral",
    "DescriptorPayload",
    "DescriptorProductionAttribute",
    "DescriptorProductionItem",
    "DescriptorProductionOwner",
    "DescriptorSortRef",
    "DescriptorTerm",
    "DescriptorTermArgument",
    "FixedCellContent",
    "FixedInitializerContent",
    "FormatFragment",
    "GrammarDescriptor",
    "GrammarProductionItemKind",
    "OriginFrame",
    "ProductionAttribute",
    "ProtocolCellContent",
    "ProtocolContextAliasBindingKind",
    "ProtocolHeadRuleExtra",
    "ProtocolHeadRuleResult",
    "ProtocolInitializerCellContent",
    "ProtocolInitializerStateTerm",
    "ProtocolMapBody",
    "ProtocolRuleBindingKind",
    "ProtocolRuleFrame",
    "ProtocolRuleMapBody",
    "ProtocolRuleStateTerm",
    "RustVisibility",
    "SemanticSortRef",
    "SemanticTermKind",
    "WireGrammarDescriptor",
    "WireProductionAttribute",
    "WireProductionItem",
    "WireProductionOwner",
    "WireTerm",
    "WireTermArgument",
];

// Flattened fields must remain outside reflection.
const UNSUPPORTED_FLATTENED: &[&str] = &[
    "DefinitionTerm",
    "Descriptor",
    "GrammarProductionItem",
    "SemanticTerm",
];

// Untagged variants must remain outside reflection.
const UNSUPPORTED_UNTAGGED: &[&str] = &["DefinitionRuleBody", "SemanticRuleBody"];

// Validated deserializers that reach unsupported descendants must remain outside reflection.
const UNSUPPORTED_VALIDATED: &[&str] = &[
    "DefinitionIr",
    "DescriptorBundle",
    "DescriptorProvenance",
    "OriginStack",
    "SemanticTheory",
];

// Containers that reach an unsupported descendant must remain outside reflection.
const UNSUPPORTED_TRANSITIVE: &[&str] = &[
    "ConstructorDescriptor",
    "ConstructorFieldDescriptor",
    "ContextAliasSentence",
    "DefinitionClaim",
    "DefinitionClaimBinder",
    "DefinitionModule",
    "DefinitionRuleCondition",
    "DefinitionRulePriority",
    "DefinitionSimplification",
    "DefinitionSimplificationPriority",
    "DefinitionVariable",
    "DescriptorApplicationReference",
    "DescriptorCellTermField",
    "DescriptorClaim",
    "DescriptorClaimBinder",
    "DescriptorConfigurationRule",
    "DescriptorContextAlias",
    "DescriptorDeclaration",
    "DescriptorFixedConfiguration",
    "DescriptorFormatFragment",
    "DescriptorHeadRule",
    "DescriptorNodeOrigin",
    "DescriptorProduction",
    "DescriptorRuleCondition",
    "DescriptorSortReference",
    "FixedCell",
    "FixedCellClause",
    "FixedCellPattern",
    "FixedConfiguration",
    "FixedConfigurationPattern",
    "FixedConfigurationRewrite",
    "FixedConfigurationVariable",
    "FixedInitializerCell",
    "GroupAssociativitySentence",
    "NodeOrigin",
    "PrecedenceRelation",
    "ProductionContextAliasReference",
    "ProductionFieldReference",
    "ProductionGroupIdentity",
    "ProductionResultSort",
    "ProductionSentence",
    "ProtocolCellField",
    "ProtocolContextAliasBinding",
    "ProtocolInitializerCell",
    "ProtocolMap",
    "ProtocolRuleBinding",
    "ProtocolRuleCell",
    "ProtocolRuleCells",
    "ProtocolRuleKSequence",
    "ProtocolRuleMap",
    "RuleSentence",
    "SemanticClaim",
    "SemanticClaimBinder",
    "SemanticContextAlias",
    "SemanticModule",
    "SemanticProduction",
    "SemanticRule",
    "SemanticRuleCondition",
    "SemanticRuleLabel",
    "SemanticRulePriority",
    "SemanticSimplification",
    "SemanticSimplificationPriority",
    "SemanticSort",
    "SemanticSubsort",
    "SemanticVariable",
    "StructuredRuleDescriptor",
    "SubsortSentence",
    "SyntaxSortSentence",
    "WireCellTermField",
    "WireHeadRule",
    "WirePayload",
    "WireProduction",
    "WireRuleCondition",
    "WireStructuredRule",
];

const UNTRACEABLE: &[&[&str]] = &[
    UNSUPPORTED_TAGGED,
    UNSUPPORTED_FLATTENED,
    UNSUPPORTED_UNTAGGED,
    UNSUPPORTED_VALIDATED,
    UNSUPPORTED_TRANSITIVE,
];

fn config() -> TracerConfig {
    TracerConfig::default()
        .is_human_readable(true)
        .default_string_value(format!("a{}", "0".repeat(63)))
}

fn samples() -> Samples {
    let package = PackageId::new("ORG-EXAMPLE-SCHEMA", "schema", "0.1.0", "workspace").unwrap();
    let item = StableItemId::new(package.clone(), ["syntax"], "Value", ItemKind::Sort, "").unwrap();
    let file = SourceFileId::new(
        package.clone(),
        "src/lib.rs",
        Sha256Digest::new(format!("a{}", "0".repeat(63))).unwrap(),
    )
    .unwrap();
    let range = SourceRange::new(file.clone(), 0, 3).unwrap();
    let key = ProvenanceKey::new("sort_declaration", 0).unwrap();
    let stack = OriginStack::authored(range.clone());
    let mut tracer = Tracer::new(config());
    let mut samples = Samples::new();
    tracer.trace_value(&mut samples, &package).unwrap();
    tracer.trace_value(&mut samples, &item).unwrap();
    tracer.trace_value(&mut samples, &file).unwrap();
    tracer.trace_value(&mut samples, &key).unwrap();
    tracer.trace_value(&mut samples, &range).unwrap();
    tracer.trace_value(&mut samples, &stack).unwrap();
    tracer
        .trace_value(
            &mut samples,
            &Sha256Digest::new(format!("a{}", "0".repeat(63))).unwrap(),
        )
        .unwrap();
    tracer
        .trace_value(&mut samples, &ExplicitSymbol::new("Schema::Value").unwrap())
        .unwrap();
    tracer
        .trace_value(&mut samples, &CellColor::new("blue").unwrap())
        .unwrap();
    tracer
        .trace_value(&mut samples, &SourceMapKey::new("source-map").unwrap())
        .unwrap();
    tracer
        .trace_value(&mut samples, &ModuleId::new("MODULE").unwrap())
        .unwrap();
    tracer
        .trace_value(&mut samples, &SemanticId::new("semantic").unwrap())
        .unwrap();
    tracer
        .trace_value(&mut samples, &SymbolId::new("symbol").unwrap())
        .unwrap();
    tracer
        .trace_value(&mut samples, &LabelId::new("label").unwrap())
        .unwrap();
    tracer
        .trace_value(&mut samples, &ProductionFieldId::new("field").unwrap())
        .unwrap();
    tracer
        .trace_value(&mut samples, &ProductionGroupId::new("group").unwrap())
        .unwrap();
    Tracer::new(config())
        .trace_value(&mut samples, &DescriptorBundle::empty())
        .unwrap();
    samples
}

fn census() -> BTreeSet<String> {
    let sources = [
        include_str!("../src/bundle.rs"),
        include_str!("../src/definition.rs"),
        include_str!("../src/generated.rs"),
        include_str!("../src/grammar.rs"),
        include_str!("../src/host.rs"),
        include_str!("../src/identity.rs"),
        include_str!("../src/ir.rs"),
        include_str!("../src/json.rs"),
        include_str!("../src/lib.rs"),
        include_str!("../src/measure.rs"),
        include_str!("../src/provenance.rs"),
        include_str!("../src/semantic.rs"),
        include_str!("../src/state.rs"),
        include_str!("../src/transport/configuration.rs"),
        include_str!("../src/transport/grammar.rs"),
        include_str!("../src/transport/head_rule.rs"),
        include_str!("../src/transport/rule.rs"),
        include_str!("../src/transport.rs"),
        include_str!("../src/wire.rs"),
    ];
    let mut names = BTreeSet::new();
    for source in sources {
        let mut derives_deserialize = false;
        for line in source.lines().map(str::trim) {
            if line.starts_with("#[derive(") {
                derives_deserialize = line.contains("Deserialize");
            } else if let Some(rest) = line
                .strip_prefix("pub struct ")
                .or_else(|| line.strip_prefix("pub enum "))
            {
                if derives_deserialize {
                    names.insert(
                        rest.split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                            .next()
                            .unwrap()
                            .to_owned(),
                    );
                }
                derives_deserialize = false;
            } else if line.starts_with("impl")
                && line.contains("Deserialize<")
                && line.contains(" for ")
            {
                let name = line
                    .rsplit_once(" for ")
                    .unwrap()
                    .1
                    .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                    .next()
                    .unwrap();
                names.insert(name.to_owned());
            }
        }
    }
    names
}

#[allow(clippy::too_many_lines)]
fn registry() -> Registry {
    let samples = samples();
    let mut tracer = Tracer::new(config());
    let mut classified = BTreeSet::new();
    let mut probed = BTreeSet::new();
    macro_rules! trace {
        ($name:ident : $ty:ty) => {
            tracer.trace_type::<$ty>(&samples).unwrap_or_else(|error| {
                panic!(
                    "{} unexpectedly failed reflection: {error:?}",
                    stringify!($name)
                )
            });
            assert!(classified.insert(stringify!($name).to_owned()));
        };
    }
    trace!(BuiltinOperation: BuiltinOperation);
    trace!(BuiltinSort: BuiltinSort);
    trace!(CellCollectionType: CellCollectionType);
    trace!(CellColor: CellColor);
    trace!(CellMultiplicity: CellMultiplicity);
    trace!(CellWrapper: CellWrapper);
    trace!(ClaimModality: ClaimModality);
    trace!(CollectorMeasureDocument: CollectorMeasureDocument);
    trace!(CollectorPathProbe: CollectorPathProbe);
    trace!(CollectorReadSet: CollectorReadSet);
    trace!(CountersDocument: CountersDocument);
    trace!(DescriptorApplicationHeadClass: DescriptorApplicationHeadClass);
    trace!(DescriptorAssociativitySentence: DescriptorAssociativitySentence);
    trace!(DescriptorCellColor: DescriptorCellColor);
    trace!(DescriptorCellDeclarationReference: DescriptorCellDeclarationReference);
    trace!(DescriptorCellIdentity: DescriptorCellIdentity);
    trace!(DescriptorCellMultiplicity: DescriptorCellMultiplicity);
    trace!(DescriptorCellName: DescriptorCellName);
    trace!(DescriptorCellReference: DescriptorCellReference);
    trace!(DescriptorCellType: DescriptorCellType);
    trace!(DescriptorConfigurationReference: DescriptorConfigurationReference);
    trace!(DescriptorContextAliasReference: DescriptorContextAliasReference);
    trace!(DescriptorFieldReference: DescriptorFieldReference);
    trace!(DescriptorGroupReference: DescriptorGroupReference);
    trace!(DescriptorKSequenceNotation: DescriptorKSequenceNotation);
    trace!(DescriptorLexicalPrecedence: DescriptorLexicalPrecedence);
    trace!(DescriptorPrecedenceChain: DescriptorPrecedenceChain);
    trace!(DescriptorRuleLabel: DescriptorRuleLabel);
    trace!(DescriptorRulePriority: DescriptorRulePriority);
    trace!(DescriptorSimplification: DescriptorSimplification);
    trace!(DescriptorSimplificationPriority: DescriptorSimplificationPriority);
    trace!(ExplicitSymbol: ExplicitSymbol);
    trace!(GroupAssociativity: GroupAssociativity);
    trace!(HookOperation: HookOperation);
    trace!(ItemKind: ItemKind);
    trace!(LabelId: LabelId);
    trace!(LabelIdentity: LabelIdentity);
    trace!(ListOperation: ListOperation);
    trace!(MapOperation: MapOperation);
    trace!(ModuleId: ModuleId);
    trace!(PackageId: PackageId);
    trace!(ProductionFieldId: ProductionFieldId);
    trace!(ProductionGroupId: ProductionGroupId);
    trace!(ProvenanceKey: ProvenanceKey);
    trace!(RangedOriginKind: RangedOriginKind);
    trace!(SchemaVersion: SchemaVersion);
    trace!(SemanticId: SemanticId);
    trace!(SentenceKind: SentenceKind);
    trace!(SetOperation: SetOperation);
    trace!(Sha256Digest: Sha256Digest);
    trace!(SortDescriptor: SortDescriptor);
    trace!(SourceFileId: SourceFileId);
    trace!(SourceMapKey: SourceMapKey);
    trace!(SourceRange: SourceRange);
    trace!(Span: Span);
    trace!(StableItemId: StableItemId);
    trace!(StrictnessKind: StrictnessKind);
    trace!(SymbolId: SymbolId);
    trace!(SymbolIdentity: SymbolIdentity);
    trace!(SymbolKind: SymbolKind);
    trace!(TimingsDocument: TimingsDocument);
    trace!(TransformationOriginKind: TransformationOriginKind);
    trace!(WireApplicationReference: WireApplicationReference);
    trace!(WireConfigurationReference: WireConfigurationReference);
    trace!(WireConstructorDescriptor: WireConstructorDescriptor);
    trace!(WireConstructorFieldDescriptor: WireConstructorFieldDescriptor);
    trace!(WireContextAliasReference: WireContextAliasReference);
    trace!(WireHeadRuleCellReference: WireHeadRuleCellReference);
    trace!(WireSortReference: WireSortReference);
    trace!(WireTypeReference: WireTypeReference);
    trace!(ProtocolCellDeclaration: ProtocolCellDeclaration<String>);
    trace!(ProtocolConfigurationVariable: ProtocolConfigurationVariable<String>);
    trace!(ProtocolInitializerTerm: ProtocolInitializerTerm<String>);
    trace!(ProtocolKSequenceItem: ProtocolKSequenceItem<String>);
    trace!(ProtocolKSequence: ProtocolKSequence<String>);
    trace!(ProtocolMapItem: ProtocolMapItem<String>);
    trace!(ProtocolConfigurationInitializer: ProtocolConfigurationInitializer<String,String,String>);
    trace!(ProtocolHeadRuleBinding: ProtocolHeadRuleBinding<String>);
    trace!(ProtocolRuleKSequenceItem: ProtocolRuleKSequenceItem<String>);
    trace!(ProtocolRuleMapItem: ProtocolRuleMapItem<String>);
    let listed: BTreeSet<_> = UNTRACEABLE
        .iter()
        .flat_map(|group| group.iter().copied())
        .map(str::to_owned)
        .collect();
    assert_eq!(
        listed.len(),
        UNTRACEABLE.iter().map(|group| group.len()).sum::<usize>(),
        "duplicate untraceable type"
    );
    macro_rules! unsupported {
        ($name:ident : $ty:ty) => {{
            let mut probe = Tracer::new(config());
            let error = probe.trace_type::<$ty>(&samples).unwrap_err();
            assert!(
                matches!(error, Error::NotSupported(_)),
                "{} changed reflection status: {error:?}",
                stringify!($name)
            );
            assert!(classified.insert(stringify!($name).to_owned()));
            probed.insert(stringify!($name).to_owned());
        }};
    }
    unsupported!(CellAttribute: CellAttribute);
    unsupported!(CellContentFrame: CellContentFrame);
    unsupported!(ConfigurationRoot: ConfigurationRoot);
    unsupported!(ConstructorDescriptor: ConstructorDescriptor);
    unsupported!(ConstructorFieldDescriptor: ConstructorFieldDescriptor);
    unsupported!(ContextAliasSentence: ContextAliasSentence);
    unsupported!(DefinitionClaim: DefinitionClaim);
    unsupported!(DefinitionClaimBinder: DefinitionClaimBinder);
    unsupported!(DefinitionIr: DefinitionIr);
    unsupported!(DefinitionModule: DefinitionModule);
    unsupported!(DefinitionRuleBody: DefinitionRuleBody);
    unsupported!(DefinitionRuleCondition: DefinitionRuleCondition);
    unsupported!(DefinitionRulePriority: DefinitionRulePriority);
    unsupported!(DefinitionSimplification: DefinitionSimplification);
    unsupported!(DefinitionSimplificationPriority: DefinitionSimplificationPriority);
    unsupported!(DefinitionSortRef: DefinitionSortRef);
    unsupported!(DefinitionTerm: DefinitionTerm);
    unsupported!(DefinitionTermKind: DefinitionTermKind);
    unsupported!(DefinitionVariable: DefinitionVariable);
    unsupported!(Descriptor: Descriptor);
    unsupported!(DescriptorApplicationRef: DescriptorApplicationRef);
    unsupported!(DescriptorApplicationReference: DescriptorApplicationReference);
    unsupported!(DescriptorBundle: DescriptorBundle);
    unsupported!(DescriptorCellTermField: DescriptorCellTermField);
    unsupported!(DescriptorClaim: DescriptorClaim);
    unsupported!(DescriptorClaimBinder: DescriptorClaimBinder);
    unsupported!(DescriptorConfigurationRoot: DescriptorConfigurationRoot);
    unsupported!(DescriptorConfigurationRule: DescriptorConfigurationRule);
    unsupported!(DescriptorContextAlias: DescriptorContextAlias);
    unsupported!(DescriptorDeclaration: DescriptorDeclaration);
    unsupported!(DescriptorFixedConfiguration: DescriptorFixedConfiguration);
    unsupported!(DescriptorFormatFragment: DescriptorFormatFragment);
    unsupported!(DescriptorHeadRule: DescriptorHeadRule);
    unsupported!(DescriptorLiteral: DescriptorLiteral);
    unsupported!(DescriptorNodeOrigin: DescriptorNodeOrigin);
    unsupported!(DescriptorPayload: DescriptorPayload);
    unsupported!(DescriptorProduction: DescriptorProduction);
    unsupported!(DescriptorProductionAttribute: DescriptorProductionAttribute);
    unsupported!(DescriptorProductionItem: DescriptorProductionItem);
    unsupported!(DescriptorProductionOwner: DescriptorProductionOwner);
    unsupported!(DescriptorProvenance: DescriptorProvenance);
    unsupported!(DescriptorRuleCondition: DescriptorRuleCondition);
    unsupported!(DescriptorSortRef: DescriptorSortRef);
    unsupported!(DescriptorSortReference: DescriptorSortReference);
    unsupported!(DescriptorTerm: DescriptorTerm);
    unsupported!(DescriptorTermArgument: DescriptorTermArgument);
    unsupported!(FormatFragment: FormatFragment);
    unsupported!(GrammarDescriptor: GrammarDescriptor);
    unsupported!(GroupAssociativitySentence: GroupAssociativitySentence);
    unsupported!(NodeOrigin: NodeOrigin);
    unsupported!(OriginFrame: OriginFrame);
    unsupported!(OriginStack: OriginStack);
    unsupported!(PrecedenceRelation: PrecedenceRelation);
    unsupported!(ProductionContextAliasReference: ProductionContextAliasReference);
    unsupported!(ProductionFieldReference: ProductionFieldReference);
    unsupported!(ProductionGroupIdentity: ProductionGroupIdentity);
    unsupported!(ProductionSentence: ProductionSentence);
    unsupported!(ProtocolRuleFrame: ProtocolRuleFrame);
    unsupported!(RuleSentence: RuleSentence);
    unsupported!(RustVisibility: RustVisibility);
    unsupported!(SemanticClaim: SemanticClaim);
    unsupported!(SemanticClaimBinder: SemanticClaimBinder);
    unsupported!(SemanticContextAlias: SemanticContextAlias);
    unsupported!(SemanticModule: SemanticModule);
    unsupported!(SemanticProduction: SemanticProduction);
    unsupported!(SemanticRule: SemanticRule);
    unsupported!(SemanticRuleBody: SemanticRuleBody);
    unsupported!(SemanticRuleCondition: SemanticRuleCondition);
    unsupported!(SemanticRuleLabel: SemanticRuleLabel);
    unsupported!(SemanticRulePriority: SemanticRulePriority);
    unsupported!(SemanticSimplification: SemanticSimplification);
    unsupported!(SemanticSimplificationPriority: SemanticSimplificationPriority);
    unsupported!(SemanticSort: SemanticSort);
    unsupported!(SemanticSortRef: SemanticSortRef);
    unsupported!(SemanticSubsort: SemanticSubsort);
    unsupported!(SemanticTerm: SemanticTerm);
    unsupported!(SemanticTermKind: SemanticTermKind);
    unsupported!(SemanticTheory: SemanticTheory);
    unsupported!(SemanticVariable: SemanticVariable);
    unsupported!(StructuredRuleDescriptor: StructuredRuleDescriptor);
    unsupported!(SubsortSentence: SubsortSentence);
    unsupported!(SyntaxSortSentence: SyntaxSortSentence);
    unsupported!(WireCellTermField: WireCellTermField);
    unsupported!(WireGrammarDescriptor: WireGrammarDescriptor);
    unsupported!(WireHeadRule: WireHeadRule);
    unsupported!(WirePayload: WirePayload);
    unsupported!(WireProduction: WireProduction);
    unsupported!(WireProductionAttribute: WireProductionAttribute);
    unsupported!(WireProductionItem: WireProductionItem);
    unsupported!(WireProductionOwner: WireProductionOwner);
    unsupported!(WireRuleCondition: WireRuleCondition);
    unsupported!(WireStructuredRule: WireStructuredRule);
    unsupported!(WireTerm: WireTerm);
    unsupported!(WireTermArgument: WireTermArgument);
    unsupported!(ApplicationRef: ApplicationRef<String>);
    unsupported!(GrammarProductionItem: GrammarProductionItem<String>);
    unsupported!(GrammarProductionItemKind: GrammarProductionItemKind<String>);
    unsupported!(ProductionResultSort: ProductionResultSort<String>);
    unsupported!(ProductionAttribute: ProductionAttribute<String>);
    unsupported!(FixedCell: FixedCell<String,String>);
    unsupported!(FixedCellContent: FixedCellContent<String,String>);
    unsupported!(FixedConfigurationVariable: FixedConfigurationVariable<String>);
    unsupported!(FixedInitializerCell: FixedInitializerCell<String,String>);
    unsupported!(FixedInitializerContent: FixedInitializerContent<String,String>);
    unsupported!(FixedConfiguration: FixedConfiguration<String,String,String>);
    unsupported!(CellPost: CellPost<String>);
    unsupported!(FixedCellClause: FixedCellClause<String,String>);
    unsupported!(FixedCellPattern: FixedCellPattern<String,String>);
    unsupported!(FixedConfigurationPattern: FixedConfigurationPattern<String,String>);
    unsupported!(FixedConfigurationRewrite: FixedConfigurationRewrite<String,String>);
    unsupported!(ProtocolCellContent: ProtocolCellContent<String,String>);
    unsupported!(ProtocolCellField: ProtocolCellField<String,String,String>);
    unsupported!(ProtocolMapBody: ProtocolMapBody<String>);
    unsupported!(ProtocolMap: ProtocolMap<String>);
    unsupported!(ProtocolInitializerStateTerm: ProtocolInitializerStateTerm<String>);
    unsupported!(ProtocolInitializerCellContent: ProtocolInitializerCellContent<String,String,String>);
    unsupported!(ProtocolInitializerCell: ProtocolInitializerCell<String,String,String>);
    unsupported!(ProtocolHeadRuleResult: ProtocolHeadRuleResult<String>);
    unsupported!(ProtocolHeadRuleExtra: ProtocolHeadRuleExtra<String,String>);
    unsupported!(ProtocolRuleBindingKind: ProtocolRuleBindingKind<String>);
    unsupported!(ProtocolRuleBinding: ProtocolRuleBinding<String>);
    unsupported!(ProtocolRuleKSequence: ProtocolRuleKSequence<String>);
    unsupported!(ProtocolRuleMapBody: ProtocolRuleMapBody<String>);
    unsupported!(ProtocolRuleMap: ProtocolRuleMap<String>);
    unsupported!(ProtocolRuleStateTerm: ProtocolRuleStateTerm<String>);
    unsupported!(ProtocolRuleCell: ProtocolRuleCell<String,String>);
    unsupported!(ProtocolRuleCells: ProtocolRuleCells<String,String>);
    unsupported!(ProtocolContextAliasBindingKind: ProtocolContextAliasBindingKind<String>);
    unsupported!(ProtocolContextAliasBinding: ProtocolContextAliasBinding<String>);
    unsupported!(DefinitionSentence: DefinitionSentence);
    assert_eq!(
        probed, listed,
        "the untraceable lists must name exactly the probed types"
    );
    assert_eq!(
        classified,
        census(),
        "every public Deserialize type must be traced or listed as unsupported"
    );
    tracer.registry().unwrap()
}

#[test]
fn krs_ir_schema_shape_is_pinned() {
    // serde_yaml cannot directly emit nested enum values in ContainerFormat.
    let actual = serde_yaml::to_string(&serde_json::to_value(registry()).unwrap()).unwrap();
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/schema")
        .join(format!("krs_ir-{}.yaml", SchemaVersion::CURRENT.0));
    if std::env::var(RECORD).as_deref() == Ok("1") {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, actual).unwrap();
    } else {
        let expected = fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!("{}: {error}; bump SchemaVersion::CURRENT and Krs.lock, then set {RECORD}=1 to add the new registry", path.display())
        });
        assert_eq!(
            actual,
            expected,
            "{} changed; bump SchemaVersion::CURRENT and Krs.lock and add the new registry with {RECORD}=1, or revert",
            path.display()
        );
    }
}
