macro_rules! leaf {
    ($ty:ty, $value:expr) => {
        impl Sample for $ty {
            fn samples() -> Vec<Self> {
                vec![$value]
            }
        }
    };
}

leaf!(SchemaVersion, SchemaVersion::CURRENT);
leaf!(
    PackageId,
    PackageId::new("ORG-EXAMPLE-SCHEMA", "schema", "0.1.0", "workspace").unwrap()
);
leaf!(
    Sha256Digest,
    Sha256Digest::new(format!("a{}", "0".repeat(63))).unwrap()
);
leaf!(
    StableItemId,
    StableItemId::new(
        sample::<PackageId>(),
        ["syntax"],
        "Value",
        ItemKind::Sort,
        ""
    )
    .unwrap()
);
leaf!(
    SourceFileId,
    SourceFileId::new(
        sample::<PackageId>(),
        "src/lib.rs",
        sample::<Sha256Digest>()
    )
    .unwrap()
);
leaf!(
    SourceRange,
    SourceRange::new(sample::<SourceFileId>(), 0, 3).unwrap()
);
leaf!(
    ProvenanceKey,
    ProvenanceKey::new("sort_declaration", 0).unwrap()
);
leaf!(CellColor, CellColor::new("blue").unwrap());
leaf!(
    ExplicitSymbol,
    ExplicitSymbol::new("Schema::Value").unwrap()
);
leaf!(SourceMapKey, SourceMapKey::new("source-map").unwrap());
leaf!(ModuleId, ModuleId::new("MODULE").unwrap());
leaf!(SemanticId, SemanticId::new("semantic").unwrap());
leaf!(SymbolId, SymbolId::new("symbol").unwrap());
leaf!(LabelId, LabelId::new("label").unwrap());
leaf!(ProductionFieldId, ProductionFieldId::new("field").unwrap());
leaf!(ProductionGroupId, ProductionGroupId::new("group").unwrap());
leaf!(
    NodeOrigin,
    NodeOrigin::new(sample::<SourceMapKey>(), sample::<OriginStack>())
);

// The frame list is private; use the validating constructor.
impl Sample for OriginStack {
    fn samples() -> Vec<Self> {
        let mut stack = Self::authored(sample::<SourceRange>());
        stack.push(OriginFrame::Transformation {
            kind: TransformationOriginKind::SemanticIr,
            item: Some(sample::<StableItemId>()),
            label: Some("transform".into()),
        });
        vec![stack]
    }
}

// The provenance fields are private; use the validating constructor.
impl Sample for DescriptorProvenance {
    fn samples() -> Vec<Self> {
        let key = sample::<ProvenanceKey>();
        vec![Self::new(
            key.clone(),
            vec![DescriptorNodeOrigin::new(key, sample::<OriginStack>())],
        )
        .unwrap()]
    }
}

// The schema field is private; use the validating public constructor.
impl Sample for DescriptorBundle {
    fn samples() -> Vec<Self> {
        let mut descriptor = sample::<Descriptor>();
        let primary = descriptor.provenance.primary_key().clone();
        descriptor.provenance = DescriptorProvenance::new(
            primary.clone(),
            vec![
                DescriptorNodeOrigin::new(primary, sample::<OriginStack>()),
                DescriptorNodeOrigin::new(
                    ProvenanceKey::new("stable_symbol", 0).unwrap(),
                    sample::<OriginStack>(),
                ),
            ],
        )
        .unwrap();
        let declaration = DescriptorDeclaration::new(
            descriptor.id.clone(),
            RustVisibility::Inherited,
            Some(sample::<ExplicitSymbol>()),
        );
        vec![Self::with_declarations(vec![descriptor], vec![declaration]).unwrap()]
    }
}

// The flattened fields are private; use the public constructor.
impl Sample for DefinitionTerm {
    fn samples() -> Vec<Self> {
        vec![Self::variable(
            sample::<NodeOrigin>(),
            DefinitionSortRef::Builtin(BuiltinSort::Int),
            sample::<SemanticId>(),
        )]
    }
}

// The flattened fields are private; use the public constructor.
impl Sample for SemanticTerm {
    fn samples() -> Vec<Self> {
        vec![Self::variable(
            sample::<NodeOrigin>(),
            SemanticSortRef::Builtin(BuiltinSort::Int),
            sample::<SemanticId>(),
        )]
    }
}

// The schema field is private; use the validating constructor.
impl Sample for SemanticTheory {
    fn samples() -> Vec<Self> {
        let value: serde_json::Value =
            serde_json::from_str(include_str!("../golden/semantic_foo_bar.json")).unwrap();
        let modules: Vec<SemanticModule> =
            serde_json::from_value(value["modules"].clone()).unwrap();
        vec![Self::new(modules).unwrap()]
    }
}

// The schema field is private; use the validating constructor.
impl Sample for DefinitionIr {
    fn samples() -> Vec<Self> {
        let value: serde_json::Value =
            serde_json::from_str(include_str!("../golden/definition_foo_bar.json")).unwrap();
        let modules: Vec<DefinitionModule> =
            serde_json::from_value(value["modules"].clone()).unwrap();
        let main_module: ModuleId = serde_json::from_value(value["main_module"].clone()).unwrap();
        vec![Self::new(main_module, modules).unwrap()]
    }
}

// The identity fields are private; use their public constructors.
leaf!(
    LabelIdentity,
    LabelIdentity::new(sample::<LabelId>(), "label").unwrap()
);
leaf!(
    SymbolIdentity,
    SymbolIdentity::new(sample::<SymbolId>(), "symbol", sample::<SymbolKind>()).unwrap()
);
leaf!(
    DescriptorDeclaration,
    DescriptorDeclaration::new(
        sample::<StableItemId>(),
        sample::<RustVisibility>(),
        Some(sample::<ExplicitSymbol>())
    )
);

// The flattened fields are private; use the public constructor.
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample for GrammarProductionItem<S> {
    fn samples() -> Vec<Self> {
        vec![Self::terminal(sample::<NodeOrigin>(), "terminal").unwrap()]
    }
}

// The sentence fields are private; use the validating constructor.
impl Sample for ProductionSentence {
    fn samples() -> Vec<Self> {
        let symbol =
            SymbolIdentity::new(sample::<SymbolId>(), "production", SymbolKind::Production)
                .unwrap();
        vec![Self::new(
            sample::<NodeOrigin>(),
            symbol,
            sample::<DefinitionSortRef>(),
            sample::<Vec<ProductionItem>>(),
            sample::<Vec<DefinitionProductionAttribute>>(),
        )
        .unwrap()]
    }
}

trait OtherSample: Sample {
    fn other() -> Self;
}
impl OtherSample for String {
    fn other() -> Self {
        "other".into()
    }
}
impl OtherSample for SemanticId {
    fn other() -> Self {
        Self::new("other").unwrap()
    }
}
impl OtherSample for SymbolId {
    fn other() -> Self {
        Self::new("other").unwrap()
    }
}

// The content field is private; use the public leaf constructor.
impl<
        S: Sample + Clone + Serialize + DeserializeOwned,
        C: Sample + Clone + Serialize + DeserializeOwned,
    > Sample for FixedCell<S, C>
{
    fn samples() -> Vec<Self> {
        vec![Self::leaf(
            sample::<NodeOrigin>(),
            sample::<C>(),
            "cell",
            sample::<Vec<CellAttribute>>(),
            sample::<S>(),
        )
        .unwrap()]
    }
}

// The content field is private; use the public term constructor.
impl<
        C: Sample + Clone + Serialize + DeserializeOwned,
        T: Sample + Clone + Serialize + DeserializeOwned,
    > Sample for FixedInitializerCell<C, T>
{
    fn samples() -> Vec<Self> {
        vec![Self::term(
            sample::<NodeOrigin>(),
            sample::<C>(),
            sample::<T>(),
        )]
    }
}

// The fields are private; use the validating constructor.
impl<
        S: Sample + Clone + Serialize + DeserializeOwned,
        C: Sample + Clone + Ord + Serialize + DeserializeOwned,
        T: Sample + Clone + Serialize + DeserializeOwned,
    > Sample for FixedConfiguration<S, C, T>
{
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<SemanticId>(),
            sample::<ConfigurationRoot>(),
            sample::<Vec<FixedCell<S, C>>>(),
            sample::<NodeOrigin>(),
            sample::<SemanticId>(),
            sample::<Vec<FixedConfigurationVariable<S>>>(),
            sample::<Vec<FixedInitializerCell<C, T>>>(),
        )
        .unwrap()]
    }
}

// The fields are private; use the validating constructor.
impl<
        C: OtherSample + Clone + Ord + Serialize + DeserializeOwned,
        T: Sample + Clone + Serialize + DeserializeOwned,
    > Sample for FixedConfigurationPattern<C, T>
{
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<SemanticId>(),
            sample::<Vec<FixedCellPattern<C, T>>>(),
            vec![C::other()],
        )
        .unwrap()]
    }
}

// The fields are private; use the validating constructor.
impl<
        C: OtherSample + Clone + Ord + Serialize + DeserializeOwned,
        T: Sample + Clone + Serialize + DeserializeOwned,
    > Sample for FixedConfigurationRewrite<C, T>
{
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<SemanticId>(),
            sample::<Vec<FixedCellClause<C, T>>>(),
            vec![C::other()],
        )
        .unwrap()]
    }
}

// The fields are private; use the public constructor and metadata setters.
impl Sample for RuleSentence {
    fn samples() -> Vec<Self> {
        let term = sample::<DefinitionTerm>();
        let body = DefinitionTerm::rewrite(
            sample::<NodeOrigin>(),
            DefinitionSortRef::Builtin(BuiltinSort::Int),
            term.clone(),
            term,
        )
        .unwrap();
        let condition = DefinitionRuleCondition::new(
            sample::<NodeOrigin>(),
            DefinitionTerm::variable(
                sample::<NodeOrigin>(),
                DefinitionSortRef::Builtin(BuiltinSort::Bool),
                sample::<SemanticId>(),
            ),
        );
        let rule = Self::new(
            sample::<NodeOrigin>(),
            sample::<LabelIdentity>(),
            SentenceKind::Equation,
            sample::<Vec<DefinitionVariable>>(),
            body,
        )
        .unwrap()
        .with_priority(Some(sample::<DefinitionRulePriority>()))
        .unwrap()
        .with_simplification(Some(sample::<DefinitionSimplification>()))
        .with_claim(Some(sample::<DefinitionClaim>()))
        .with_requires(Some(condition))
        .unwrap();
        vec![rule]
    }
}

// The fields are private; use the constructor that accepts context aliases.
impl Sample for SemanticModule {
    fn samples() -> Vec<Self> {
        vec![Self::new_with_context_aliases(
            sample::<NodeOrigin>(),
            sample::<ModuleId>(),
            sample::<Vec<ModuleId>>(),
            sample::<Vec<SemanticSort>>(),
            sample::<Vec<SemanticSubsort>>(),
            sample::<Vec<SemanticProduction>>(),
            sample::<Vec<PrecedenceRelation>>(),
            sample::<Vec<GroupAssociativitySentence>>(),
            sample::<Option<SemanticConfiguration>>(),
            sample::<Vec<SemanticContextAlias>>(),
            sample::<Vec<SemanticRule>>(),
        )]
    }
}

// The fields are private; use the validating API constructor.
impl Sample for SemanticProduction {
    fn samples() -> Vec<Self> {
        let id = StableItemId::new(
            sample::<PackageId>(),
            ["syntax"],
            "Constructor",
            ItemKind::Constructor,
            "",
        )
        .unwrap();
        vec![Self::with_api(
            sample::<NodeOrigin>(),
            id,
            sample::<SemanticSortRef>(),
            sample::<Vec<SemanticProductionItem>>(),
            sample::<Vec<SemanticProductionAttribute>>(),
            sample::<RustVisibility>(),
            Some(sample::<ExplicitSymbol>()),
        )
        .unwrap()]
    }
}

// The fields are private; use the constructor and metadata setters.
impl Sample for SemanticRule {
    fn samples() -> Vec<Self> {
        let id = StableItemId::new(
            sample::<PackageId>(),
            ["syntax"],
            "Rule",
            ItemKind::Rule,
            "",
        )
        .unwrap();
        let term = sample::<SemanticTerm>();
        let body = SemanticTerm::rewrite(
            sample::<NodeOrigin>(),
            SemanticSortRef::Builtin(BuiltinSort::Int),
            term.clone(),
            term,
        )
        .unwrap();
        let condition = SemanticRuleCondition::new(
            sample::<NodeOrigin>(),
            SemanticTerm::variable(
                sample::<NodeOrigin>(),
                SemanticSortRef::Builtin(BuiltinSort::Bool),
                sample::<SemanticId>(),
            ),
        );
        let rule = Self::new(
            sample::<NodeOrigin>(),
            id,
            SentenceKind::Transition,
            sample::<Vec<SemanticVariable>>(),
            body,
        )
        .unwrap()
        .with_label(Some(sample::<SemanticRuleLabel>()))
        .with_priority(Some(sample::<SemanticRulePriority>()))
        .unwrap()
        .with_simplification(Some(sample::<SemanticSimplification>()))
        .with_claim(Some(sample::<SemanticClaim>()))
        .with_requires(Some(condition))
        .unwrap();
        vec![rule]
    }
}

// The fields are private; use the API constructor.
impl Sample for SemanticSort {
    fn samples() -> Vec<Self> {
        vec![Self::with_api(
            sample::<NodeOrigin>(),
            sample::<StableItemId>(),
            sample::<RustVisibility>(),
            Some(sample::<ExplicitSymbol>()),
        )]
    }
}
