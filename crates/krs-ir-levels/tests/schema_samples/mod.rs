//! Exhaustive typed examples for serde-reflection unsupported shapes.
use krs_ir::measure::*;
use krs_ir::wire::*;
use krs_ir::*;
use krs_ir_levels::*;
use serde::{Serialize, de::DeserializeOwned};
use std::collections::{BTreeMap, BTreeSet};

trait Sample: Sized {
    fn samples() -> Vec<Self>;
    fn first() -> Self {
        Self::samples().into_iter().next().unwrap()
    }
}
fn sample<T: Sample>() -> T {
    T::first()
}
fn sample_origin(key: &str) -> NodeOrigin {
    NodeOrigin::new(SourceMapKey::new(key).unwrap(), sample::<OriginStack>())
}
fn checked_samples<T>(
    values: Vec<T>,
    count: usize,
    name: &str,
    variant_index: impl Fn(&T) -> usize,
) -> Vec<T> {
    let mut seen = vec![false; count];
    for value in &values {
        seen[variant_index(value)] = true;
    }
    assert!(
        seen.into_iter().all(std::convert::identity),
        "{name} variant coverage"
    );
    values
}
macro_rules! sample_primitive {
    ($($ty:ty => $value:expr),* $(,)?) => {
        $(
            impl Sample for $ty {
                fn samples() -> Vec<Self> {
                    vec![$value]
                }
            }
        )*
    };
}
sample_primitive!(
    String => "sample".to_owned(),
    bool => true,
    u8 => 1,
    u16 => 1,
    u32 => 1,
    u64 => 1,
    usize => 1,
    i8 => 1,
    i16 => 1,
    i32 => 1,
    i64 => 1,
    f64 => 1.0,
);
impl<T: Sample> Sample for Option<T> {
    fn samples() -> Vec<Self> {
        vec![Some(sample::<T>())]
    }
}
impl<T: Sample> Sample for Vec<T> {
    fn samples() -> Vec<Self> {
        vec![vec![sample::<T>()]]
    }
}
impl<T: Sample> Sample for Box<T> {
    fn samples() -> Vec<Self> {
        vec![Box::new(sample::<T>())]
    }
}
impl<T: Sample + Ord> Sample for BTreeSet<T> {
    fn samples() -> Vec<Self> {
        vec![BTreeSet::from([sample::<T>()])]
    }
}
impl<K: Sample + Ord, V: Sample> Sample for BTreeMap<K, V> {
    fn samples() -> Vec<Self> {
        vec![BTreeMap::from([(sample::<K>(), sample::<V>())])]
    }
}
impl<A: Sample, B: Sample> Sample for (A, B) {
    fn samples() -> Vec<Self> {
        vec![(sample::<A>(), sample::<B>())]
    }
}
impl<A: Sample, B: Sample, C: Sample> Sample for (A, B, C) {
    fn samples() -> Vec<Self> {
        vec![(sample::<A>(), sample::<B>(), sample::<C>())]
    }
}
impl Sample for std::path::PathBuf {
    fn samples() -> Vec<Self> {
        vec!["src/lib.rs".into()]
    }
}

impl Sample for BuiltinOperation {
    fn samples() -> Vec<Self> {
        vec![Self::IntAdd]
    }
}
impl Sample for BuiltinSort {
    fn samples() -> Vec<Self> {
        vec![Self::KSequence]
    }
}
impl Sample for CellCollectionType {
    fn samples() -> Vec<Self> {
        vec![Self::Bag]
    }
}
impl Sample for CellMultiplicity {
    fn samples() -> Vec<Self> {
        vec![Self::Star]
    }
}
impl Sample for CellClauseKind {
    fn samples() -> Vec<Self> {
        vec![Self::Content, Self::Whole]
    }
}
impl Sample for CellStream {
    fn samples() -> Vec<Self> {
        vec![Self::Stdin]
    }
}
impl Sample for DescriptorCellStream {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: sample::<CellStream>(),
        }]
    }
}
impl Sample for DescriptorCellExit {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
        }]
    }
}
impl Sample for CellWrapper {
    fn samples() -> Vec<Self> {
        vec![Self::Cell]
    }
}
impl Sample for ClaimModality {
    fn samples() -> Vec<Self> {
        vec![Self::AllPaths]
    }
}
impl Sample for CollectorMeasureDocument {
    fn samples() -> Vec<Self> {
        vec![Self {
            schema: sample::<String>(),
            started_unix_seconds: sample::<f64>(),
            spans: sample::<Vec<Span>>(),
            counters: sample::<BTreeMap<String, u64>>(),
        }]
    }
}
impl Sample for CollectorPathProbe {
    fn samples() -> Vec<Self> {
        vec![Self {
            path: sample::<std::path::PathBuf>(),
            canonical: sample::<Option<std::path::PathBuf>>(),
            is_file: sample::<bool>(),
        }]
    }
}
impl Sample for CollectorReadSet {
    fn samples() -> Vec<Self> {
        vec![Self {
            files: sample::<Vec<(std::path::PathBuf, String)>>(),
            probes: sample::<Vec<CollectorPathProbe>>(),
        }]
    }
}
impl Sample for CountersDocument {
    fn samples() -> Vec<Self> {
        vec![Self {
            schema: sample::<String>(),
            command: sample::<String>(),
            status: sample::<String>(),
            counters: sample::<BTreeMap<String, u64>>(),
        }]
    }
}
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample for GeneratedOperation<S> {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::SortPredicate(sample::<S>()),
                Self::SortProjection(sample::<S>()),
            ],
            2,
            "GeneratedOperation",
            |value| match value {
                Self::SortPredicate(..) => 0,
                Self::SortProjection(..) => 1,
            },
        )
    }
}
impl Sample for SortTestKind {
    fn samples() -> Vec<Self> {
        vec![Self::Predicate, Self::Projection]
    }
}
impl Sample for DescriptorApplicationHeadClass {
    fn samples() -> Vec<Self> {
        vec![Self::Applied]
    }
}
impl Sample for DescriptorAssociativitySentence {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            associativity: sample::<GroupAssociativity>(),
            groups: sample::<Vec<DescriptorGroupReference>>(),
        }]
    }
}
impl Sample for DescriptorLexical {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
            regex_key: sample::<ProvenanceKey>(),
            regex: sample::<String>(),
        }]
    }
}
impl Sample for DescriptorSpecModuleName {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: sample::<String>(),
        }]
    }
}
impl Sample for DescriptorModuleImport {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            path: sample::<String>(),
        }]
    }
}
impl Sample for DescriptorLayoutRegex {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            regex: sample::<String>(),
        }]
    }
}
impl Sample for DescriptorCellColor {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: sample::<String>(),
        }]
    }
}
impl Sample for DescriptorCellDeclarationReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            declaration: sample::<StableItemId>(),
        }]
    }
}
impl Sample for DescriptorCellIdentity {
    fn samples() -> Vec<Self> {
        vec![Self {
            owner: sample::<StableItemId>(),
            field: sample::<String>(),
        }]
    }
}
impl Sample for DescriptorCellMultiplicity {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: sample::<String>(),
        }]
    }
}
impl Sample for DescriptorCellName {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: sample::<String>(),
        }]
    }
}
impl Sample for DescriptorCellReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            cell: sample::<DescriptorCellIdentity>(),
        }]
    }
}
impl Sample for DescriptorCellType {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: DescriptorCellCollectionType::Bag,
        }]
    }
}
impl Sample for DescriptorConfigurationReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            configuration: sample::<StableItemId>(),
        }]
    }
}
impl Sample for DescriptorContextAliasReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            alias: sample::<StableItemId>(),
        }]
    }
}
impl Sample for DescriptorFieldReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            field: sample::<ProductionFieldId>(),
        }]
    }
}
impl Sample for DescriptorColorEntry {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: sample::<String>(),
        }]
    }
}
impl Sample for DescriptorGroupReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            group: sample::<ProductionGroupId>(),
        }]
    }
}
impl Sample for DescriptorKSequenceNotation {
    fn samples() -> Vec<Self> {
        vec![Self::Comma]
    }
}
impl Sample for DescriptorLexicalPrecedence {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: sample::<u32>(),
        }]
    }
}
impl Sample for DescriptorPrecedenceChain {
    fn samples() -> Vec<Self> {
        let first = sample::<DescriptorGroupReference>();
        let mut second = first.clone();
        second.group = ProductionGroupId::new("second").unwrap();
        second.key = ProvenanceKey::new(ProvenanceRole::PrecedenceGroupReference, 1);
        vec![Self::new(sample::<ProvenanceKey>(), vec![first, second]).unwrap()]
    }
}

impl Sample for DescriptorRuleLabel {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
        }]
    }
}
impl Sample for DescriptorRulePriority {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: sample::<u32>(),
        }]
    }
}
impl Sample for DescriptorNondetGroup {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
        }]
    }
}
impl Sample for SemanticNondetGroup {
    fn samples() -> Vec<Self> {
        vec![Self::new(sample::<NodeOrigin>(), sample::<String>())]
    }
}
impl Sample for DescriptorSimplification {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            priority: sample::<Option<DescriptorSimplificationPriority>>(),
            restriction: sample::<Option<DescriptorMatchRestriction>>(),
        }]
    }
}
impl Sample for DescriptorEquationAttributes {
    fn samples() -> Vec<Self> {
        vec![Self {
            restriction: sample::<DescriptorMatchRestriction>(),
        }]
    }
}
impl Sample for DescriptorMatchRestriction {
    fn samples() -> Vec<Self> {
        vec![Self {
            concrete: sample::<Option<DescriptorRestriction>>(),
            symbolic: sample::<Option<DescriptorRestriction>>(),
            smt_lemma: sample::<Option<ProvenanceKey>>(),
        }]
    }
}
impl Sample for DescriptorRestriction {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            variables: sample::<Vec<DescriptorRestrictionVariable>>(),
        }]
    }
}
impl Sample for DescriptorRestrictionVariable {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
        }]
    }
}
impl Sample for IrMatchRestriction {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<Option<IrRestriction>>(),
            sample::<Option<IrRestriction>>(),
            sample::<Option<NodeOrigin>>(),
        )]
    }
}
impl Sample for IrRestriction {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<Vec<IrRestrictionVariable>>(),
        )]
    }
}
impl Sample for IrRestrictionVariable {
    fn samples() -> Vec<Self> {
        vec![Self::new(sample::<NodeOrigin>(), sample::<SemanticId>())]
    }
}
impl Sample for DescriptorUnboundVariables {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            variables: sample::<Vec<DescriptorUnboundVariable>>(),
        }]
    }
}
impl Sample for DescriptorUnboundVariable {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
        }]
    }
}
impl Sample for IrUnboundVariables {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<Vec<IrUnboundVariable>>(),
        )]
    }
}
impl Sample for IrUnboundVariable {
    fn samples() -> Vec<Self> {
        vec![
            Self::new(sample::<NodeOrigin>(), Some(sample::<SemanticId>())),
            Self::new(sample::<NodeOrigin>(), None),
        ]
    }
}
impl Sample for DescriptorSimplificationPriority {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: sample::<u32>(),
        }]
    }
}
impl Sample for GroupAssociativity {
    fn samples() -> Vec<Self> {
        vec![Self::Left]
    }
}
impl Sample for HookOperation {
    fn samples() -> Vec<Self> {
        vec![Self::KryptoKeccak256Raw]
    }
}
impl Sample for ItemKind {
    fn samples() -> Vec<Self> {
        vec![Self::Sort]
    }
}
impl Sample for ListOperation {
    fn samples() -> Vec<Self> {
        vec![Self::Empty]
    }
}
impl Sample for MapOperation {
    fn samples() -> Vec<Self> {
        vec![Self::Empty]
    }
}
impl Sample for RangedOriginKind {
    fn samples() -> Vec<Self> {
        vec![Self::Authored]
    }
}
impl Sample for SentenceKind {
    fn samples() -> Vec<Self> {
        vec![Self::Transition]
    }
}
impl Sample for SetOperation {
    fn samples() -> Vec<Self> {
        vec![Self::Empty]
    }
}
impl Sample for SortDescriptor {
    fn samples() -> Vec<Self> {
        vec![Self {
            parents: sample::<BTreeSet<StableItemId>>(),
        }]
    }
}
impl Sample for Span {
    fn samples() -> Vec<Self> {
        vec![Self {
            id: sample::<String>(),
            seconds: sample::<f64>(),
            depth: sample::<u8>(),
        }]
    }
}
impl Sample for StrictnessKind {
    fn samples() -> Vec<Self> {
        vec![Self::Strict]
    }
}
impl Sample for IntLiterals {
    fn samples() -> Vec<Self> {
        vec![Self::Unsigned]
    }
}
impl Sample for ModuleRole {
    fn samples() -> Vec<Self> {
        vec![Self::ProgramSyntax]
    }
}
impl Sample for PackageSettings {
    fn samples() -> Vec<Self> {
        vec![Self {
            package: sample::<PackageId>(),
            int_literals: IntLiterals::Unsigned,
            allow_raw_k: true,
            profile: RawKProfile::Strict,
        }]
    }
}
impl Sample for RawSentenceKind {
    fn samples() -> Vec<Self> {
        vec![Self::Rule]
    }
}
impl Sample for RawSentence {
    fn samples() -> Vec<Self> {
        vec![Self {
            origin: sample::<NodeOrigin>(),
            kind: RawSentenceKind::Rule,
            text: sample::<String>(),
            line: 1,
            column: 1,
            builtin_sorts: BTreeSet::from([BuiltinSort::Int]),
        }]
    }
}
impl Sample for SymbolKind {
    fn samples() -> Vec<Self> {
        vec![Self::Sort]
    }
}
impl Sample for TimingsDocument {
    fn samples() -> Vec<Self> {
        vec![Self {
            schema: sample::<String>(),
            command: sample::<String>(),
            status: sample::<String>(),
            failed_span: sample::<Option<String>>(),
            total_wall_seconds: sample::<f64>(),
            attributed_seconds: sample::<f64>(),
            unattributed_seconds: sample::<f64>(),
            spans: sample::<Vec<Span>>(),
        }]
    }
}
impl Sample for TransformationOriginKind {
    fn samples() -> Vec<Self> {
        vec![Self::GeneratedDescriptor]
    }
}
impl Sample for WireApplicationReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            target: TargetSlot(sample::<usize>()),
            authored_path: sample::<String>(),
        }]
    }
}
impl Sample for WireCellIdentity {
    fn samples() -> Vec<Self> {
        vec![Self {
            owner: TypeSlot(sample::<usize>()),
            field: TypeSlot(sample::<usize>()),
        }]
    }
}
impl Sample for WireCellReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            cell: sample::<WireCellIdentity>(),
        }]
    }
}
impl Sample for WireCellDeclarationReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            declaration: sample::<WireTypeReference>(),
        }]
    }
}
impl Sample for WireSortDescriptor {
    fn samples() -> Vec<Self> {
        vec![Self {
            parents: sample::<Vec<WireTypeReference>>(),
        }]
    }
}
impl Sample for WireConfigurationReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            configuration: sample::<WireTypeReference>(),
        }]
    }
}
impl Sample for WireConstructorDescriptor {
    fn samples() -> Vec<Self> {
        vec![Self {
            sort: sample::<WireSortReference>(),
            fields: sample::<Vec<WireConstructorFieldDescriptor>>(),
        }]
    }
}
impl Sample for WireConstructorFieldDescriptor {
    fn samples() -> Vec<Self> {
        vec![Self {
            name: sample::<String>(),
            sort: sample::<WireTypeReference>(),
        }]
    }
}
impl Sample for WireContextAliasReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            slot: ItemSlot(sample::<usize>()),
        }]
    }
}
impl Sample for WireHeadRuleCellReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
        }]
    }
}
impl Sample for WireSortReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            target: sample::<WireTypeReference>(),
        }]
    }
}
impl Sample for WireTypeReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            slot: TypeSlot(sample::<usize>()),
            authored_path: sample::<String>(),
        }]
    }
}
impl<F: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolCellDeclaration<F> {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            fields: sample::<Vec<F>>(),
        }]
    }
}
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolConfigurationVariable<S> {
    fn samples() -> Vec<Self> {
        vec![Self {
            binding_key: sample::<ProvenanceKey>(),
            binding: sample::<String>(),
            external_name_key: sample::<ProvenanceKey>(),
            external_name: sample::<String>(),
            sort: sample::<S>(),
            main_key: sample::<Option<ProvenanceKey>>(),
        }]
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolInitializerTerm<T> {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            term: sample::<T>(),
        }]
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolKSequenceItem<T> {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: sample::<ProtocolInitializerTerm<T>>(),
        }]
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolKSequence<T> {
    fn samples() -> Vec<Self> {
        vec![Self {
            payload_key: sample::<Option<ProvenanceKey>>(),
            dot_k_key: sample::<Option<ProvenanceKey>>(),
            notation: sample::<DescriptorKSequenceNotation>(),
            items: sample::<Vec<ProtocolKSequenceItem<T>>>(),
        }]
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolMapItem<T> {
    fn samples() -> Vec<Self> {
        vec![Self {
            key_key: sample::<ProvenanceKey>(),
            key: sample::<ProtocolInitializerTerm<T>>(),
            value_key: sample::<ProvenanceKey>(),
            value: sample::<ProtocolInitializerTerm<T>>(),
        }]
    }
}
impl<
    O: Sample + Clone + Serialize + DeserializeOwned,
    V: Sample + Clone + Serialize + DeserializeOwned,
    C: Sample + Clone + Serialize + DeserializeOwned,
> Sample for ProtocolConfigurationInitializer<O, V, C>
{
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            owner_key: sample::<ProvenanceKey>(),
            owner: sample::<O>(),
            variables: sample::<Vec<V>>(),
            body_key: sample::<ProvenanceKey>(),
            cells: sample::<Vec<C>>(),
        }]
    }
}
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolTypedBinding<S> {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
            sort: sample::<S>(),
        }]
    }
}
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolHeadRuleBinding<S> {
    fn samples() -> Vec<Self> {
        vec![Self {
            name: sample::<String>(),
            refinement: sample::<Option<S>>(),
        }]
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolRuleKSequenceItem<T> {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            value: sample::<T>(),
        }]
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolRuleMapItem<T> {
    fn samples() -> Vec<Self> {
        vec![Self {
            key_key: sample::<ProvenanceKey>(),
            key: sample::<T>(),
            value_key: sample::<ProvenanceKey>(),
            value: sample::<T>(),
        }]
    }
}
impl<
    D: Sample + Clone + Serialize + DeserializeOwned,
    S: Sample + Clone + Serialize + DeserializeOwned,
> Sample for ApplicationRef<D, S>
{
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Declared(sample::<D>()),
                Self::Builtin(sample::<BuiltinOperation>()),
                Self::Generated(GeneratedOperation::SortPredicate(sample::<S>())),
                Self::Generated(GeneratedOperation::SortProjection(sample::<S>())),
            ],
            3,
            "ApplicationRef",
            |value| match value {
                Self::Declared(..) => 0,
                Self::Builtin(..) => 1,
                Self::Generated(..) => 2,
            },
        )
    }
}
impl Sample for CellAttribute {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Color {
                    origin: sample::<NodeOrigin>(),
                    value: sample::<CellColor>(),
                },
                Self::Multiplicity {
                    origin: sample::<NodeOrigin>(),
                    value: sample::<CellMultiplicity>(),
                },
                Self::CollectionType {
                    origin: sample::<NodeOrigin>(),
                    value: sample::<CellCollectionType>(),
                },
                Self::Stream {
                    origin: sample::<NodeOrigin>(),
                    value: sample::<CellStream>(),
                },
                Self::Exit {
                    origin: sample::<NodeOrigin>(),
                },
            ],
            5,
            "CellAttribute",
            |value| match value {
                Self::Color { .. } => 0,
                Self::Multiplicity { .. } => 1,
                Self::CollectionType { .. } => 2,
                Self::Stream { .. } => 3,
                Self::Exit { .. } => 4,
            },
        )
    }
}
impl Sample for CellContentFrame {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Exact,
                Self::KSequenceTail {
                    origin: sample::<NodeOrigin>(),
                    binding: sample::<Option<SemanticId>>(),
                },
                Self::MapRemainder {
                    origin: sample::<NodeOrigin>(),
                    binding: sample::<Option<SemanticId>>(),
                },
                Self::ListRemainder {
                    origin: sample::<NodeOrigin>(),
                },
            ],
            4,
            "CellContentFrame",
            |value| match value {
                Self::Exact => 0,
                Self::KSequenceTail { .. } => 1,
                Self::MapRemainder { .. } => 2,
                Self::ListRemainder { .. } => 3,
            },
        )
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for CellPost<T> {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Preserve,
                Self::Replace {
                    term: sample::<T>(),
                },
            ],
            2,
            "CellPost",
            |value| match value {
                Self::Preserve => 0,
                Self::Replace { .. } => 1,
            },
        )
    }
}
impl Sample for ConfigurationRoot {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::GeneratedTop,
                Self::Named {
                    origin: sample::<NodeOrigin>(),
                    name: sample::<String>(),
                },
            ],
            2,
            "ConfigurationRoot",
            |value| match value {
                Self::GeneratedTop => 0,
                Self::Named { .. } => 1,
            },
        )
    }
}
impl Sample for DefinitionSentence {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::SyntaxSort(sample::<SyntaxSortSentence>()),
                Self::Subsort(sample::<SubsortSentence>()),
                Self::Production(sample::<ProductionSentence>()),
                Self::Precedence(sample::<PrecedenceRelation>()),
                Self::Associativity(sample::<GroupAssociativitySentence>()),
                Self::Configuration(sample::<ConfigurationSentence>()),
                Self::ContextAlias(sample::<ContextAliasSentence>()),
                Self::Rule(sample::<RuleSentence>()),
                Self::Lexical(sample::<LexicalSentence>()),
                Self::Layout(sample::<LayoutSentence>()),
                Self::Raw(sample::<RawSentence>()),
            ],
            11,
            "DefinitionSentence",
            |value| match value {
                Self::SyntaxSort(..) => 0,
                Self::Subsort(..) => 1,
                Self::Production(..) => 2,
                Self::Precedence(..) => 3,
                Self::Associativity(..) => 4,
                Self::Configuration(..) => 5,
                Self::ContextAlias(..) => 6,
                Self::Rule(..) => 7,
                Self::Lexical(..) => 8,
                Self::Layout(..) => 9,
                Self::Raw(..) => 10,
            },
        )
    }
}
impl Sample for DefinitionSortRef {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Declared(sample::<SymbolId>()),
                Self::Builtin(sample::<BuiltinSort>()),
                Self::Cell(sample::<SymbolId>()),
            ],
            3,
            "DefinitionSortRef",
            |value| match value {
                Self::Declared(..) => 0,
                Self::Builtin(..) => 1,
                Self::Cell(..) => 2,
            },
        )
    }
}
impl Sample for DefinitionTermKind {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Variable {
                    variable: sample::<SemanticId>(),
                },
                Self::Application {
                    application: sample::<DefinitionApplicationRef>(),
                    arguments: sample::<Vec<DefinitionTerm>>(),
                },
                Self::Token {
                    value: sample::<String>(),
                },
                Self::KSequence {
                    item_sort: sample::<DefinitionSortRef>(),
                    items: sample::<Vec<DefinitionTerm>>(),
                },
                Self::Map(Box::new(MapOperands::Items(NonEmpty::new(
                    MapEntry {
                        key: sample::<DefinitionTerm>(),
                        value: sample::<DefinitionTerm>(),
                    },
                    Vec::new(),
                )))),
                Self::List(Box::new(ListOperands::Item {
                    element: sample::<DefinitionTerm>(),
                })),
                Self::Set(Box::new(SetOperands::Item {
                    element: sample::<DefinitionTerm>(),
                })),
                Self::Cell {
                    cell: sample::<SymbolId>(),
                    children: sample::<Vec<DefinitionTerm>>(),
                },
                Self::Rewrite {
                    from: sample::<Box<DefinitionTerm>>(),
                    to: sample::<Box<DefinitionTerm>>(),
                },
                Self::As {
                    alias: sample::<SemanticId>(),
                    pattern: sample::<Box<DefinitionTerm>>(),
                },
                Self::Or {
                    alternatives: AtLeastTwo::new(
                        sample::<DefinitionTerm>(),
                        sample::<DefinitionTerm>(),
                        Vec::new(),
                    ),
                },
            ],
            11,
            "DefinitionTermKind",
            |value| match value {
                Self::Variable { .. } => 0,
                Self::Application { .. } => 1,
                Self::Token { .. } => 2,
                Self::KSequence { .. } => 3,
                Self::Map(_) => 4,
                Self::List(_) => 5,
                Self::Set(_) => 6,
                Self::Cell { .. } => 7,
                Self::Rewrite { .. } => 8,
                Self::As { .. } => 9,
                Self::Or { .. } => 10,
            },
        )
    }
}
impl Sample for DescriptorApplicationRef {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Declared(sample::<StableItemId>()),
                Self::Builtin(sample::<BuiltinOperation>()),
                Self::Map(TermMapOperation::Update),
                Self::List(sample::<ListOperation>()),
                Self::Set(sample::<SetOperation>()),
            ],
            5,
            "DescriptorApplicationRef",
            |value| match value {
                Self::Declared(..) => 0,
                Self::Builtin(..) => 1,
                Self::Map(..) => 2,
                Self::List(..) => 3,
                Self::Set(..) => 4,
            },
        )
    }
}
impl Sample for DescriptorConfigurationRoot {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::GeneratedTop,
                Self::Named {
                    key: sample::<ProvenanceKey>(),
                    name: sample::<String>(),
                },
            ],
            2,
            "DescriptorConfigurationRoot",
            |value| match value {
                Self::GeneratedTop => 0,
                Self::Named { .. } => 1,
            },
        )
    }
}
impl Sample for DescriptorLiteral {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Int(sample::<String>()),
                Self::Bool(sample::<bool>()),
                Self::String(sample::<String>()),
                Self::Float(sample::<String>()),
            ],
            4,
            "DescriptorLiteral",
            |value| match value {
                Self::Int(..) => 0,
                Self::Bool(..) => 1,
                Self::String(..) => 2,
                Self::Float(..) => 3,
            },
        )
    }
}
impl Sample for DescriptorPayload {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Sort(sample::<SortDescriptor>()),
                Self::Constructor(sample::<ConstructorDescriptor>()),
                Self::Grammar(sample::<Box<GrammarDescriptor>>()),
                Self::StructuredRule(sample::<Box<StructuredRuleDescriptor>>()),
                Self::FixedConfiguration(sample::<Box<DescriptorFixedConfiguration>>()),
                Self::Cell(sample::<Box<DescriptorCellDeclaration>>()),
                Self::ConfigurationRule(sample::<Box<DescriptorConfigurationRule>>()),
                Self::HeadRule(sample::<Box<crate::DescriptorHeadRule>>()),
                Self::ContextAlias(sample::<Box<DescriptorContextAlias>>()),
            ],
            9,
            "DescriptorPayload",
            |value| match value {
                Self::Sort(..) => 0,
                Self::Constructor(..) => 1,
                Self::Grammar(..) => 2,
                Self::StructuredRule(..) => 3,
                Self::FixedConfiguration(..) => 4,
                Self::Cell(..) => 5,
                Self::ConfigurationRule(..) => 6,
                Self::HeadRule(..) => 7,
                Self::ContextAlias(..) => 8,
            },
        )
    }
}
impl Sample for DescriptorProductionAttribute {
    #[expect(
        clippy::too_many_lines,
        reason = "One sample per production-attribute variant."
    )]
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Documentation {
                    key: sample::<ProvenanceKey>(),
                    text: sample::<String>(),
                },
                Self::Function {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Total {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Hook {
                    key: sample::<ProvenanceKey>(),
                    operation: sample::<HookOperation>(),
                },
                Self::Alias {
                    key: sample::<ProvenanceKey>(),
                    recursive: sample::<Option<ProvenanceKey>>(),
                },
                Self::Token {
                    key: sample::<ProvenanceKey>(),
                    lexical_precedence: sample::<Option<DescriptorLexicalPrecedence>>(),
                },
                Self::Group {
                    reference: sample::<DescriptorGroupReference>(),
                },
                Self::Bracket {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Avoid {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Format {
                    key: sample::<ProvenanceKey>(),
                    fragments: sample::<Vec<DescriptorFormatFragment>>(),
                },
                Self::Strictness {
                    key: sample::<ProvenanceKey>(),
                    kind: sample::<StrictnessKind>(),
                    using: sample::<Option<DescriptorContextAliasReference>>(),
                    fields: sample::<Vec<DescriptorFieldReference>>(),
                    result_sort: sample::<Box<DescriptorSortReference>>(),
                },
                Self::Internal {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Program {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Color {
                    key: sample::<ProvenanceKey>(),
                    value: sample::<String>(),
                },
                Self::Colors {
                    key: sample::<ProvenanceKey>(),
                    values: sample::<Vec<DescriptorColorEntry>>(),
                },
                Self::Prefer {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Overload {
                    target: sample::<DescriptorApplicationReference>(),
                },
                Self::Memo {
                    key: sample::<ProvenanceKey>(),
                },
                Self::ListCons {
                    key: sample::<ProvenanceKey>(),
                    separator_key: sample::<ProvenanceKey>(),
                    separator: sample::<String>(),
                    non_empty: sample::<Option<ProvenanceKey>>(),
                    terminator: sample::<DescriptorApplicationReference>(),
                },
                Self::ListTerminator {
                    cons: sample::<DescriptorApplicationReference>(),
                },
                Self::RawHook {
                    key: sample::<ProvenanceKey>(),
                    namespace: sample::<String>(),
                    name: sample::<String>(),
                },
                Self::FreshGenerator {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Smtlib {
                    key: sample::<ProvenanceKey>(),
                    symbol: sample::<String>(),
                },
                Self::SmtHook {
                    key: sample::<ProvenanceKey>(),
                    template: sample::<Vec<DescriptorSmtFragment>>(),
                },
                Self::Desugar {
                    key: sample::<ProvenanceKey>(),
                    recursive: sample::<Option<ProvenanceKey>>(),
                },
            ],
            25,
            "DescriptorProductionAttribute",
            |value| match value {
                Self::Documentation { .. } => 0,
                Self::Function { .. } => 1,
                Self::Total { .. } => 2,
                Self::Hook { .. } => 3,
                Self::Alias { .. } => 4,
                Self::Token { .. } => 5,
                Self::Group { .. } => 6,
                Self::Bracket { .. } => 7,
                Self::Avoid { .. } => 8,
                Self::Format { .. } => 9,
                Self::Strictness { .. } => 10,
                Self::Internal { .. } => 11,
                Self::Program { .. } => 12,
                Self::Color { .. } => 13,
                Self::Colors { .. } => 14,
                Self::Prefer { .. } => 15,
                Self::Overload { .. } => 16,
                Self::Memo { .. } => 17,
                Self::ListCons { .. } => 18,
                Self::ListTerminator { .. } => 19,
                Self::RawHook { .. } => 20,
                Self::FreshGenerator { .. } => 21,
                Self::Smtlib { .. } => 22,
                Self::SmtHook { .. } => 23,
                Self::Desugar { .. } => 24,
            },
        )
    }
}
impl Sample for DescriptorProductionItem {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Terminal {
                    key: sample::<ProvenanceKey>(),
                    text: sample::<String>(),
                },
                Self::NonTerminal {
                    key: sample::<ProvenanceKey>(),
                    field_key: sample::<ProvenanceKey>(),
                    declaration_key: sample::<Option<ProvenanceKey>>(),
                    field: sample::<ProductionFieldId>(),
                    sort: sample::<Box<DescriptorSortReference>>(),
                },
                Self::RegexTerminal {
                    key: sample::<ProvenanceKey>(),
                    precede_regex: sample::<Option<String>>(),
                    regex: sample::<String>(),
                    follow_regex: sample::<Option<String>>(),
                },
            ],
            3,
            "DescriptorProductionItem",
            |value| match value {
                Self::Terminal { .. } => 0,
                Self::NonTerminal { .. } => 1,
                Self::RegexTerminal { .. } => 2,
            },
        )
    }
}
impl Sample for DescriptorProductionOwner {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Constructor {
                    constructor: sample::<DescriptorApplicationReference>(),
                },
                Self::TokenSort {
                    sort: sample::<DescriptorSortReference>(),
                },
                Self::BracketSort {
                    sort: sample::<DescriptorSortReference>(),
                },
            ],
            3,
            "DescriptorProductionOwner",
            |value| match value {
                Self::Constructor { .. } => 0,
                Self::TokenSort { .. } => 1,
                Self::BracketSort { .. } => 2,
            },
        )
    }
}
impl Sample for DescriptorSortRef {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Declared(sample::<StableItemId>()),
                Self::Builtin(sample::<BuiltinSort>()),
                Self::Cell(sample::<StableItemId>()),
            ],
            3,
            "DescriptorSortRef",
            |value| match value {
                Self::Declared(..) => 0,
                Self::Builtin(..) => 1,
                Self::Cell(..) => 2,
            },
        )
    }
}
impl Sample for DescriptorTerm {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Variable {
                    key: sample::<ProvenanceKey>(),
                    path_key: sample::<ProvenanceKey>(),
                    name: sample::<String>(),
                },
                Self::Application {
                    head_class: sample::<DescriptorApplicationHeadClass>(),
                    reference: sample::<DescriptorApplicationReference>(),
                    path_key: sample::<ProvenanceKey>(),
                    arguments: sample::<Vec<DescriptorTermArgument>>().try_into().unwrap(),
                },
                Self::Literal {
                    key: sample::<ProvenanceKey>(),
                    literal: sample::<DescriptorLiteral>(),
                },
                Self::Wildcard {
                    key: sample::<ProvenanceKey>(),
                },
                Self::BuiltinToken {
                    key: sample::<ProvenanceKey>(),
                    sort: sample::<BuiltinSort>(),
                    value: sample::<String>(),
                },
                Self::Anonymous {
                    key: sample::<ProvenanceKey>(),
                    sort: sample::<DescriptorSortReference>(),
                    spelling: sample::<String>(),
                },
                Self::OrBool {
                    key: sample::<ProvenanceKey>(),
                    arguments: AtLeastTwo::new(
                        sample::<DescriptorTerm>(),
                        sample::<DescriptorTerm>(),
                        Vec::new(),
                    ),
                },
                Self::Cell {
                    key: sample::<ProvenanceKey>(),
                    declaration: sample::<StableItemId>(),
                    fields: sample::<Vec<DescriptorCellTermField>>(),
                },
                Self::Lexeme {
                    key: sample::<ProvenanceKey>(),
                    sort: sample::<DescriptorSortReference>(),
                    text: sample::<String>(),
                },
                Self::SortTest {
                    key: sample::<ProvenanceKey>(),
                    kind: SortTestKind::Predicate,
                    sort: sample::<DescriptorSortReference>(),
                    operand: Box::new(sample::<DescriptorTerm>()),
                },
                Self::SortTest {
                    key: sample::<ProvenanceKey>(),
                    kind: SortTestKind::Projection,
                    sort: sample::<DescriptorSortReference>(),
                    operand: Box::new(sample::<DescriptorTerm>()),
                },
                Self::As {
                    key: sample::<ProvenanceKey>(),
                    binding_key: sample::<ProvenanceKey>(),
                    name: sample::<String>(),
                    pattern: Box::new(sample::<DescriptorTerm>()),
                },
                Self::Or {
                    key: sample::<ProvenanceKey>(),
                    alternatives: AtLeastTwo::new(
                        sample::<DescriptorTerm>(),
                        sample::<DescriptorTerm>(),
                        Vec::new(),
                    ),
                },
            ],
            12,
            "DescriptorTerm",
            |value| match value {
                Self::Variable { .. } => 0,
                Self::Application { .. } => 1,
                Self::Literal { .. } => 2,
                Self::Wildcard { .. } => 3,
                Self::BuiltinToken { .. } => 4,
                Self::Anonymous { .. } => 5,
                Self::OrBool { .. } => 6,
                Self::Cell { .. } => 7,
                Self::Lexeme { .. } => 8,
                Self::SortTest { .. } => 9,
                Self::As { .. } => 10,
                Self::Or { .. } => 11,
            },
        )
    }
    // Recursive DescriptorTerm variants need a terminal first sample.
    fn first() -> Self {
        Self::Variable {
            key: sample::<ProvenanceKey>(),
            path_key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
        }
    }
}
impl Sample for DescriptorTermArgument {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Positional {
                    value: sample::<Box<DescriptorTerm>>(),
                },
                Self::Named {
                    key: sample::<ProvenanceKey>(),
                    field: sample::<ProductionFieldId>(),
                    value: sample::<Box<DescriptorTerm>>(),
                },
            ],
            2,
            "DescriptorTermArgument",
            |value| match value {
                Self::Positional { .. } => 0,
                Self::Named { .. } => 1,
            },
        )
    }
}
impl<
    S: Sample + Clone + Serialize + DeserializeOwned,
    C: Sample + Clone + Serialize + DeserializeOwned,
> Sample for FixedCellContent<S, C>
{
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Term {
                    sort: sample::<S>(),
                },
                Self::Children {
                    children: sample::<Vec<FixedCell<S, C>>>(),
                },
            ],
            2,
            "FixedCellContent",
            |value| match value {
                Self::Term { .. } => 0,
                Self::Children { .. } => 1,
            },
        )
    }
    // Children contain FixedCellContent again, so start with a term.
    fn first() -> Self {
        Self::Term {
            sort: sample::<S>(),
        }
    }
}
impl<
    C: Sample + Clone + Serialize + DeserializeOwned,
    T: Sample + Clone + Serialize + DeserializeOwned,
> Sample for FixedInitializerContent<C, T>
{
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Term {
                    term: sample::<T>(),
                },
                Self::Children {
                    children: sample::<Vec<FixedInitializerCell<C, T>>>(),
                },
            ],
            2,
            "FixedInitializerContent",
            |value| match value {
                Self::Term { .. } => 0,
                Self::Children { .. } => 1,
            },
        )
    }
    // Children contain FixedInitializerContent again, so start with a term.
    fn first() -> Self {
        Self::Term {
            term: sample::<T>(),
        }
    }
}
impl Sample for FormatFragment {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Literal(sample::<String>()),
                Self::Item(sample::<u16>()),
                Self::Newline,
                Self::Indent,
                Self::Dedent,
                Self::ColorNext,
                Self::ColorReset,
            ],
            7,
            "FormatFragment",
            |value| match value {
                Self::Literal(..) => 0,
                Self::Item(..) => 1,
                Self::Newline => 2,
                Self::Indent => 3,
                Self::Dedent => 4,
                Self::ColorNext => 5,
                Self::ColorReset => 6,
            },
        )
    }
}
impl Sample for GrammarDescriptor {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Production(sample::<DescriptorProduction>()),
                Self::Subsort {
                    key: sample::<ProvenanceKey>(),
                    subsort: sample::<DescriptorSortReference>(),
                    supersort: sample::<DescriptorSortReference>(),
                },
                Self::Precedence {
                    key: sample::<ProvenanceKey>(),
                    chains: sample::<Vec<DescriptorPrecedenceChain>>(),
                },
                Self::Associativity {
                    key: sample::<ProvenanceKey>(),
                    sentences: sample::<Vec<DescriptorAssociativitySentence>>(),
                },
                Self::Tokens {
                    productions: vec![sample::<DescriptorProduction>()],
                },
                Self::Lexical {
                    lexicals: sample::<Vec<DescriptorLexical>>(),
                },
                Self::Layout {
                    regexes: sample::<Vec<DescriptorLayoutRegex>>(),
                },
                Self::RawSentence {
                    key: sample::<ProvenanceKey>(),
                    kind: sample::<RawSentenceKind>(),
                    text: sample::<String>(),
                    line: sample::<u32>(),
                    column: sample::<u32>(),
                },
                Self::SpecModule {
                    key: sample::<ProvenanceKey>(),
                    name: Some(sample::<DescriptorSpecModuleName>()),
                    imports: sample::<Vec<DescriptorModuleImport>>(),
                },
            ],
            9,
            "GrammarDescriptor",
            |value| match value {
                Self::Production(..) => 0,
                Self::Subsort { .. } => 1,
                Self::Precedence { .. } => 2,
                Self::Associativity { .. } => 3,
                Self::Tokens { .. } => 4,
                Self::Lexical { .. } => 5,
                Self::Layout { .. } => 6,
                Self::RawSentence { .. } => 7,
                Self::SpecModule { .. } => 8,
            },
        )
    }
}
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample for GrammarProductionItemKind<S> {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Terminal {
                    text: sample::<String>(),
                },
                Self::NonTerminal {
                    field: sample::<ProductionFieldId>(),
                    sort: sample::<S>(),
                },
                Self::RegexTerminal {
                    precede_regex: sample::<Option<String>>(),
                    regex: sample::<String>(),
                    follow_regex: sample::<Option<String>>(),
                },
            ],
            3,
            "GrammarProductionItemKind",
            |value| match value {
                Self::Terminal { .. } => 0,
                Self::NonTerminal { .. } => 1,
                Self::RegexTerminal { .. } => 2,
            },
        )
    }
}
impl Sample for OriginFrame {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Ranged {
                    kind: sample::<RangedOriginKind>(),
                    range: sample::<SourceRange>(),
                    item: sample::<Option<StableItemId>>(),
                    label: sample::<Option<String>>(),
                },
                Self::Transformation {
                    kind: sample::<TransformationOriginKind>(),
                    item: sample::<Option<StableItemId>>(),
                    label: sample::<Option<String>>(),
                },
            ],
            2,
            "OriginFrame",
            |value| match value {
                Self::Ranged { .. } => 0,
                Self::Transformation { .. } => 1,
            },
        )
    }
}
impl<
    S: Sample + Clone + Serialize + DeserializeOwned,
    D: Sample + Clone + Serialize + DeserializeOwned,
> Sample for ProductionAttribute<S, D>
{
    #[expect(
        clippy::too_many_lines,
        reason = "One sample per production-attribute variant."
    )]
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Documentation {
                    origin: sample::<NodeOrigin>(),
                    text: sample::<String>(),
                },
                Self::Function {
                    origin: sample::<NodeOrigin>(),
                },
                Self::Total {
                    origin: sample::<NodeOrigin>(),
                },
                Self::Hook {
                    origin: sample::<NodeOrigin>(),
                    operation: sample::<HookOperation>(),
                },
                Self::Alias {
                    origin: sample::<NodeOrigin>(),
                    recursive: true,
                },
                Self::Token {
                    origin: sample::<NodeOrigin>(),
                    lexical_precedence: sample::<Option<u32>>(),
                },
                Self::Group {
                    origin: sample::<NodeOrigin>(),
                    group: sample::<ProductionGroupId>(),
                },
                Self::Bracket {
                    origin: sample::<NodeOrigin>(),
                },
                Self::Avoid {
                    origin: sample::<NodeOrigin>(),
                },
                Self::Format {
                    origin: sample::<NodeOrigin>(),
                    fragments: sample::<Vec<FormatFragment>>(),
                },
                Self::Strictness {
                    origin: sample::<NodeOrigin>(),
                    kind: sample::<StrictnessKind>(),
                    using: sample::<Option<ProductionContextAliasReference>>(),
                    fields: sample::<Vec<ProductionFieldReference>>(),
                    result_sort: sample::<ProductionResultSort<S>>(),
                },
                Self::Internal {
                    origin: sample::<NodeOrigin>(),
                },
                Self::Program {
                    origin: sample::<NodeOrigin>(),
                },
                Self::Color {
                    origin: sample::<NodeOrigin>(),
                    value: sample::<String>(),
                },
                Self::Colors {
                    origin: sample::<NodeOrigin>(),
                    values: sample::<Vec<String>>(),
                },
                Self::Prefer {
                    origin: sample::<NodeOrigin>(),
                },
                Self::Overload {
                    origin: sample::<NodeOrigin>(),
                    target: sample::<D>(),
                },
                Self::Private {
                    origin: sample::<NodeOrigin>(),
                },
                Self::Memo {
                    origin: sample::<NodeOrigin>(),
                },
                Self::ListCons {
                    origin: sample::<NodeOrigin>(),
                    separator: sample::<String>(),
                    non_empty: sample::<bool>(),
                    terminator: sample::<D>(),
                },
                Self::ListTerminator {
                    origin: sample::<NodeOrigin>(),
                    cons: sample::<D>(),
                },
                Self::RawHook {
                    origin: sample::<NodeOrigin>(),
                    namespace: sample::<String>(),
                    name: sample::<String>(),
                },
                Self::FreshGenerator {
                    origin: sample::<NodeOrigin>(),
                },
                Self::Smtlib {
                    origin: sample::<NodeOrigin>(),
                    symbol: sample::<String>(),
                },
                Self::SmtHook {
                    origin: sample::<NodeOrigin>(),
                    template: sample::<Vec<SmtFragment>>(),
                },
                Self::Desugar {
                    origin: sample::<NodeOrigin>(),
                    recursive: true,
                },
            ],
            26,
            "ProductionAttribute",
            |value| match value {
                Self::Documentation { .. } => 0,
                Self::Function { .. } => 1,
                Self::Total { .. } => 2,
                Self::Hook { .. } => 3,
                Self::Alias { .. } => 4,
                Self::Token { .. } => 5,
                Self::Group { .. } => 6,
                Self::Bracket { .. } => 7,
                Self::Avoid { .. } => 8,
                Self::Format { .. } => 9,
                Self::Strictness { .. } => 10,
                Self::Internal { .. } => 11,
                Self::Program { .. } => 12,
                Self::Color { .. } => 13,
                Self::Colors { .. } => 14,
                Self::Prefer { .. } => 15,
                Self::Overload { .. } => 16,
                Self::Private { .. } => 17,
                Self::Memo { .. } => 18,
                Self::ListCons { .. } => 19,
                Self::ListTerminator { .. } => 20,
                Self::RawHook { .. } => 21,
                Self::FreshGenerator { .. } => 22,
                Self::Smtlib { .. } => 23,
                Self::SmtHook { .. } => 24,
                Self::Desugar { .. } => 25,
            },
        )
    }
}
impl<
    S: Sample + Clone + Serialize + DeserializeOwned,
    N: Sample + Clone + Serialize + DeserializeOwned,
> Sample for ProtocolCellContent<S, N>
{
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Leaf {
                    wrapper_key: sample::<ProvenanceKey>(),
                    wrapper: sample::<CellWrapper>(),
                    sort: sample::<S>(),
                    arguments: sample::<Vec<S>>(),
                },
                Self::Nested {
                    declaration: sample::<N>(),
                },
            ],
            2,
            "ProtocolCellContent",
            |value| match value {
                Self::Leaf { .. } => 0,
                Self::Nested { .. } => 1,
            },
        )
    }
}
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample
    for ProtocolContextAliasBindingKind<S>
{
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Here,
                Self::Term {
                    sort: sample::<S>(),
                },
                Self::KSequenceFrame,
                Self::MapFrame,
                Self::ConfigurationFrame,
            ],
            5,
            "ProtocolContextAliasBindingKind",
            |value| match value {
                Self::Here => 0,
                Self::Term { .. } => 1,
                Self::KSequenceFrame => 2,
                Self::MapFrame => 3,
                Self::ConfigurationFrame => 4,
            },
        )
    }
}
impl<
    I: Sample + Clone + Serialize + DeserializeOwned,
    T: Sample + Clone + Serialize + DeserializeOwned,
> Sample for ProtocolHeadRuleExtra<I, T>
{
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::HaveMap {
                    cell: sample::<I>(),
                    key: sample::<T>(),
                    value_binding: sample::<String>(),
                },
                Self::UpdateMap {
                    cell: sample::<I>(),
                    base_binding: sample::<String>(),
                    update: sample::<T>(),
                },
                Self::RewriteCell {
                    cell: sample::<I>(),
                    result_key: sample::<ProvenanceKey>(),
                    before: sample::<T>(),
                    after: sample::<T>(),
                },
            ],
            3,
            "ProtocolHeadRuleExtra",
            |value| match value {
                Self::HaveMap { .. } => 0,
                Self::UpdateMap { .. } => 1,
                Self::RewriteCell { .. } => 2,
            },
        )
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolHeadRuleHead<T> {
    fn samples() -> Vec<Self> {
        vec![Self {
            subject: sample::<T>(),
            result: sample::<ProtocolHeadRuleResult<T>>(),
        }]
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolHeadRuleResult<T> {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Replace(sample::<T>()),
                Self::Splice(sample::<Vec<T>>()),
                Self::Erase,
            ],
            3,
            "ProtocolHeadRuleResult",
            |value| match value {
                Self::Replace(..) => 0,
                Self::Splice(..) => 1,
                Self::Erase => 2,
            },
        )
    }
}
impl<
    I: Sample + Clone + Serialize + DeserializeOwned,
    N: Sample + Clone + Serialize + DeserializeOwned,
    T: Sample + Clone + Serialize + DeserializeOwned,
> Sample for ProtocolInitializerCellContent<I, N, T>
{
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Leaf {
                    constructor_key: sample::<ProvenanceKey>(),
                    wrapper: sample::<CellWrapper>(),
                    value: sample::<T>(),
                },
                Self::Nested {
                    declaration: sample::<N>(),
                    children: sample::<Vec<ProtocolInitializerCell<I, N, T>>>(),
                },
            ],
            2,
            "ProtocolInitializerCellContent",
            |value| match value {
                Self::Leaf { .. } => 0,
                Self::Nested { .. } => 1,
            },
        )
    }
    // Nested cells contain ProtocolInitializerCellContent again.
    fn first() -> Self {
        Self::Leaf {
            constructor_key: sample::<ProvenanceKey>(),
            wrapper: sample::<CellWrapper>(),
            value: sample::<T>(),
        }
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolInitializerStateTerm<T> {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Term(sample::<ProtocolInitializerTerm<T>>()),
                Self::KSequence(sample::<ProtocolKSequence<T>>()),
                Self::Map(sample::<ProtocolMap<T>>()),
            ],
            3,
            "ProtocolInitializerStateTerm",
            |value| match value {
                Self::Term(..) => 0,
                Self::KSequence(..) => 1,
                Self::Map(..) => 2,
            },
        )
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolMapBody<T> {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Empty {
                    explicit_dot: sample::<bool>(),
                },
                Self::Items {
                    items: sample::<Vec<ProtocolMapItem<T>>>(),
                },
                Self::Update {
                    base_key: sample::<ProvenanceKey>(),
                    base: sample::<ProtocolInitializerTerm<T>>(),
                    key_key: sample::<ProvenanceKey>(),
                    key: sample::<ProtocolInitializerTerm<T>>(),
                    value_key: sample::<ProvenanceKey>(),
                    value: sample::<ProtocolInitializerTerm<T>>(),
                },
            ],
            3,
            "ProtocolMapBody",
            |value| match value {
                Self::Empty { .. } => 0,
                Self::Items { .. } => 1,
                Self::Update { .. } => 2,
            },
        )
    }
}
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolRuleBindingKind<S> {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Term {
                    sort: sample::<S>(),
                },
                Self::KSequenceFrame,
                Self::MapFrame,
                Self::ConfigurationFrame,
            ],
            4,
            "ProtocolRuleBindingKind",
            |value| match value {
                Self::Term { .. } => 0,
                Self::KSequenceFrame => 1,
                Self::MapFrame => 2,
                Self::ConfigurationFrame => 3,
            },
        )
    }
}
impl Sample for ProtocolRuleFrame {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Exact,
                Self::Anonymous {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Bind {
                    key: sample::<ProvenanceKey>(),
                    binding: sample::<String>(),
                },
                Self::Reuse {
                    key: sample::<ProvenanceKey>(),
                    binding: sample::<String>(),
                },
            ],
            4,
            "ProtocolRuleFrame",
            |value| match value {
                Self::Exact => 0,
                Self::Anonymous { .. } => 1,
                Self::Bind { .. } => 2,
                Self::Reuse { .. } => 3,
            },
        )
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolRuleMapBody<T> {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Empty {
                    explicit_dot: sample::<bool>(),
                },
                Self::Items {
                    items: sample::<Vec<ProtocolRuleMapItem<T>>>(),
                    remainder: sample::<ProtocolRuleFrame>(),
                },
                Self::Update {
                    base_key: sample::<ProvenanceKey>(),
                    base: sample::<T>(),
                    key_key: sample::<ProvenanceKey>(),
                    key: sample::<T>(),
                    value_key: sample::<ProvenanceKey>(),
                    value: sample::<T>(),
                },
            ],
            3,
            "ProtocolRuleMapBody",
            |value| match value {
                Self::Empty { .. } => 0,
                Self::Items { .. } => 1,
                Self::Update { .. } => 2,
            },
        )
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolRuleStateTerm<T> {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Term(sample::<T>()),
                Self::KSequence(sample::<ProtocolRuleKSequence<T>>()),
                Self::Map(sample::<ProtocolRuleMap<T>>()),
                Self::Group(sample::<T>()),
            ],
            4,
            "ProtocolRuleStateTerm",
            |value| match value {
                Self::Term(..) => 0,
                Self::KSequence(..) => 1,
                Self::Map(..) => 2,
                Self::Group(..) => 3,
            },
        )
    }
}
impl Sample for RustVisibility {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Inherited,
                Self::Public,
                Self::Restricted {
                    path: sample::<String>(),
                    explicit_in: sample::<bool>(),
                },
            ],
            3,
            "RustVisibility",
            |value| match value {
                Self::Inherited => 0,
                Self::Public => 1,
                Self::Restricted { .. } => 2,
            },
        )
    }
}
impl Sample for SemanticSortRef {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Declared(sample::<StableItemId>()),
                Self::Builtin(sample::<BuiltinSort>()),
                Self::Cell(sample::<StableItemId>()),
            ],
            3,
            "SemanticSortRef",
            |value| match value {
                Self::Declared(..) => 0,
                Self::Builtin(..) => 1,
                Self::Cell(..) => 2,
            },
        )
    }
}
impl Sample for SemanticTermKind {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Variable {
                    variable: sample::<SemanticId>(),
                },
                Self::Application {
                    application: sample::<SemanticApplicationRef>(),
                    arguments: sample::<Vec<SemanticTerm>>(),
                },
                Self::Token {
                    value: sample::<String>(),
                },
                Self::KSequence {
                    item_sort: sample::<SemanticSortRef>(),
                    items: sample::<Vec<SemanticTerm>>(),
                },
                Self::Map(Box::new(MapOperands::Items(NonEmpty::new(
                    MapEntry {
                        key: sample::<SemanticTerm>(),
                        value: sample::<SemanticTerm>(),
                    },
                    Vec::new(),
                )))),
                Self::List(Box::new(ListOperands::Item {
                    element: sample::<SemanticTerm>(),
                })),
                Self::Set(Box::new(SetOperands::Item {
                    element: sample::<SemanticTerm>(),
                })),
                Self::Cell {
                    cell: sample::<SemanticId>(),
                    children: sample::<Vec<SemanticTerm>>(),
                },
                Self::Rewrite {
                    from: sample::<Box<SemanticTerm>>(),
                    to: sample::<Box<SemanticTerm>>(),
                },
                Self::As {
                    alias: sample::<SemanticId>(),
                    pattern: sample::<Box<SemanticTerm>>(),
                },
                Self::Or {
                    alternatives: AtLeastTwo::new(
                        sample::<SemanticTerm>(),
                        sample::<SemanticTerm>(),
                        Vec::new(),
                    ),
                },
            ],
            11,
            "SemanticTermKind",
            |value| match value {
                Self::Variable { .. } => 0,
                Self::Application { .. } => 1,
                Self::Token { .. } => 2,
                Self::KSequence { .. } => 3,
                Self::Map(_) => 4,
                Self::List(_) => 5,
                Self::Set(_) => 6,
                Self::Cell { .. } => 7,
                Self::Rewrite { .. } => 8,
                Self::As { .. } => 9,
                Self::Or { .. } => 10,
            },
        )
    }
}
impl Sample for WireGrammarDescriptor {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Production(sample::<WireProduction>()),
                Self::Subsort {
                    key: sample::<ProvenanceKey>(),
                    subsort: sample::<WireSortReference>(),
                    supersort: sample::<WireSortReference>(),
                },
                Self::Precedence {
                    key: sample::<ProvenanceKey>(),
                    chains: sample::<Vec<DescriptorPrecedenceChain>>(),
                },
                Self::Associativity {
                    key: sample::<ProvenanceKey>(),
                    sentences: sample::<Vec<DescriptorAssociativitySentence>>(),
                },
                Self::Tokens {
                    productions: vec![sample::<WireProduction>()],
                },
                Self::Lexical {
                    lexicals: sample::<Vec<DescriptorLexical>>(),
                },
                Self::Layout {
                    regexes: sample::<Vec<DescriptorLayoutRegex>>(),
                },
                Self::RawSentence {
                    key: sample::<ProvenanceKey>(),
                    kind: sample::<RawSentenceKind>(),
                    text: sample::<String>(),
                    line: sample::<u32>(),
                    column: sample::<u32>(),
                },
                Self::SpecModule {
                    key: sample::<ProvenanceKey>(),
                    name: Some(sample::<DescriptorSpecModuleName>()),
                    imports: sample::<Vec<DescriptorModuleImport>>(),
                },
            ],
            9,
            "WireGrammarDescriptor",
            |value| match value {
                Self::Production(..) => 0,
                Self::Subsort { .. } => 1,
                Self::Precedence { .. } => 2,
                Self::Associativity { .. } => 3,
                Self::Tokens { .. } => 4,
                Self::Lexical { .. } => 5,
                Self::Layout { .. } => 6,
                Self::RawSentence { .. } => 7,
                Self::SpecModule { .. } => 8,
            },
        )
    }
}
impl Sample for WireProductionAttribute {
    #[expect(
        clippy::too_many_lines,
        reason = "One sample per production-attribute variant."
    )]
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Documentation {
                    key: sample::<ProvenanceKey>(),
                    text: sample::<String>(),
                },
                Self::Function {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Total {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Hook {
                    key: sample::<ProvenanceKey>(),
                    operation: sample::<HookOperation>(),
                },
                Self::Alias {
                    key: sample::<ProvenanceKey>(),
                    recursive: sample::<Option<ProvenanceKey>>(),
                },
                Self::Token {
                    key: sample::<ProvenanceKey>(),
                    lexical_precedence: sample::<Option<DescriptorLexicalPrecedence>>(),
                },
                Self::Group {
                    reference: sample::<DescriptorGroupReference>(),
                },
                Self::Bracket {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Avoid {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Format {
                    key: sample::<ProvenanceKey>(),
                    fragments: sample::<Vec<DescriptorFormatFragment>>(),
                },
                Self::Strictness {
                    key: sample::<ProvenanceKey>(),
                    kind: sample::<StrictnessKind>(),
                    using: sample::<Option<WireContextAliasReference>>(),
                    fields: sample::<Vec<DescriptorFieldReference>>(),
                    result_sort: sample::<Box<WireSortReference>>(),
                },
                Self::Internal {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Program {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Color {
                    key: sample::<ProvenanceKey>(),
                    value: sample::<String>(),
                },
                Self::Colors {
                    key: sample::<ProvenanceKey>(),
                    values: sample::<Vec<DescriptorColorEntry>>(),
                },
                Self::Prefer {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Overload {
                    target: sample::<WireApplicationReference>(),
                },
                Self::Memo {
                    key: sample::<ProvenanceKey>(),
                },
                Self::ListCons {
                    key: sample::<ProvenanceKey>(),
                    separator_key: sample::<ProvenanceKey>(),
                    separator: sample::<String>(),
                    non_empty: sample::<Option<ProvenanceKey>>(),
                    terminator: sample::<WireApplicationReference>(),
                },
                Self::ListTerminator {
                    cons: sample::<WireApplicationReference>(),
                },
                Self::RawHook {
                    key: sample::<ProvenanceKey>(),
                    namespace: sample::<String>(),
                    name: sample::<String>(),
                },
                Self::FreshGenerator {
                    key: sample::<ProvenanceKey>(),
                },
                Self::Smtlib {
                    key: sample::<ProvenanceKey>(),
                    symbol: sample::<String>(),
                },
                Self::SmtHook {
                    key: sample::<ProvenanceKey>(),
                    template: sample::<Vec<DescriptorSmtFragment>>(),
                },
                Self::Desugar {
                    key: sample::<ProvenanceKey>(),
                    recursive: sample::<Option<ProvenanceKey>>(),
                },
            ],
            25,
            "WireProductionAttribute",
            |value| match value {
                Self::Documentation { .. } => 0,
                Self::Function { .. } => 1,
                Self::Total { .. } => 2,
                Self::Hook { .. } => 3,
                Self::Alias { .. } => 4,
                Self::Token { .. } => 5,
                Self::Group { .. } => 6,
                Self::Bracket { .. } => 7,
                Self::Avoid { .. } => 8,
                Self::Format { .. } => 9,
                Self::Strictness { .. } => 10,
                Self::Internal { .. } => 11,
                Self::Program { .. } => 12,
                Self::Color { .. } => 13,
                Self::Colors { .. } => 14,
                Self::Prefer { .. } => 15,
                Self::Overload { .. } => 16,
                Self::Memo { .. } => 17,
                Self::ListCons { .. } => 18,
                Self::ListTerminator { .. } => 19,
                Self::RawHook { .. } => 20,
                Self::FreshGenerator { .. } => 21,
                Self::Smtlib { .. } => 22,
                Self::SmtHook { .. } => 23,
                Self::Desugar { .. } => 24,
            },
        )
    }
}
impl Sample for WireProductionItem {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Terminal {
                    key: sample::<ProvenanceKey>(),
                    text: sample::<String>(),
                },
                Self::NonTerminal {
                    key: sample::<ProvenanceKey>(),
                    field_key: sample::<ProvenanceKey>(),
                    declaration_key: sample::<Option<ProvenanceKey>>(),
                    field: sample::<ProductionFieldId>(),
                    sort: sample::<Box<WireSortReference>>(),
                },
                Self::RegexTerminal {
                    key: sample::<ProvenanceKey>(),
                    precede_regex: sample::<Option<String>>(),
                    regex: sample::<String>(),
                    follow_regex: sample::<Option<String>>(),
                },
            ],
            3,
            "WireProductionItem",
            |value| match value {
                Self::Terminal { .. } => 0,
                Self::NonTerminal { .. } => 1,
                Self::RegexTerminal { .. } => 2,
            },
        )
    }
}
impl Sample for WireProductionOwner {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Constructor {
                    constructor: sample::<WireApplicationReference>(),
                },
                Self::TokenSort {
                    sort: sample::<WireSortReference>(),
                },
                Self::BracketSort {
                    sort: sample::<WireSortReference>(),
                },
            ],
            3,
            "WireProductionOwner",
            |value| match value {
                Self::Constructor { .. } => 0,
                Self::TokenSort { .. } => 1,
                Self::BracketSort { .. } => 2,
            },
        )
    }
}
impl Sample for WireTerm {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Variable {
                    key: sample::<ProvenanceKey>(),
                    path_key: sample::<ProvenanceKey>(),
                    name: sample::<String>(),
                },
                Self::Application {
                    head_class: sample::<DescriptorApplicationHeadClass>(),
                    reference: sample::<WireApplicationReference>(),
                    path_key: sample::<ProvenanceKey>(),
                    arguments: sample::<Vec<WireTermArgument>>().try_into().unwrap(),
                },
                Self::Literal {
                    key: sample::<ProvenanceKey>(),
                    literal: sample::<DescriptorLiteral>(),
                },
                Self::Wildcard {
                    key: sample::<ProvenanceKey>(),
                },
                Self::BuiltinToken {
                    key: sample::<ProvenanceKey>(),
                    sort: sample::<BuiltinSort>(),
                    value: sample::<String>(),
                },
                Self::Anonymous {
                    key: sample::<ProvenanceKey>(),
                    sort: sample::<WireSortReference>(),
                    spelling: sample::<String>(),
                },
                Self::OrBool {
                    key: sample::<ProvenanceKey>(),
                    arguments: AtLeastTwo::new(
                        sample::<WireTerm>(),
                        sample::<WireTerm>(),
                        Vec::new(),
                    ),
                },
                Self::Cell {
                    key: sample::<ProvenanceKey>(),
                    declaration: sample::<WireTypeReference>(),
                    fields: sample::<Vec<WireCellTermField>>(),
                },
                Self::Lexeme {
                    key: sample::<ProvenanceKey>(),
                    sort: sample::<WireSortReference>(),
                    text: sample::<String>(),
                },
                Self::SortTest {
                    key: sample::<ProvenanceKey>(),
                    kind: SortTestKind::Predicate,
                    sort: sample::<WireSortReference>(),
                    operand: Box::new(sample::<WireTerm>()),
                },
                Self::SortTest {
                    key: sample::<ProvenanceKey>(),
                    kind: SortTestKind::Projection,
                    sort: sample::<WireSortReference>(),
                    operand: Box::new(sample::<WireTerm>()),
                },
                Self::As {
                    key: sample::<ProvenanceKey>(),
                    binding_key: sample::<ProvenanceKey>(),
                    name: sample::<String>(),
                    pattern: Box::new(sample::<WireTerm>()),
                },
                Self::Or {
                    key: sample::<ProvenanceKey>(),
                    alternatives: AtLeastTwo::new(
                        sample::<WireTerm>(),
                        sample::<WireTerm>(),
                        Vec::new(),
                    ),
                },
            ],
            12,
            "WireTerm",
            |value| match value {
                Self::Variable { .. } => 0,
                Self::Application { .. } => 1,
                Self::Literal { .. } => 2,
                Self::Wildcard { .. } => 3,
                Self::BuiltinToken { .. } => 4,
                Self::Anonymous { .. } => 5,
                Self::OrBool { .. } => 6,
                Self::Cell { .. } => 7,
                Self::Lexeme { .. } => 8,
                Self::SortTest { .. } => 9,
                Self::As { .. } => 10,
                Self::Or { .. } => 11,
            },
        )
    }
    // Recursive WireTerm variants need a terminal first sample.
    fn first() -> Self {
        Self::Variable {
            key: sample::<ProvenanceKey>(),
            path_key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
        }
    }
}
impl Sample for WireTermArgument {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Positional {
                    value: sample::<Box<WireTerm>>(),
                },
                Self::Named {
                    key: sample::<ProvenanceKey>(),
                    field: sample::<ProductionFieldId>(),
                    value: sample::<Box<WireTerm>>(),
                },
            ],
            2,
            "WireTermArgument",
            |value| match value {
                Self::Positional { .. } => 0,
                Self::Named { .. } => 1,
            },
        )
    }
}
impl Sample for Descriptor {
    fn samples() -> Vec<Self> {
        vec![krs_ir::testing::descriptor(
            sample::<StableItemId>(),
            sample::<BTreeMap<String, Option<String>>>(),
            sample::<DescriptorProvenance>(),
            sample::<DescriptorPayload>(),
        )]
    }
}
impl Sample for DefinitionRuleBody {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Term(sample::<IrRewrite<DefinitionLevel>>()),
                Self::Configuration(
                    sample::<FixedConfigurationRewrite<SymbolId, DefinitionTerm>>(),
                ),
            ],
            2,
            "DefinitionRuleBody",
            |value| match value {
                Self::Term(..) => 0,
                Self::Configuration(..) => 1,
            },
        )
    }
}
impl Sample for SemanticRuleBody {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Term(sample::<IrRewrite<SemanticLevel>>()),
                Self::Configuration(
                    sample::<FixedConfigurationRewrite<SemanticId, SemanticTerm>>(),
                ),
            ],
            2,
            "SemanticRuleBody",
            |value| match value {
                Self::Term(..) => 0,
                Self::Configuration(..) => 1,
            },
        )
    }
}
impl Sample for ConstructorDescriptor {
    fn samples() -> Vec<Self> {
        vec![Self {
            sort: sample::<DescriptorSortRef>(),
            fields: sample::<Vec<ConstructorFieldDescriptor>>(),
        }]
    }
}
impl Sample for ConstructorFieldDescriptor {
    fn samples() -> Vec<Self> {
        vec![Self {
            name: sample::<String>(),
            sort: sample::<Option<crate::DescriptorSortRef>>(),
        }]
    }
}
impl Sample for ContextAliasSentence {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<StableItemId>(),
            sample::<NodeOrigin>(),
            sample::<String>(),
            sample::<NodeOrigin>(),
            sample::<SemanticId>(),
            sample::<Vec<DefinitionVariable>>(),
            sample::<FixedConfigurationPattern<SymbolId, DefinitionTerm>>(),
        )]
    }
}
impl Sample for DefinitionClaim {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<crate::ClaimModality>(),
            sample::<Option<NodeOrigin>>(),
            sample::<Vec<DefinitionScopedBinder>>(),
        )]
    }
}
impl Sample for DefinitionScopedBinder {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<NodeOrigin>(),
            sample::<SemanticId>(),
            sample::<NodeOrigin>(),
            sample::<DefinitionSortRef>(),
        )]
    }
}
impl Sample for DefinitionModule {
    fn samples() -> Vec<Self> {
        let cell = SymbolId::new("definition.cell").unwrap();
        let sort = DefinitionSortRef::Builtin(BuiltinSort::Int);
        let configuration = FixedConfiguration::new(
            sample_origin("definition.configuration"),
            SemanticId::new("definition.configuration").unwrap(),
            ConfigurationRoot::GeneratedTop,
            vec![
                FixedCell::leaf(
                    sample_origin("definition.cell"),
                    cell.clone(),
                    "cell",
                    vec![],
                    sort.clone(),
                )
                .unwrap(),
            ],
            sample_origin("definition.initializer"),
            SemanticId::new("definition.initializer").unwrap(),
            vec![],
            vec![FixedInitializerCell::term(
                sample_origin("definition.initializer.cell"),
                cell,
                DefinitionTerm::token(sample_origin("definition.token"), sort, "1").unwrap(),
            )],
        )
        .unwrap();
        vec![Self::new(
            sample_origin("definition.module"),
            sample::<ModuleId>(),
            vec![],
            vec![],
            vec![DefinitionSentence::Configuration(configuration)],
        )]
    }
}
impl Sample for DefinitionRuleCondition {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<DefinitionTerm>(),
        )]
    }
}
impl Sample for DefinitionVariable {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<SemanticId>(),
            sample::<DefinitionSortRef>(),
        )]
    }
}
impl Sample for DescriptorApplicationReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            application: sample::<DescriptorApplicationRef>(),
        }]
    }
}
impl Sample for DescriptorCellTermField {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            field: sample::<ProductionFieldId>(),
            value: sample::<Box<DescriptorTerm>>(),
        }]
    }
}
impl Sample for DescriptorClaim {
    fn samples() -> Vec<Self> {
        vec![Self {
            declaration_key: sample::<ProvenanceKey>(),
            modality_key: sample::<ProvenanceKey>(),
            modality: sample::<ClaimModality>(),
            circularity_key: sample::<Option<ProvenanceKey>>(),
            trusted_key: sample::<Option<ProvenanceKey>>(),
            universals: sample::<Vec<DescriptorClaimBinder>>(),
            existentials: sample::<Vec<DescriptorClaimBinder>>(),
            ensures: sample::<Option<DescriptorRuleCondition>>(),
            or_bool_keys: sample::<Vec<ProvenanceKey>>(),
        }]
    }
}
impl Sample for DescriptorClaimBinder {
    fn samples() -> Vec<Self> {
        vec![Self {
            declaration_key: sample::<ProvenanceKey>(),
            name_key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
            sort: sample::<DescriptorSortReference>(),
        }]
    }
}
impl Sample for DescriptorConfigurationRule {
    fn samples() -> Vec<Self> {
        vec![Self {
            sentence_kind: sample::<ConfigurationSentenceKind>(),
            label: sample::<Option<DescriptorRuleLabel>>(),
            priority: sample::<Option<crate::DescriptorRulePriority>>(),
            nondet: sample::<Option<DescriptorNondetGroup>>(),
            requires: sample::<Option<DescriptorRuleCondition>>(),
            claim: sample::<Option<DescriptorClaim>>(),
            pattern_key: sample::<ProvenanceKey>(),
            subject_configuration: sample::<DescriptorConfigurationReference>(),
            result_key: sample::<ProvenanceKey>(),
            result_configuration: sample::<DescriptorConfigurationReference>(),
            bindings: sample::<Vec<DescriptorRuleBinding>>(),
            subject: sample::<DescriptorRuleCells>(),
            result: sample::<DescriptorRuleCells>(),
            existentials: sample(),
            ensures: sample(),
            fresh: sample(),
        }]
    }
}
impl Sample for DescriptorContextAlias {
    fn samples() -> Vec<Self> {
        vec![Self {
            declaration_key: sample::<ProvenanceKey>(),
            name_key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
            here_key: sample::<ProvenanceKey>(),
            here: sample::<String>(),
            pattern_key: sample::<ProvenanceKey>(),
            configuration: sample::<DescriptorConfigurationReference>(),
            bindings: sample::<Vec<ProtocolContextAliasBinding<DescriptorSortReference>>>(),
            pattern: sample::<DescriptorRuleCells>(),
        }]
    }
}
impl Sample for DescriptorFixedConfiguration {
    fn samples() -> Vec<Self> {
        vec![Self {
            root: sample::<DescriptorConfigurationRoot>(),
            declaration: sample::<DescriptorConfigurationDeclaration>(),
            initializer: sample::<DescriptorConfigurationInitializer>(),
        }]
    }
}
impl Sample for DescriptorFormatFragment {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            fragment: sample::<FormatFragment>(),
        }]
    }
}
impl Sample for DescriptorSmtFragment {
    fn samples() -> Vec<Self> {
        vec![
            Self {
                key: None,
                fragment: SmtFragment::Text(sample::<String>()),
            },
            Self {
                key: Some(sample::<ProvenanceKey>()),
                fragment: SmtFragment::Field(sample::<ProductionFieldId>()),
            },
        ]
    }
}
impl Sample for SmtFragment {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Text(sample::<String>()),
                Self::Field(sample::<ProductionFieldId>()),
            ],
            2,
            "SmtFragment",
            |value| match value {
                Self::Text(..) => 0,
                Self::Field(..) => 1,
            },
        )
    }
}
impl Sample for DescriptorHeadRule {
    fn samples() -> Vec<Self> {
        vec![Self {
            sentence_kind: sample::<SentenceKind>(),
            label: sample::<Option<DescriptorRuleLabel>>(),
            priority: sample::<Option<DescriptorRulePriority>>(),
            nondet: sample::<Option<DescriptorNondetGroup>>(),
            pattern_key: sample::<ProvenanceKey>(),
            result_key: sample::<ProvenanceKey>(),
            head_sort: sample::<Option<DescriptorSortReference>>(),
            configuration: sample::<StableItemId>(),
            computation_cell: sample::<Option<DescriptorCellReference>>(),
            bindings: sample::<Vec<DescriptorHeadRuleBinding>>(),
            head: sample::<Option<ProtocolHeadRuleHead<DescriptorTerm>>>(),
            requires: sample::<Option<DescriptorRuleCondition>>(),
            extras: sample::<Vec<DescriptorHeadRuleExtra>>(),
            existentials: sample(),
            ensures: sample(),
            fresh: sample(),
        }]
    }
}
impl Sample for DescriptorNodeOrigin {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            origin: sample::<OriginStack>(),
        }]
    }
}
impl Sample for DescriptorProduction {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            template_key: sample::<Option<ProvenanceKey>>(),
            owner: sample::<DescriptorProductionOwner>(),
            result_sort: sample::<DescriptorSortReference>(),
            items: sample::<Vec<DescriptorProductionItem>>(),
            attributes: sample::<Vec<DescriptorProductionAttribute>>(),
        }]
    }
}
impl Sample for DescriptorRuleCondition {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            term: sample::<DescriptorTerm>(),
        }]
    }
}
impl Sample for DescriptorSortReference {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            sort: sample::<DescriptorSortRef>(),
        }]
    }
}
impl<
    C: Sample + Clone + Serialize + DeserializeOwned,
    T: Sample + Clone + Serialize + DeserializeOwned,
> Sample for FixedCellClause<C, T>
{
    fn samples() -> Vec<Self> {
        vec![
            Self::new(
                sample::<NodeOrigin>(),
                sample::<C>(),
                sample::<T>(),
                sample::<CellPost<T>>(),
                sample::<CellContentFrame>(),
            ),
            Self::whole(
                sample::<NodeOrigin>(),
                sample::<C>(),
                sample::<T>(),
                sample::<CellPost<T>>(),
            ),
        ]
    }
}
impl<
    C: Sample + Clone + Serialize + DeserializeOwned,
    T: Sample + Clone + Serialize + DeserializeOwned,
> Sample for FixedCellPattern<C, T>
{
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<C>(),
            sample::<T>(),
            sample::<CellContentFrame>(),
        )]
    }
}
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample for FixedConfigurationVariable<S> {
    fn samples() -> Vec<Self> {
        vec![
            Self::new(
                sample::<NodeOrigin>(),
                sample::<SemanticId>(),
                sample::<String>(),
                sample::<S>(),
                sample::<bool>(),
            )
            .unwrap(),
        ]
    }
}
impl Sample for GroupAssociativitySentence {
    fn samples() -> Vec<Self> {
        vec![
            Self::new(
                sample::<NodeOrigin>(),
                sample::<GroupAssociativity>(),
                sample::<Vec<ProductionGroupId>>(),
            )
            .unwrap(),
        ]
    }
}
impl Sample for LexicalSentence {
    fn samples() -> Vec<Self> {
        vec![Self::new(sample::<NodeOrigin>(), "Alpha", "[a-zA-Z]").unwrap()]
    }
}
impl Sample for LayoutSentence {
    fn samples() -> Vec<Self> {
        vec![Self::new(sample::<NodeOrigin>(), "[\\ \\n]").unwrap()]
    }
}
impl Sample for PrecedenceRelation {
    fn samples() -> Vec<Self> {
        vec![
            Self::new(
                sample::<NodeOrigin>(),
                sample::<Vec<ProductionGroupId>>(),
                sample::<Vec<ProductionGroupId>>(),
            )
            .unwrap(),
        ]
    }
}
impl Sample for ProductionContextAliasReference {
    fn samples() -> Vec<Self> {
        vec![Self::new(sample::<NodeOrigin>(), sample::<StableItemId>())]
    }
}
impl Sample for ProductionFieldReference {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<ProductionFieldId>(),
        )]
    }
}
impl Sample for ProductionGroupIdentity {
    fn samples() -> Vec<Self> {
        vec![
            Self::new(
                sample::<NodeOrigin>(),
                sample::<ProductionGroupId>(),
                sample::<String>(),
            )
            .unwrap(),
        ]
    }
}
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample for ProductionResultSort<S> {
    fn samples() -> Vec<Self> {
        vec![Self::new(sample::<NodeOrigin>(), sample::<S>())]
    }
}
impl<
    I: Sample + Clone + Serialize + DeserializeOwned,
    S: Sample + Clone + Serialize + DeserializeOwned,
    N: Sample + Clone + Serialize + DeserializeOwned,
> Sample for ProtocolCellField<I, S, N>
{
    fn samples() -> Vec<Self> {
        vec![Self {
            reference: sample::<I>(),
            rust_field: sample::<String>(),
            emitted_name: sample::<Option<DescriptorCellName>>(),
            color: sample::<Option<DescriptorCellColor>>(),
            multiplicity: sample::<Option<DescriptorCellMultiplicity>>(),
            cell_type: sample::<Option<DescriptorCellType>>(),
            stream: sample::<Option<DescriptorCellStream>>(),
            exit: sample::<Option<DescriptorCellExit>>(),
            content: sample::<ProtocolCellContent<S, N>>(),
        }]
    }
}
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolContextAliasBinding<S> {
    fn samples() -> Vec<Self> {
        vec![Self {
            name: sample::<String>(),
            kind: sample::<ProtocolContextAliasBindingKind<S>>(),
        }]
    }
}
impl<
    I: Sample + Clone + Serialize + DeserializeOwned,
    N: Sample + Clone + Serialize + DeserializeOwned,
    T: Sample + Clone + Serialize + DeserializeOwned,
> Sample for ProtocolInitializerCell<I, N, T>
{
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            field: sample::<I>(),
            content: sample::<ProtocolInitializerCellContent<I, N, T>>(),
        }]
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolMap<T> {
    fn samples() -> Vec<Self> {
        vec![Self {
            payload_key: sample::<Option<ProvenanceKey>>(),
            body: sample::<ProtocolMapBody<T>>(),
        }]
    }
}
impl<S: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolRuleBinding<S> {
    fn samples() -> Vec<Self> {
        vec![Self {
            name: sample::<String>(),
            kind: sample::<ProtocolRuleBindingKind<S>>(),
        }]
    }
}
impl<
    I: Sample + Clone + Serialize + DeserializeOwned,
    T: Sample + Clone + Serialize + DeserializeOwned,
> Sample for ProtocolRuleCell<I, T>
{
    fn samples() -> Vec<Self> {
        vec![
            Self {
                field: sample::<I>(),
                wrapper_key: Some(sample::<ProvenanceKey>()),
                wrapper: Some(sample::<CellWrapper>()),
                value: sample::<ProtocolRuleStateTerm<T>>(),
            },
            Self {
                field: sample::<I>(),
                wrapper_key: None,
                wrapper: None,
                value: ProtocolRuleStateTerm::Group(sample::<T>()),
            },
        ]
    }
}
impl<
    I: Sample + Clone + Serialize + DeserializeOwned,
    T: Sample + Clone + Serialize + DeserializeOwned,
> Sample for ProtocolRuleCells<I, T>
{
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            cells: sample::<Vec<ProtocolRuleCell<I, T>>>(),
            remainder: sample::<ProtocolRuleFrame>(),
        }]
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolRuleKSequence<T> {
    fn samples() -> Vec<Self> {
        vec![Self {
            payload_key: sample::<Option<ProvenanceKey>>(),
            dot_k_key: sample::<Option<ProvenanceKey>>(),
            notation: sample::<DescriptorKSequenceNotation>(),
            items: sample::<Vec<ProtocolRuleKSequenceItem<T>>>(),
            tail: sample::<ProtocolRuleFrame>(),
        }]
    }
}
impl<T: Sample + Clone + Serialize + DeserializeOwned> Sample for ProtocolRuleMap<T> {
    fn samples() -> Vec<Self> {
        vec![Self {
            payload_key: sample::<Option<ProvenanceKey>>(),
            body: sample::<ProtocolRuleMapBody<T>>(),
        }]
    }
}
impl Sample for SemanticClaim {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<crate::ClaimModality>(),
            sample::<Option<NodeOrigin>>(),
            sample::<Vec<SemanticScopedBinder>>(),
        )]
    }
}
impl Sample for SemanticScopedBinder {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<NodeOrigin>(),
            sample::<SemanticId>(),
            sample::<NodeOrigin>(),
            sample::<SemanticSortRef>(),
        )]
    }
}
impl Sample for SemanticContextAlias {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<StableItemId>(),
            sample::<NodeOrigin>(),
            sample::<String>(),
            sample::<NodeOrigin>(),
            sample::<SemanticId>(),
            sample::<Vec<SemanticVariable>>(),
            sample::<FixedConfigurationPattern<SemanticId, SemanticTerm>>(),
        )]
    }
}
impl Sample for SemanticRuleCondition {
    fn samples() -> Vec<Self> {
        vec![Self::new(sample::<NodeOrigin>(), sample::<SemanticTerm>())]
    }
}
impl Sample for SemanticRuleLabel {
    fn samples() -> Vec<Self> {
        vec![Self::new(sample::<NodeOrigin>(), sample::<String>()).unwrap()]
    }
}
impl Sample for IrRulePriority {
    fn samples() -> Vec<Self> {
        vec![Self::new(sample::<NodeOrigin>(), sample::<u32>())]
    }
}
impl Sample for IrSimplification {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<Option<IrSimplificationPriority>>(),
        )]
    }
}
impl Sample for IrSimplificationPriority {
    fn samples() -> Vec<Self> {
        vec![Self::new(sample::<NodeOrigin>(), sample::<u32>())]
    }
}
impl Sample for SemanticSubsort {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<SemanticSortRef>(),
            sample::<SemanticSortRef>(),
        )]
    }
}
impl Sample for SemanticVariable {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<SemanticId>(),
            sample::<SemanticSortRef>(),
        )]
    }
}
impl Sample for StructuredRuleDescriptor {
    fn samples() -> Vec<Self> {
        vec![Self {
            sentence_kind: sample::<SentenceKind>(),
            label: sample::<Option<DescriptorRuleLabel>>(),
            requires: sample::<Option<DescriptorRuleCondition>>(),
            priority: sample::<Option<DescriptorRulePriority>>(),
            nondet: sample::<Option<DescriptorNondetGroup>>(),
            anywhere: sample::<Option<ProvenanceKey>>(),
            simplification: sample::<Option<DescriptorSimplification>>(),
            pattern_key: sample::<ProvenanceKey>(),
            typed_bindings: sample::<Vec<DescriptorTypedBinding>>(),
            result_key: sample::<ProvenanceKey>(),
            subject_sort: sample::<DescriptorSortReference>(),
            result_sort: sample::<DescriptorSortReference>(),
            bindings: sample::<Vec<String>>(),
            subject: sample::<DescriptorTerm>(),
            result: sample::<DescriptorTerm>(),
            existentials: sample(),
            ensures: sample(),
            fresh: sample(),
            equation: sample::<Option<DescriptorEquationAttributes>>(),
            unbound_variables: sample::<Option<DescriptorUnboundVariables>>(),
        }]
    }
}
impl Sample for SubsortSentence {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<NodeOrigin>(),
            sample::<DefinitionSortRef>(),
            sample::<DefinitionSortRef>(),
        )]
    }
}
impl Sample for SyntaxSortSentence {
    fn samples() -> Vec<Self> {
        vec![Self::new(sample::<NodeOrigin>(), sample::<SymbolIdentity>()).unwrap()]
    }
}
impl Sample for WireCellTermField {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            field: sample::<ProductionFieldId>(),
            value: sample::<Box<WireTerm>>(),
        }]
    }
}
impl Sample for WireHeadRule {
    fn samples() -> Vec<Self> {
        vec![Self {
            sentence_kind: sample::<SentenceKind>(),
            label: sample::<Option<DescriptorRuleLabel>>(),
            priority: sample::<Option<DescriptorRulePriority>>(),
            nondet: sample::<Option<DescriptorNondetGroup>>(),
            pattern_key: sample::<ProvenanceKey>(),
            result_key: sample::<ProvenanceKey>(),
            head_sort: sample::<Option<WireSortReference>>(),
            configuration: sample::<Option<WireConfigurationReference>>(),
            computation_cell_name: sample::<Option<String>>(),
            bindings: sample::<Vec<WireHeadRuleBinding>>(),
            head: sample::<Option<WireHeadRuleHead>>(),
            requires: sample::<Option<WireRuleCondition>>(),
            extras: sample::<Vec<WireHeadRuleExtra>>(),
            existentials: sample(),
            ensures: sample(),
            fresh: sample(),
        }]
    }
}
impl Sample for WirePayload {
    fn samples() -> Vec<Self> {
        checked_samples(
            vec![
                Self::Constructor(sample::<WireConstructorDescriptor>()),
                Self::Grammar(sample::<Box<WireGrammarDescriptor>>()),
                Self::StructuredRule(sample::<Box<WireStructuredRule>>()),
                Self::HeadRule(sample::<Box<WireHeadRule>>()),
                Self::Sort(sample::<WireSortDescriptor>()),
                Self::FixedConfiguration(sample::<Box<WireFixedConfiguration>>()),
                Self::Cell(sample::<Box<WireCellDeclaration>>()),
                Self::ConfigurationRule(sample::<Box<WireConfigurationRule>>()),
                Self::ContextAlias(sample::<Box<WireContextAlias>>()),
            ],
            9,
            "WirePayload",
            |value| match value {
                Self::Constructor(..) => 0,
                Self::Grammar(..) => 1,
                Self::StructuredRule(..) => 2,
                Self::HeadRule(..) => 3,
                Self::Sort(..) => 4,
                Self::FixedConfiguration(..) => 5,
                Self::Cell(..) => 6,
                Self::ConfigurationRule(..) => 7,
                Self::ContextAlias(..) => 8,
            },
        )
    }
}
impl Sample for WireFixedConfiguration {
    fn samples() -> Vec<Self> {
        vec![Self {
            root: sample::<DescriptorConfigurationRoot>(),
            declaration: sample::<WireConfigurationDeclaration>(),
            initializer: sample::<WireConfigurationInitializer>(),
        }]
    }
}
impl Sample for WireClaim {
    fn samples() -> Vec<Self> {
        vec![Self {
            declaration_key: sample::<ProvenanceKey>(),
            modality_key: sample::<ProvenanceKey>(),
            modality: sample::<ClaimModality>(),
            circularity_key: sample::<Option<ProvenanceKey>>(),
            trusted_key: sample::<Option<ProvenanceKey>>(),
            universals: sample::<Vec<WireClaimBinder>>(),
            existentials: sample::<Vec<WireClaimBinder>>(),
            ensures: sample::<Option<WireRuleCondition>>(),
            or_bool_keys: sample::<Vec<ProvenanceKey>>(),
        }]
    }
}
impl Sample for WireClaimBinder {
    fn samples() -> Vec<Self> {
        vec![Self {
            declaration_key: sample::<ProvenanceKey>(),
            name_key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
            sort: sample::<WireSortReference>(),
        }]
    }
}
impl Sample for WireConfigurationRule {
    fn samples() -> Vec<Self> {
        vec![Self {
            sentence_kind: sample::<ConfigurationSentenceKind>(),
            label: sample::<Option<DescriptorRuleLabel>>(),
            priority: sample::<Option<DescriptorRulePriority>>(),
            nondet: sample::<Option<DescriptorNondetGroup>>(),
            requires: sample::<Option<WireRuleCondition>>(),
            claim: sample::<Option<WireClaim>>(),
            pattern_key: sample::<ProvenanceKey>(),
            subject_configuration: sample::<WireConfigurationReference>(),
            result_key: sample::<ProvenanceKey>(),
            result_configuration: sample::<WireConfigurationReference>(),
            bindings: sample::<Vec<ProtocolRuleBinding<WireSortReference>>>(),
            subject: sample::<WireRuleCells>(),
            result: sample::<WireRuleCells>(),
            existentials: sample(),
            ensures: sample(),
            fresh: sample(),
        }]
    }
}
impl Sample for WireContextAlias {
    fn samples() -> Vec<Self> {
        vec![Self {
            declaration_key: sample::<ProvenanceKey>(),
            name_key: sample::<ProvenanceKey>(),
            name: sample::<String>(),
            here_key: sample::<ProvenanceKey>(),
            here: sample::<String>(),
            pattern_key: sample::<ProvenanceKey>(),
            configuration: sample::<WireConfigurationReference>(),
            bindings: sample::<Vec<ProtocolContextAliasBinding<WireSortReference>>>(),
            pattern: sample::<WireRuleCells>(),
        }]
    }
}
impl Sample for WireProduction {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            template_key: sample::<Option<ProvenanceKey>>(),
            owner: sample::<WireProductionOwner>(),
            result_sort: sample::<WireSortReference>(),
            items: sample::<Vec<WireProductionItem>>(),
            attributes: sample::<Vec<WireProductionAttribute>>(),
        }]
    }
}
impl Sample for WireRuleCondition {
    fn samples() -> Vec<Self> {
        vec![Self {
            key: sample::<ProvenanceKey>(),
            term: sample::<WireTerm>(),
        }]
    }
}
impl Sample for WireStructuredRule {
    fn samples() -> Vec<Self> {
        vec![Self {
            sentence_kind: sample::<SentenceKind>(),
            label: sample::<Option<DescriptorRuleLabel>>(),
            requires: sample::<Option<WireRuleCondition>>(),
            priority: sample::<Option<DescriptorRulePriority>>(),
            nondet: sample::<Option<DescriptorNondetGroup>>(),
            anywhere: sample::<Option<ProvenanceKey>>(),
            simplification: sample::<Option<DescriptorSimplification>>(),
            pattern_key: sample::<ProvenanceKey>(),
            typed_bindings: sample::<Vec<WireTypedBinding>>(),
            result_key: sample::<ProvenanceKey>(),
            subject_sort: sample::<WireSortReference>(),
            result_sort: sample::<WireSortReference>(),
            bindings: sample::<Vec<String>>(),
            subject: sample::<WireTerm>(),
            result: sample::<WireTerm>(),
            existentials: sample(),
            ensures: sample(),
            fresh: sample(),
            equation: sample::<Option<DescriptorEquationAttributes>>(),
            unbound_variables: sample::<Option<DescriptorUnboundVariables>>(),
        }]
    }
}

mod manual;

fn insert<T: Sample + Serialize + DeserializeOwned>(
    corpus: &mut BTreeMap<&'static str, Vec<serde_json::Value>>,
    name: &'static str,
) {
    let values: Vec<_> = T::samples()
        .iter()
        .map(|sample| {
            let json = serde_json::to_value(sample).unwrap();
            let decoded: T = serde_json::from_value(json.clone()).unwrap();
            assert_eq!(
                serde_json::to_value(decoded).unwrap(),
                json,
                "{name} round trip"
            );
            json
        })
        .collect();
    assert!(!values.is_empty());
    assert!(corpus.insert(name, values).is_none());
}

fn insert_tagged(corpus: &mut BTreeMap<&'static str, Vec<serde_json::Value>>) {
    insert::<ApplicationRef<StableItemId, SemanticSortRef>>(corpus, "ApplicationRef");
    insert::<CellAttribute>(corpus, "CellAttribute");
    insert::<CellContentFrame>(corpus, "CellContentFrame");
    insert::<CellPost<SemanticTerm>>(corpus, "CellPost");
    insert::<ConfigurationRoot>(corpus, "ConfigurationRoot");
    insert::<DefinitionSentence>(corpus, "DefinitionSentence");
    insert::<DefinitionSortRef>(corpus, "DefinitionSortRef");
    insert::<DefinitionTermKind>(corpus, "DefinitionTermKind");
    insert::<DescriptorApplicationRef>(corpus, "DescriptorApplicationRef");
    insert::<DescriptorConfigurationRoot>(corpus, "DescriptorConfigurationRoot");
    insert::<DescriptorLiteral>(corpus, "DescriptorLiteral");
    insert::<DescriptorPayload>(corpus, "DescriptorPayload");
    insert::<DescriptorProductionAttribute>(corpus, "DescriptorProductionAttribute");
    insert::<DescriptorProductionItem>(corpus, "DescriptorProductionItem");
    insert::<DescriptorProductionOwner>(corpus, "DescriptorProductionOwner");
    insert::<DescriptorSortRef>(corpus, "DescriptorSortRef");
    insert::<DescriptorTerm>(corpus, "DescriptorTerm");
    insert::<DescriptorTermArgument>(corpus, "DescriptorTermArgument");
    insert::<FixedCellContent<SemanticSortRef, SemanticId>>(corpus, "FixedCellContent");
    insert::<FixedInitializerContent<SemanticId, SemanticTerm>>(corpus, "FixedInitializerContent");
    insert::<FormatFragment>(corpus, "FormatFragment");
    insert::<SmtFragment>(corpus, "SmtFragment");
    insert::<GrammarDescriptor>(corpus, "GrammarDescriptor");
    insert::<GrammarProductionItemKind<SemanticSortRef>>(corpus, "GrammarProductionItemKind");
    insert::<OriginFrame>(corpus, "OriginFrame");
    insert::<ProductionAttribute<SemanticSortRef, StableItemId>>(corpus, "ProductionAttribute");
    insert::<ProtocolCellContent<DescriptorSortReference, DescriptorCellDeclarationReference>>(
        corpus,
        "ProtocolCellContent",
    );
    insert::<ProtocolContextAliasBindingKind<DescriptorSortReference>>(
        corpus,
        "ProtocolContextAliasBindingKind",
    );
    insert::<ProtocolHeadRuleExtra<DescriptorCellReference, DescriptorTerm>>(
        corpus,
        "ProtocolHeadRuleExtra",
    );
    insert::<ProtocolHeadRuleResult<DescriptorTerm>>(corpus, "ProtocolHeadRuleResult");
    insert::<ProtocolHeadRuleHead<DescriptorTerm>>(corpus, "ProtocolHeadRuleHead");
    insert::<
        ProtocolInitializerCellContent<
            DescriptorCellReference,
            DescriptorCellDeclarationReference,
            DescriptorInitializerStateTerm,
        >,
    >(corpus, "ProtocolInitializerCellContent");
    insert::<ProtocolInitializerStateTerm<DescriptorTerm>>(corpus, "ProtocolInitializerStateTerm");
    insert::<ProtocolMapBody<DescriptorTerm>>(corpus, "ProtocolMapBody");
    insert::<ProtocolRuleBindingKind<DescriptorSortReference>>(corpus, "ProtocolRuleBindingKind");
    insert::<ProtocolRuleFrame>(corpus, "ProtocolRuleFrame");
    insert::<ProtocolRuleMapBody<DescriptorTerm>>(corpus, "ProtocolRuleMapBody");
    insert::<ProtocolRuleStateTerm<DescriptorTerm>>(corpus, "ProtocolRuleStateTerm");
    insert::<RustVisibility>(corpus, "RustVisibility");
    insert::<SemanticSortRef>(corpus, "SemanticSortRef");
    insert::<SemanticTermKind>(corpus, "SemanticTermKind");
    insert::<WireGrammarDescriptor>(corpus, "WireGrammarDescriptor");
    insert::<WireProductionAttribute>(corpus, "WireProductionAttribute");
    insert::<WireProductionItem>(corpus, "WireProductionItem");
    insert::<WireProductionOwner>(corpus, "WireProductionOwner");
    insert::<WireTerm>(corpus, "WireTerm");
    insert::<WireTermArgument>(corpus, "WireTermArgument");
}

fn insert_structural(corpus: &mut BTreeMap<&'static str, Vec<serde_json::Value>>) {
    insert::<DescriptorPrecedenceChain>(corpus, "DescriptorPrecedenceChain");
    insert::<DescriptorCellType>(corpus, "DescriptorCellType");
    insert::<Arguments<DescriptorStage>>(corpus, "Arguments");
    insert::<AtLeastTwo<String>>(corpus, "AtLeastTwo");
    insert::<ConfigurationSentenceKind>(corpus, "ConfigurationSentenceKind");
    insert::<IrMatchRestriction>(corpus, "IrMatchRestriction");
    insert::<IrRestriction>(corpus, "IrRestriction");
    insert::<IrRestrictionVariable>(corpus, "IrRestrictionVariable");
    insert::<IrUnboundVariables>(corpus, "IrUnboundVariables");
    insert::<IrUnboundVariable>(corpus, "IrUnboundVariable");
    insert::<IrRewrite<SemanticLevel>>(corpus, "IrRewrite");
    insert::<TermMapOperation>(corpus, "TermMapOperation");
    insert::<DefinitionTerm>(corpus, "DefinitionTerm");
    insert::<Descriptor>(corpus, "Descriptor");
    insert::<GrammarProductionItem<SemanticSortRef>>(corpus, "GrammarProductionItem");
    insert::<SemanticTerm>(corpus, "SemanticTerm");
    insert::<DefinitionRuleBody>(corpus, "DefinitionRuleBody");
    insert::<SemanticRuleBody>(corpus, "SemanticRuleBody");
    insert::<DefinitionIr>(corpus, "DefinitionIr");
    insert::<DescriptorBundle>(corpus, "DescriptorBundle");
    insert::<DescriptorProvenance>(corpus, "DescriptorProvenance");
    insert::<OriginStack>(corpus, "OriginStack");
    insert::<SemanticTheory>(corpus, "SemanticTheory");
}

fn insert_transitive_first(corpus: &mut BTreeMap<&'static str, Vec<serde_json::Value>>) {
    insert::<ConstructorDescriptor>(corpus, "ConstructorDescriptor");
    insert::<ConstructorFieldDescriptor>(corpus, "ConstructorFieldDescriptor");
    insert::<ContextAliasSentence>(corpus, "ContextAliasSentence");
    insert::<DefinitionClaim>(corpus, "DefinitionClaim");
    insert::<DefinitionScopedBinder>(corpus, "DefinitionScopedBinder");
    insert::<DefinitionModule>(corpus, "DefinitionModule");
    insert::<DefinitionRuleCondition>(corpus, "DefinitionRuleCondition");
    insert::<DefinitionRulePriority>(corpus, "DefinitionRulePriority");
    insert::<DefinitionSimplification>(corpus, "DefinitionSimplification");
    insert::<DefinitionSimplificationPriority>(corpus, "DefinitionSimplificationPriority");
    insert::<DefinitionVariable>(corpus, "DefinitionVariable");
    insert::<DescriptorApplicationReference>(corpus, "DescriptorApplicationReference");
    insert::<DescriptorCellTermField>(corpus, "DescriptorCellTermField");
    insert::<DescriptorClaim>(corpus, "DescriptorClaim");
    insert::<DescriptorClaimBinder>(corpus, "DescriptorClaimBinder");
    insert::<DescriptorConfigurationRule>(corpus, "DescriptorConfigurationRule");
    insert::<DescriptorContextAlias>(corpus, "DescriptorContextAlias");
    insert::<DescriptorDeclaration>(corpus, "DescriptorDeclaration");
    insert::<DescriptorFixedConfiguration>(corpus, "DescriptorFixedConfiguration");
    insert::<DescriptorFormatFragment>(corpus, "DescriptorFormatFragment");
    insert::<DescriptorSmtFragment>(corpus, "DescriptorSmtFragment");
    insert::<DescriptorHeadRule>(corpus, "DescriptorHeadRule");
    insert::<DescriptorNodeOrigin>(corpus, "DescriptorNodeOrigin");
    insert::<DescriptorProduction>(corpus, "DescriptorProduction");
    insert::<DescriptorRuleCondition>(corpus, "DescriptorRuleCondition");
    insert::<DescriptorSortReference>(corpus, "DescriptorSortReference");
    insert::<FixedCell<SemanticSortRef, SemanticId>>(corpus, "FixedCell");
    insert::<FixedCellClause<SemanticId, SemanticTerm>>(corpus, "FixedCellClause");
    insert::<FixedCellPattern<SemanticId, SemanticTerm>>(corpus, "FixedCellPattern");
    insert::<FixedConfiguration<SemanticSortRef, SemanticId, SemanticTerm>>(
        corpus,
        "FixedConfiguration",
    );
    insert::<FixedConfigurationPattern<SemanticId, SemanticTerm>>(
        corpus,
        "FixedConfigurationPattern",
    );
    insert::<FixedConfigurationRewrite<SemanticId, SemanticTerm>>(
        corpus,
        "FixedConfigurationRewrite",
    );
    insert::<FixedConfigurationVariable<SemanticSortRef>>(corpus, "FixedConfigurationVariable");
    insert::<FixedInitializerCell<SemanticId, SemanticTerm>>(corpus, "FixedInitializerCell");
    insert::<GeneratedOperation<SemanticSortRef>>(corpus, "GeneratedOperation");
    insert::<GroupAssociativitySentence>(corpus, "GroupAssociativitySentence");
    insert::<LayoutSentence>(corpus, "LayoutSentence");
    insert::<LexicalSentence>(corpus, "LexicalSentence");
    insert::<NodeOrigin>(corpus, "NodeOrigin");
    insert::<PrecedenceRelation>(corpus, "PrecedenceRelation");
    insert::<RawSentence>(corpus, "RawSentence");
    insert::<ProductionContextAliasReference>(corpus, "ProductionContextAliasReference");
}

fn insert_transitive_rest(corpus: &mut BTreeMap<&'static str, Vec<serde_json::Value>>) {
    insert::<ProductionFieldReference>(corpus, "ProductionFieldReference");
    insert::<ProductionGroupIdentity>(corpus, "ProductionGroupIdentity");
    insert::<ProductionResultSort<SemanticSortRef>>(corpus, "ProductionResultSort");
    insert::<ProductionSentence>(corpus, "ProductionSentence");
    insert::<
        ProtocolCellField<
            DescriptorCellReference,
            DescriptorSortReference,
            DescriptorCellDeclarationReference,
        >,
    >(corpus, "ProtocolCellField");
    insert::<ProtocolContextAliasBinding<DescriptorSortReference>>(
        corpus,
        "ProtocolContextAliasBinding",
    );
    insert::<
        ProtocolInitializerCell<
            DescriptorCellReference,
            DescriptorCellDeclarationReference,
            DescriptorInitializerStateTerm,
        >,
    >(corpus, "ProtocolInitializerCell");
    insert::<ProtocolMap<DescriptorTerm>>(corpus, "ProtocolMap");
    insert::<ProtocolRuleBinding<DescriptorSortReference>>(corpus, "ProtocolRuleBinding");
    insert::<ProtocolRuleCell<DescriptorCellReference, DescriptorTerm>>(corpus, "ProtocolRuleCell");
    insert::<ProtocolRuleCells<DescriptorCellReference, DescriptorTerm>>(
        corpus,
        "ProtocolRuleCells",
    );
    insert::<ProtocolRuleKSequence<DescriptorTerm>>(corpus, "ProtocolRuleKSequence");
    insert::<ProtocolRuleMap<DescriptorTerm>>(corpus, "ProtocolRuleMap");
    insert::<RuleSentence>(corpus, "RuleSentence");
    insert::<SemanticClaim>(corpus, "SemanticClaim");
    insert::<SemanticScopedBinder>(corpus, "SemanticScopedBinder");
    insert::<SemanticContextAlias>(corpus, "SemanticContextAlias");
    insert::<SemanticModule>(corpus, "SemanticModule");
    insert::<SemanticProduction>(corpus, "SemanticProduction");
    insert::<SemanticRule>(corpus, "SemanticRule");
    insert::<SemanticRuleCondition>(corpus, "SemanticRuleCondition");
    insert::<SemanticRuleLabel>(corpus, "SemanticRuleLabel");
    insert::<SemanticRulePriority>(corpus, "SemanticRulePriority");
    insert::<SemanticNondetGroup>(corpus, "SemanticNondetGroup");
    insert::<SemanticSimplification>(corpus, "SemanticSimplification");
    insert::<SemanticSimplificationPriority>(corpus, "SemanticSimplificationPriority");
    insert::<SemanticSort>(corpus, "SemanticSort");
    insert::<SemanticSubsort>(corpus, "SemanticSubsort");
    insert::<SemanticVariable>(corpus, "SemanticVariable");
    insert::<StructuredRuleDescriptor>(corpus, "StructuredRuleDescriptor");
    insert::<SubsortSentence>(corpus, "SubsortSentence");
    insert::<SyntaxSortSentence>(corpus, "SyntaxSortSentence");
    insert::<WireCellTermField>(corpus, "WireCellTermField");
    insert::<WireFixedConfiguration>(corpus, "WireFixedConfiguration");
    insert::<WireClaim>(corpus, "WireClaim");
    insert::<WireConfigurationRule>(corpus, "WireConfigurationRule");
    insert::<WireContextAlias>(corpus, "WireContextAlias");
    insert::<WireHeadRule>(corpus, "WireHeadRule");
    insert::<WirePayload>(corpus, "WirePayload");
    // The original payload samples must remain byte-identical; new kinds are pinned through their wire aliases.
    // All payload samples above still undergo variant-coverage and round-trip checks.
    corpus.get_mut("WirePayload").unwrap().truncate(4);
    insert::<WireProduction>(corpus, "WireProduction");
    insert::<WireRuleCondition>(corpus, "WireRuleCondition");
    insert::<WireStructuredRule>(corpus, "WireStructuredRule");
}

pub(super) fn corpus() -> BTreeMap<&'static str, Vec<serde_json::Value>> {
    let mut corpus = BTreeMap::new();
    insert_tagged(&mut corpus);
    insert_structural(&mut corpus);
    insert_transitive_first(&mut corpus);
    insert_transitive_rest(&mut corpus);
    corpus
}

impl<L: IrLevel> Sample for IrRewrite<L>
where
    IrTerm<L>: Sample,
    L::Sort: Sample,
{
    fn samples() -> Vec<Self> {
        let from = sample::<IrTerm<L>>();
        vec![Self::new(
            from.origin().clone(),
            from.sort().clone(),
            from.clone(),
            from,
        )]
    }
}
impl Sample for ConfigurationSentenceKind {
    fn samples() -> Vec<Self> {
        vec![Self::Transition, Self::Equation, Self::Claim]
    }
}

impl Sample for Arguments<DescriptorStage> {
    fn samples() -> Vec<Self> {
        vec![sample::<Vec<DescriptorTermArgument>>().try_into().unwrap()]
    }
}
impl Sample for AtLeastTwo<String> {
    fn samples() -> Vec<Self> {
        vec![Self::new(
            sample::<String>(),
            sample::<String>(),
            Vec::new(),
        )]
    }
}
impl Sample for TermMapOperation {
    fn samples() -> Vec<Self> {
        Self::ALL.to_vec()
    }
}
