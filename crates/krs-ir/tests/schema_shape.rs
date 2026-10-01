//! Pin the serde-reflection registry for the supported KRS IR shapes.
//! The registry, unsupported samples, and collector encoding are pinned in `tests/schema`.
//! The samples file also lists every `ProvenanceRole` spelling, a closed catalog the registry
//! sees only as a string.
//! A change to a pinned schema file must advance `SchemaVersion::CURRENT` and `Krs.lock`
//! `[schemas] krs_ir`; a collector file change must advance `collector::VERSION` and its
//! `Krs.lock` entry. A released version's file must never be overwritten.
//! After advancing a version, use `UPDATE_EXPECT=1` to create the absent versioned file.
//! An existing versioned file is compared byte for byte even when recording is enabled.
//!
//! Samples of types with private fields are built through their constructors.
//! A new `#[serde(default, skip_serializing_if = ...)]` field that a constructor leaves empty
//! does not appear in the sample JSON, so such a field is not caught here;
//! its author must add a `with_*` call to the type's sample.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use krs_ir::measure::*;
use krs_ir::transport::collector;
use krs_ir::wire::*;
use krs_ir::*;
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use serde_reflection::{Error, FormatHolder, Registry, Samples, Tracer, TracerConfig};
use syn::{Item, Meta, Token, punctuated::Punctuated};

mod schema_samples;

fn recording() -> bool {
    std::env::var("UPDATE_EXPECT").as_deref() == Ok("1")
}

fn assert_versioned_pin(file: &str, bump: &str, actual: &str) {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join(file);
    let bump_message = format!(
        "advance {bump}, then record the new versioned file with UPDATE_EXPECT=1; never overwrite a released version's file"
    );
    match fs::read(&path) {
        Ok(expected) => {
            if expected != actual.as_bytes() {
                let expected = String::from_utf8_lossy(&expected);
                let hint = expected
                    .lines()
                    .zip(actual.lines())
                    .enumerate()
                    .find(|(_, (left, right))| left != right)
                    .map_or_else(
                        || {
                            format!(
                                "line count: expected {}, actual {}; first differing byte at {}",
                                expected.lines().count(),
                                actual.lines().count(),
                                expected
                                    .as_bytes()
                                    .iter()
                                    .zip(actual.as_bytes())
                                    .position(|(left, right)| left != right)
                                    .unwrap_or(expected.len().min(actual.len()))
                            )
                        },
                        |(index, (left, right))| {
                            format!("line {}: expected {left:?}, actual {right:?}", index + 1)
                        },
                    );
                panic!("{} differs ({hint}); {bump_message}", path.display());
            }
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound && recording() => {
            fs::write(&path, actual).unwrap();
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            panic!("{} is missing; {bump_message}", path.display());
        }
        Err(error) => panic!("cannot read {}: {error}", path.display()),
    }
}

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

// String-validated types need a valid default string:
// provenance roles accept only catalog spellings, and digests accept only 64 hex digits.
// Each type is traced with whichever default it accepts, and the two registries are unified.
fn config() -> TracerConfig {
    TracerConfig::default()
        .is_human_readable(true)
        .default_string_value("sort_declaration".to_owned())
}

fn digest_config() -> TracerConfig {
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
    let key = ProvenanceKey::new(ProvenanceRole::SortDeclaration, 0);
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

fn is_deserialize_path(path: &syn::Path) -> bool {
    let mut segments = path.segments.iter();
    match (segments.next(), segments.next(), segments.next()) {
        (Some(deserialize), None, None) => deserialize.ident == "Deserialize",
        (Some(serde), Some(deserialize), None) => {
            serde.ident == "serde" && deserialize.ident == "Deserialize"
        }
        _ => false,
    }
}

fn rust_sources(directory: &std::path::Path, sources: &mut Vec<syn::File>) {
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            rust_sources(&path, sources);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            sources.push(syn::parse_file(&fs::read_to_string(path).unwrap()).unwrap());
        }
    }
}

fn has_deserialize(meta: &Meta) -> bool {
    if meta.path().is_ident("derive") {
        let Meta::List(list) = meta else { return false };
        return list
            .parse_args_with(Punctuated::<syn::Path, Token![,]>::parse_terminated)
            .unwrap()
            .iter()
            .any(is_deserialize_path);
    }
    if meta.path().is_ident("cfg_attr") {
        let Meta::List(list) = meta else { return false };
        return list
            .parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
            .unwrap()
            .iter()
            .any(has_deserialize);
    }
    false
}

// Types declared inside `macro_rules!` transcribers cannot be parsed as items,
// so their tokens are scanned for derive attributes and public declarations.
fn collect_macro_tokens(
    tokens: TokenStream,
    public: &mut BTreeSet<String>,
    derived: &mut BTreeSet<String>,
) {
    let tokens: Vec<TokenTree> = tokens.into_iter().collect();
    let mut derives_deserialize = false;
    for (index, token) in tokens.iter().enumerate() {
        match token {
            TokenTree::Punct(punct) if punct.as_char() == '#' => {
                if let Some(TokenTree::Group(group)) = tokens.get(index + 1)
                    && group.delimiter() == Delimiter::Bracket
                    && let Ok(meta) = syn::parse2::<Meta>(group.stream())
                    && has_deserialize(&meta)
                {
                    derives_deserialize = true;
                }
            }
            TokenTree::Ident(keyword) if keyword == "struct" || keyword == "enum" => {
                let previous = index
                    .checked_sub(1)
                    .and_then(|previous| tokens.get(previous));
                let public_item =
                    matches!(previous, Some(TokenTree::Ident(visibility)) if visibility == "pub");
                if let Some(TokenTree::Ident(name)) = tokens.get(index + 1)
                    && public_item
                {
                    public.insert(name.to_string());
                    if derives_deserialize {
                        derived.insert(name.to_string());
                    }
                }
                derives_deserialize = false;
            }
            TokenTree::Group(group) => {
                collect_macro_tokens(group.stream(), public, derived);
            }
            _ => {}
        }
    }
}

fn collect_items(
    items: &[Item],
    public: &mut BTreeSet<String>,
    derived: &mut BTreeSet<String>,
    implemented: &mut BTreeSet<String>,
    stage_derived: &mut BTreeSet<String>,
    stage_aliases: &mut BTreeMap<String, (String, bool)>,
) {
    for item in items {
        let declaration = match item {
            Item::Struct(item) => Some((&item.vis, &item.ident, &item.attrs)),
            Item::Enum(item) => Some((&item.vis, &item.ident, &item.attrs)),
            _ => None,
        };
        if let Some((syn::Visibility::Public(_), ident, attrs)) = declaration {
            let name = ident.to_string();
            public.insert(name.clone());
            if attrs.iter().any(|attr| has_deserialize(&attr.meta)) {
                derived.insert(name);
            }
        }
        match item {
            Item::Impl(item) => {
                if let Some((_, trait_path, _)) = &item.trait_
                    && is_deserialize_path(trait_path)
                    && let syn::Type::Path(self_type) = item.self_ty.as_ref()
                    && let Some(segment) = self_type.path.segments.last()
                {
                    implemented.insert(segment.ident.to_string());
                }
            }
            Item::Mod(item) => {
                if let Some((_, nested)) = &item.content {
                    collect_items(
                        nested,
                        public,
                        derived,
                        implemented,
                        stage_derived,
                        stage_aliases,
                    );
                }
            }
            Item::Type(item) if matches!(item.vis, syn::Visibility::Public(_)) => {
                if let Some(target) = stage_alias_target(item.ty.as_ref()) {
                    stage_aliases.insert(item.ident.to_string(), target);
                }
            }
            Item::Macro(item)
                if item.mac.path.is_ident("macro_rules")
                    || item
                        .mac
                        .path
                        .segments
                        .last()
                        .is_some_and(|segment| segment.ident == "protocol_shape") =>
            {
                collect_macro_tokens(item.mac.tokens.clone(), public, derived);
            }
            Item::Macro(item)
                if item
                    .mac
                    .path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.ident == "stage_shape") =>
            {
                collect_macro_tokens(item.mac.tokens.clone(), public, stage_derived);
            }
            _ => {}
        }
    }
}

fn stage_alias_target(ty: &syn::Type) -> Option<(String, bool)> {
    let syn::Type::Path(target) = ty else {
        return None;
    };
    let segment = target.path.segments.last()?;
    let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments else {
        return None;
    };
    let Some(syn::GenericArgument::Type(syn::Type::Path(stage))) = arguments.args.first() else {
        return None;
    };
    let serializable = match stage.path.segments.last()?.ident.to_string().as_str() {
        "WireStage" | "DescriptorStage" => true,
        "HostStage" => false,
        _ => return None,
    };
    Some((segment.ident.to_string(), serializable))
}

fn deserializable_names(sources: &[syn::File]) -> BTreeSet<String> {
    let mut public = BTreeSet::new();
    let mut derived = BTreeSet::new();
    let mut implemented = BTreeSet::new();
    let mut stage_derived = BTreeSet::new();
    let mut stage_aliases = BTreeMap::new();
    for source in sources {
        collect_items(
            &source.items,
            &mut public,
            &mut derived,
            &mut implemented,
            &mut stage_derived,
            &mut stage_aliases,
        );
    }
    derived.extend(implemented.intersection(&public).cloned());
    // Stage shapes are classified through their serialized concrete aliases.
    // Host aliases carry Rust identities and must remain outside this census.
    let aliases: BTreeSet<_> = stage_aliases
        .iter()
        .filter(|(_, (target, serializable))| *serializable && stage_derived.contains(target))
        .map(|(name, _)| name.clone())
        .collect();
    for (target, _) in stage_aliases.values() {
        stage_derived.remove(target);
    }
    derived.extend(stage_derived);
    derived.extend(aliases);
    derived
}

fn census() -> BTreeSet<String> {
    let mut sources = Vec::new();
    rust_sources(
        &PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/src")),
        &mut sources,
    );
    deserializable_names(&sources)
}

#[test]
fn serde_census_preserves_concrete_stage_aliases() {
    let source = syn::parse_file(
        r"
        stage_shape! {
            #[derive(serde::Deserialize)]
            pub struct Term<S: Stage> {
                pub sort: S::Sort => [sort],
            }
        }
        pub type WireTerm = Term<WireStage>;
        pub type HostTerm = Term<HostStage>;
        pub type DescriptorTerm = Term<DescriptorStage>;
        stage_shape! {
            #[derive(Deserialize)]
            pub enum Payload<S: Stage, H => head => H2> {
                Head(value: H => [via head]),
            }
        }
        pub type DescriptorPayload = Payload<DescriptorStage, DescriptorHeadRule>;
        pub type HostDescriptorPayload = Payload<HostStage, HostHeadRule>;
        #[derive(Deserialize)]
        pub struct ProtocolTerm<T> {
            pub value: T,
        }
        protocol_shape! {
            #[derive(Deserialize)]
            pub struct ProtocolField<T> {
                pub value: T => [map],
            }
        }
        mod semantic {
            #[derive(Deserialize)]
            pub struct Term<T> {
                pub value: T,
            }
        }
        ",
    )
    .unwrap();
    assert_eq!(
        deserializable_names(&[source]),
        BTreeSet::from([
            "WireTerm".to_owned(),
            "DescriptorTerm".to_owned(),
            "DescriptorPayload".to_owned(),
            "ProtocolTerm".to_owned(),
            "ProtocolField".to_owned(),
            "Term".to_owned(),
        ])
    );
}

#[allow(clippy::too_many_lines)]
fn registry() -> Registry {
    let samples = samples();
    let mut tracer = Tracer::new(config());
    let mut digest_tracer = Tracer::new(digest_config());
    let mut classified = BTreeSet::new();
    let mut probed = BTreeSet::new();
    macro_rules! trace {
        ($name:ident : $ty:ty) => {
            let mut probe = Tracer::new(config());
            if probe.trace_type::<$ty>(&samples).is_ok() {
                tracer.trace_type::<$ty>(&samples).unwrap();
            } else {
                digest_tracer
                    .trace_type::<$ty>(&samples)
                    .unwrap_or_else(|error| {
                        panic!(
                            "{} unexpectedly failed reflection: {error:?}",
                            stringify!($name)
                        )
                    });
            }
            assert!(classified.insert(stringify!($name).to_owned()));
        };
    }
    trace!(BuiltinOperation: BuiltinOperation);
    trace!(BuiltinSort: BuiltinSort);
    trace!(SortedByKey: krs_ir::sorted::SortedByKey<ModuleId>);
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
    trace!(ProvenanceRole: ProvenanceRole);
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
    let mut registry = tracer.registry().unwrap();
    for (name, format) in digest_tracer.registry().unwrap() {
        if let Some(existing) = registry.get_mut(&name) {
            existing.unify(format).unwrap();
        } else {
            registry.insert(name, format);
        }
    }
    registry
}

#[test]
fn krs_ir_schema_shape_is_pinned() {
    let actual = format!("{}\n", serde_json::to_string_pretty(&registry()).unwrap());
    assert_versioned_pin(
        &format!("schema/krs_ir-{}.json", SchemaVersion::CURRENT.0),
        "SchemaVersion::CURRENT and Krs.lock [schemas] krs_ir",
        &actual,
    );
}

#[test]
fn unsupported_samples_are_pinned() {
    let mut corpus = schema_samples::corpus();
    let listed: BTreeSet<_> = UNTRACEABLE
        .iter()
        .flat_map(|group| group.iter().copied())
        .collect();
    assert_eq!(corpus.keys().copied().collect::<BTreeSet<_>>(), listed);
    // The registry sees `ProvenanceRole` only as a string, so its closed catalog is pinned here.
    corpus.insert(
        "ProvenanceRole",
        ProvenanceRole::ALL
            .iter()
            .map(|role| serde_json::to_value(role).unwrap())
            .collect(),
    );
    let actual = format!("{}\n", serde_json::to_string_pretty(&corpus).unwrap());
    assert_versioned_pin(
        &format!("schema/krs_ir-{}.samples.json", SchemaVersion::CURRENT.0),
        "SchemaVersion::CURRENT and Krs.lock [schemas] krs_ir",
        &actual,
    );
}

fn collector_origin(id: &StableItemId, populated: bool) -> OriginStack {
    let authored = krs_ir::testing::authored(0, 3);
    let range = match &authored.frames()[0] {
        OriginFrame::Ranged { range, .. } => range.clone(),
        OriginFrame::Transformation { .. } => unreachable!(),
    };
    let item = populated.then(|| id.clone());
    let label = populated.then(|| "collector schema sample".to_owned());
    let mut frames = vec![OriginFrame::Ranged {
        kind: RangedOriginKind::Authored,
        range: range.clone(),
        item: item.clone(),
        label: label.clone(),
    }];
    for kind in [
        RangedOriginKind::MacroInvocation,
        RangedOriginKind::GeneratedArtifact,
        RangedOriginKind::FrontendDiagnostic,
    ] {
        frames.push(OriginFrame::Ranged {
            kind,
            range: range.clone(),
            item: item.clone(),
            label: label.clone(),
        });
    }
    for kind in [
        TransformationOriginKind::GeneratedDescriptor,
        TransformationOriginKind::SemanticIr,
        TransformationOriginKind::DefinitionIr,
    ] {
        frames.push(OriginFrame::Transformation {
            kind,
            item: item.clone(),
            label: label.clone(),
        });
    }
    OriginStack::try_from_frames(frames).unwrap()
}

fn collector_descriptor(
    id: StableItemId,
    payload: DescriptorPayload,
    populated: bool,
) -> Descriptor {
    let role = match id.item_kind() {
        ItemKind::Sort => ProvenanceRole::SortDeclaration,
        ItemKind::Constructor => ProvenanceRole::ConstructorDeclaration,
        _ => unreachable!(),
    };
    let key = ProvenanceKey::new(role, 0);
    let mut origins = vec![DescriptorNodeOrigin::new(
        key.clone(),
        collector_origin(&id, populated),
    )];
    if populated {
        origins.push(DescriptorNodeOrigin::new(
            ProvenanceKey::new(ProvenanceRole::StableSymbol, 0),
            krs_ir::testing::authored(0, 3),
        ));
    }
    Descriptor {
        provenance: DescriptorProvenance::new(key, origins).unwrap(),
        id,
        cfg: BTreeMap::from([("feature".to_owned(), Some("enabled".to_owned()))]),
        payload,
    }
}

#[test]
fn collector_encoding_is_pinned() {
    let sort_id = krs_ir::testing::item("syntax", "Value", ItemKind::Sort);
    let constructor_id = krs_ir::testing::item("syntax", "Foo", ItemKind::Constructor);
    let sort = collector_descriptor(
        sort_id.clone(),
        DescriptorPayload::Sort(SortDescriptor {
            parents: BTreeSet::new(),
        }),
        true,
    );
    let constructor = collector_descriptor(
        constructor_id.clone(),
        DescriptorPayload::Constructor(ConstructorDescriptor {
            sort: DescriptorSortRef::Declared(sort_id.clone()),
            fields: vec![ConstructorFieldDescriptor {
                name: "value".to_owned(),
                sort: Some(DescriptorSortRef::Declared(sort_id)),
            }],
        }),
        false,
    );
    let bundle = DescriptorBundle::with_declarations(
        vec![sort, constructor],
        vec![
            DescriptorDeclaration::new(
                krs_ir::testing::item("syntax", "Value", ItemKind::Sort),
                RustVisibility::Public,
                Some(ExplicitSymbol::new("Schema::Value").unwrap()),
            ),
            DescriptorDeclaration::new(constructor_id, RustVisibility::Inherited, None),
        ],
    )
    .unwrap();
    let bytes = bundle.to_collector_protocol_measured().unwrap().0;
    let decoded = DescriptorBundle::from_collector_protocol(&bytes).unwrap();
    assert_eq!(decoded, bundle);
    let encoded: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    let frame_codes: BTreeSet<_> = encoded["descriptors"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|descriptor| descriptor["provenance"]["origins"].as_array().unwrap())
        .flat_map(|origin| origin["origin"].as_array().unwrap())
        .map(|frame| frame[0].as_u64().unwrap())
        .collect();
    assert_eq!(frame_codes, (0..=6).collect());

    let actual = format!("{}\n", serde_json::to_string_pretty(&encoded).unwrap());
    assert_versioned_pin(
        &format!("schema/collector-{}.json", collector::VERSION),
        "collector::VERSION and Krs.lock [schemas] collector",
        &actual,
    );
}
