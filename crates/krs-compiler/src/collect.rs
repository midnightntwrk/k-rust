use std::any::TypeId;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::{Component, Path, PathBuf};

use krs_ir::{
    AnchorPrecision, ConfigurationDescriptor, ConfigurationInitializerDescriptor,
    ConfigurationVariableDescriptor, ConstructorDescriptor, ConstructorFieldDescriptor, Descriptor,
    DescriptorApplicationRef, DescriptorApplicationReference, DescriptorBundle,
    DescriptorDeclaration, DescriptorNodeOrigin, DescriptorPayload, DescriptorProduction,
    DescriptorProductionAttribute, DescriptorProductionItem, DescriptorProductionOwner,
    DescriptorProvenance, DescriptorReference, DescriptorSortRef, DescriptorSortReference,
    DescriptorTerm, DescriptorTermArgument, GrammarDescriptor, HostApplicationIdentity,
    HostBuiltinRegistry, HostConfigurationDescriptor, HostDescriptor, HostDescriptorPayload,
    HostGrammarDescriptor, HostItemId, HostProductionAttribute, HostProductionItem,
    HostProductionOwner, HostProvenance, HostSortReference, HostSourceAnchor,
    HostStructuredRuleDescriptor, HostTerm, HostTermArgument, HostTypeReference, ItemKind,
    OriginFrame, OriginStack, PackageId, ProtocolCellContent, ProtocolInitializerCellContent,
    ProtocolInitializerStateTerm, ProtocolMapBody, ProtocolRuleFrame, ProtocolRuleMapBody,
    ProtocolRuleStateTerm, ProtocolVersion, ProvenanceKey, RangedOriginKind, RuleDescriptor,
    RuleParameterDescriptor, RustVisibility, Sha256Digest, SortDescriptor, SourceFileId,
    SourceRange, StableItemId, StructuredRuleDescriptor, TransformationOriginKind,
};
use krs_syntax::{
    ConfigurationDeclaration, ConstructorDeclaration, EnumConstructorDeclaration,
    InitializerFunction, ProvenanceAnchor, ProvenanceRole, RuleItem, SortDeclaration, SortsEntry,
    StateClaimItem, StateContextAliasItem, StateRuleItem, SubsortDeclaration, TokenDeclaration,
    TokenRange, parse_alias_attribute, parse_associativity_declaration, parse_bracket_attribute,
    parse_cells_expression_source_with_trivia, parse_cells_pattern_source_with_trivia,
    parse_claim_attribute, parse_configuration_attribute, parse_constructor_attribute,
    parse_constructors_attribute, parse_equation_attribute, parse_function_attribute,
    parse_init_attribute, parse_map_expression_source_with_trivia,
    parse_map_pattern_source_with_trivia, parse_precedence_declaration, parse_priority_attribute,
    parse_rule_attribute, parse_rule_block, parse_rule_block_source_with_trivia,
    parse_seqstrict_attribute, parse_simplification_attribute, parse_sort_attribute,
    parse_sorts_declaration, parse_strict_attribute, parse_subsort_attribute,
    parse_symbol_attribute, parse_term_expression_source, parse_token_attribute,
};
use proc_macro2::TokenStream;
use sha2::{Digest, Sha256};
use syn::visit::Visit;
use syn::{Attribute, ImplItem, Item, Meta};

use crate::{CollectionError, CollectionErrorKind};

/// Cargo-owned identity and host source location for one selected semantics package.
///
/// `manifest_path` is collection-only. It is canonicalized to match
/// `CARGO_MANIFEST_DIR` hints and is discarded before a
/// [`DescriptorBundle`] is returned. `crate_root` is the selected target name
/// as emitted by `module_path!()` (for example, `imp_semantics`).
#[derive(Clone, Debug)]
pub struct PackageContext {
    package: PackageId,
    crate_root: String,
    manifest_path: PathBuf,
}

impl PackageContext {
    /// Creates a caller-supplied package context without consulting Cargo.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid stable identity components, a non-absolute
    /// manifest path, or an invalid one-segment Rust crate-root name. Filesystem
    /// existence and symlink resolution are checked during collection.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        k_namespace: impl Into<String>,
        cargo_name: impl Into<String>,
        cargo_version: impl Into<String>,
        cargo_source: impl Into<String>,
        crate_root: impl Into<String>,
        manifest_path: impl Into<PathBuf>,
    ) -> Result<Self, CollectionError> {
        let package = PackageId::new(k_namespace, cargo_name, cargo_version, cargo_source)
            .map_err(|error| {
                CollectionError::new(
                    CollectionErrorKind::InvalidPackageContext,
                    format!("invalid stable package identity: {error}"),
                )
            })?;
        let crate_root = crate_root.into();
        if crate_root.is_empty()
            || crate_root.contains("::")
            || crate_root.contains(['/', '\\'])
            || !is_rust_identifier(&crate_root)
        {
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidPackageContext,
                format!("invalid selected Rust crate-root name `{crate_root}`"),
            ));
        }
        let manifest_path = manifest_path.into();
        if !manifest_path.is_absolute() {
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidPackageContext,
                format!(
                    "Cargo manifest path `{}` must be absolute",
                    manifest_path.display()
                ),
            ));
        }
        Ok(Self {
            package,
            crate_root,
            manifest_path,
        })
    }

    /// Returns the stable, path-free package identity.
    #[must_use]
    pub const fn package(&self) -> &PackageId {
        &self.package
    }

    /// Returns the selected target's `module_path!()` crate-root segment.
    #[must_use]
    pub fn crate_root(&self) -> &str {
        &self.crate_root
    }

    /// Returns the collection-only absolute Cargo manifest path.
    #[must_use]
    pub fn manifest_path(&self) -> &Path {
        &self.manifest_path
    }
}

#[derive(Debug)]
struct PreparedContext {
    package: PackageId,
    crate_root: String,
    package_dir: PathBuf,
}

#[derive(Debug)]
struct PendingDescriptor {
    host: HostDescriptor,
    id: StableItemId,
    context_index: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Coordinates {
    start_line: u32,
    start_column: u32,
    end_line: u32,
    end_column: u32,
}

#[derive(Clone, Debug)]
struct ParsedInvocation {
    primary: ProvenanceKey,
    item_name: String,
    anchors: BTreeMap<ProvenanceKey, Coordinates>,
    legacy_anchors: Option<BTreeMap<ProvenanceKey, Coordinates>>,
    payload: ParsedInvocationPayload,
    visibility: RustVisibility,
    explicit_symbol: Option<krs_ir::ExplicitSymbol>,
}

#[derive(Clone, Debug)]
enum ParsedInvocationPayload {
    Declaration,
    Rule {
        bindings: Vec<String>,
        references: BTreeMap<ProvenanceKey, String>,
        lhs: String,
        rhs: String,
    },
    HeadRule {
        bindings: Vec<String>,
        lhs: String,
        result_kind: String,
        extras: Vec<(String, String)>,
    },
    Configuration {
        root: String,
        cell_name: String,
    },
    Initializer {
        term: String,
        variable: Option<ParsedConfigurationVariable>,
        references: BTreeMap<ProvenanceKey, String>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedConfigurationVariable {
    binding: String,
    external_name: String,
    sort_key: ProvenanceKey,
}

#[derive(Debug)]
struct SourceDocument {
    text: String,
    file: SourceFileId,
    invocations: Vec<ParsedInvocation>,
}

/// Resolves unordered current-protocol host descriptors into one stable bundle.
///
/// This is the only API which accepts build-local `TypeId` producers or host
/// paths. It validates all inputs, reparses authored nodes with `krs-syntax`,
/// resolves references, and returns deterministically ordered, path-free data.
///
/// # Errors
///
/// Returns a typed error for invalid package selection, protocol/identity
/// disagreement, unresolved or wrongly-kinded Rust references, or source
/// provenance that cannot be reproduced exactly.
#[allow(clippy::too_many_lines)]
pub fn collect_host_descriptors(
    contexts: impl IntoIterator<Item = PackageContext>,
    descriptors: impl IntoIterator<Item = HostDescriptor>,
) -> Result<DescriptorBundle, CollectionError> {
    collect_host_descriptors_impl(contexts, descriptors, None)
}

/// Resolves host descriptors with the complete compiler-provided builtin catalog.
///
/// Unlike [`collect_host_descriptors`], this entry point admits protocol-v6
/// references to builtin sort and operation marker types. The registry is
/// validated for exact completeness before any descriptor is inspected.
///
/// # Errors
///
/// Returns a typed collection error for an invalid builtin registry or any of
/// the descriptor, identity, reference, source, and provenance failures
/// documented by [`collect_host_descriptors`].
pub fn collect_host_descriptors_with_builtins(
    contexts: impl IntoIterator<Item = PackageContext>,
    descriptors: impl IntoIterator<Item = HostDescriptor>,
    builtins: &HostBuiltinRegistry,
) -> Result<DescriptorBundle, CollectionError> {
    builtins.validate_v7().map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::InvalidBuiltinRegistry,
            format!("invalid builtin registry: {error}"),
        )
    })?;
    collect_host_descriptors_impl(contexts, descriptors, Some(builtins))
}

#[allow(clippy::too_many_lines)]
fn collect_host_descriptors_impl(
    contexts: impl IntoIterator<Item = PackageContext>,
    descriptors: impl IntoIterator<Item = HostDescriptor>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<DescriptorBundle, CollectionError> {
    let descriptors = descriptors.into_iter().collect::<Vec<_>>();
    let mut contexts = contexts.into_iter().collect::<Vec<_>>();
    if let Some(framework) = descriptors
        .iter()
        .find(|descriptor| is_framework_sort_descriptor(descriptor))
    {
        let package = framework.id.package();
        let already_selected = contexts.iter().any(|context| {
            context.package.cargo_name() == package.cargo_name()
                && context.package.cargo_version() == package.cargo_version()
                && context.manifest_path.parent() == Some(package.manifest_dir())
        });
        if !already_selected {
            contexts.push(PackageContext::new(
                "KRS-FRAMEWORK",
                package.cargo_name(),
                package.cargo_version(),
                "framework",
                "krs",
                package.manifest_dir().join("Cargo.toml"),
            )?);
        }
    }
    let (contexts, context_lookup) = prepare_contexts(contexts)?;
    let mut pending = Vec::new();
    let mut ids = BTreeSet::new();

    for host in descriptors {
        if host.protocol_version != ProtocolVersion::CURRENT {
            return Err(CollectionError::new(
                CollectionErrorKind::UnsupportedProtocol,
                format!(
                    "descriptor protocol {} is unsupported; expected {}",
                    host.protocol_version.0,
                    ProtocolVersion::CURRENT.0
                ),
            ));
        }
        validate_payload_item_kind(&host)?;
        validate_rule_reference_provenance(&host)?;
        host.validate_v7_ownership().map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                format!("invalid host protocol-v7 descriptor: {error}"),
            )
        })?;
        host.validate_configuration_pairing().map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                format!("invalid paired configuration descriptor: {error}"),
            )
        })?;
        let canonical_hint =
            canonicalize_path(host.id.package().manifest_dir(), "host manifest directory")?;
        let lookup_key = (
            host.id.package().cargo_name().to_owned(),
            host.id.package().cargo_version().to_owned(),
            canonical_hint,
        );
        let Some(&context_index) = context_lookup.get(&lookup_key) else {
            return Err(CollectionError::new(
                CollectionErrorKind::PackageNotSelected,
                format!(
                    "host package `{} {}` at `{}` is not in the selected collection",
                    host.id.package().cargo_name(),
                    host.id.package().cargo_version(),
                    host.id.package().manifest_dir().display()
                ),
            ));
        };
        let id = stable_item_id(&host.id, &contexts[context_index])?;
        if !ids.insert(id.clone()) {
            return Err(CollectionError::new(
                CollectionErrorKind::DuplicateItemId,
                format!("duplicate final item identity `{}`", display_item(&id)),
            ));
        }
        pending.push(PendingDescriptor {
            host,
            id,
            context_index,
        });
    }

    pending.sort_by(|left, right| left.id.cmp(&right.id));
    let context_aliases = pending
        .iter()
        .filter(|pending| pending.id.item_kind() == ItemKind::ContextAlias)
        .map(|pending| (pending.host.id.clone(), pending.id.clone()))
        .collect::<HashMap<_, _>>();
    let declarations = declared_type_table(&pending, builtins)?;
    let cell_fields = declared_cell_field_table(&pending)?;
    let head_targets = resolve_head_rule_targets(&pending, &cell_fields)?;
    let mut source_cache = BTreeMap::new();
    let mut resolved = Vec::with_capacity(pending.len());
    let mut declaration_metadata = Vec::with_capacity(pending.len());
    for pending in pending {
        let (provenance, visibility, explicit_symbol) = materialize_descriptor_provenance(
            &pending.host,
            &pending.host.payload,
            &pending.id,
            pending.context_index,
            &contexts,
            &mut source_cache,
        )?;
        let payload = resolve_payload(
            &pending.host.payload,
            &declarations,
            &cell_fields,
            &context_aliases,
            builtins,
            &head_targets,
        )?;
        declaration_metadata.push(DescriptorDeclaration::new(
            pending.id.clone(),
            visibility,
            explicit_symbol,
        ));
        resolved.push(Descriptor {
            id: pending.id,
            cfg: pending.host.cfg,
            provenance,
            payload,
        });
    }
    resolved.sort();
    let bundle =
        DescriptorBundle::with_declarations(resolved, declaration_metadata).map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::InvalidStableIdentity,
                format!("invalid declaration metadata coverage: {error}"),
            )
        })?;
    for descriptor in &bundle.descriptors {
        descriptor
            .validate_configuration_contract()
            .map_err(|error| {
                CollectionError::new(
                    CollectionErrorKind::InvalidConfiguration,
                    format!("invalid stable configuration descriptor: {error}"),
                )
            })?;
        descriptor.validate_v6_contract().map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::ProvenanceMismatch,
                format!("invalid stable protocol-v6 descriptor: {error}"),
            )
        })?;
        descriptor.validate_v7_contract().map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::ProvenanceMismatch,
                format!("invalid stable protocol-v7 descriptor: {error}"),
            )
        })?;
    }
    Ok(bundle)
}

fn is_framework_sort_descriptor(descriptor: &HostDescriptor) -> bool {
    descriptor.id.package().cargo_name() == "krs"
        && descriptor.id.rust_module_path().len() == 1
        && descriptor.id.rust_module_path()[0] == "krs"
        && descriptor.id.item_kind() == ItemKind::Sort
        && matches!(descriptor.id.item_name(), "KItem" | "KResult")
}

type ContextLookup = BTreeMap<(String, String, PathBuf), usize>;

fn prepare_contexts(
    contexts: impl IntoIterator<Item = PackageContext>,
) -> Result<(Vec<PreparedContext>, ContextLookup), CollectionError> {
    let mut prepared = Vec::new();
    let mut lookup = BTreeMap::new();
    let mut namespaces = BTreeSet::new();
    for context in contexts {
        if !namespaces.insert(context.package.k_namespace().to_owned()) {
            return Err(CollectionError::new(
                CollectionErrorKind::DuplicateKNamespace,
                format!(
                    "immutable K namespace `{}` is selected more than once",
                    context.package.k_namespace()
                ),
            ));
        }
        let manifest = canonicalize_path(&context.manifest_path, "Cargo manifest")?;
        if !manifest.is_file() {
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidPackageContext,
                format!("Cargo manifest `{}` is not a file", manifest.display()),
            ));
        }
        let package_dir = manifest.parent().ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::InvalidPackageContext,
                format!(
                    "Cargo manifest `{}` has no package directory",
                    manifest.display()
                ),
            )
        })?;
        let index = prepared.len();
        let key = (
            context.package.cargo_name().to_owned(),
            context.package.cargo_version().to_owned(),
            package_dir.to_owned(),
        );
        if lookup.insert(key, index).is_some() {
            return Err(CollectionError::new(
                CollectionErrorKind::DuplicatePackageContext,
                format!(
                    "Cargo package `{} {}` at `{}` has multiple collection contexts",
                    context.package.cargo_name(),
                    context.package.cargo_version(),
                    package_dir.display()
                ),
            ));
        }
        prepared.push(PreparedContext {
            package: context.package,
            crate_root: context.crate_root,
            package_dir: package_dir.to_owned(),
        });
    }
    Ok((prepared, lookup))
}

fn stable_item_id(
    host: &HostItemId,
    context: &PreparedContext,
) -> Result<StableItemId, CollectionError> {
    let (root, module_path) = host.rust_module_path().split_first().ok_or_else(|| {
        CollectionError::new(
            CollectionErrorKind::CrateRootMismatch,
            "host `module_path!()` was unexpectedly empty",
        )
    })?;
    if root != &context.crate_root {
        return Err(CollectionError::new(
            CollectionErrorKind::CrateRootMismatch,
            format!(
                "host module root `{root}` does not match selected target `{}`",
                context.crate_root
            ),
        ));
    }
    StableItemId::new(
        context.package.clone(),
        module_path.iter().cloned(),
        host.item_name(),
        host.item_kind(),
        host.disambiguator(),
    )
    .map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::InvalidStableIdentity,
            format!("cannot materialize stable item identity: {error}"),
        )
    })
}

fn validate_payload_item_kind(host: &HostDescriptor) -> Result<(), CollectionError> {
    let expected = match &host.payload {
        HostDescriptorPayload::Sort(_) => ItemKind::Sort,
        HostDescriptorPayload::Constructor(_) => ItemKind::Constructor,
        HostDescriptorPayload::Configuration(_) | HostDescriptorPayload::FixedConfiguration(_) => {
            ItemKind::Configuration
        }
        HostDescriptorPayload::Rule(rule) => match rule.sentence_kind {
            krs_ir::SentenceKind::Transition => ItemKind::Rule,
            krs_ir::SentenceKind::Equation => ItemKind::Equation,
            krs_ir::SentenceKind::Simplification => ItemKind::Simplification,
            krs_ir::SentenceKind::Alias => ItemKind::Alias,
            krs_ir::SentenceKind::Claim => ItemKind::Claim,
        },
        HostDescriptorPayload::Grammar(_) => ItemKind::Grammar,
        HostDescriptorPayload::StructuredRule(rule) => match rule.sentence_kind {
            krs_ir::SentenceKind::Transition => ItemKind::Rule,
            krs_ir::SentenceKind::Equation => ItemKind::Equation,
            krs_ir::SentenceKind::Simplification => ItemKind::Simplification,
            krs_ir::SentenceKind::Alias => ItemKind::Alias,
            krs_ir::SentenceKind::Claim => ItemKind::Claim,
        },
        HostDescriptorPayload::Cell(_) => ItemKind::Cell,
        HostDescriptorPayload::ConfigurationRule(rule) => match rule.sentence_kind {
            krs_ir::SentenceKind::Transition => ItemKind::Rule,
            krs_ir::SentenceKind::Equation => ItemKind::Equation,
            krs_ir::SentenceKind::Simplification => ItemKind::Simplification,
            krs_ir::SentenceKind::Alias => ItemKind::Alias,
            krs_ir::SentenceKind::Claim => ItemKind::Claim,
        },
        HostDescriptorPayload::HeadRule(rule) => match rule.sentence_kind {
            krs_ir::SentenceKind::Transition => ItemKind::Rule,
            krs_ir::SentenceKind::Equation => ItemKind::Equation,
            krs_ir::SentenceKind::Simplification => ItemKind::Simplification,
            krs_ir::SentenceKind::Alias => ItemKind::Alias,
            krs_ir::SentenceKind::Claim => ItemKind::Claim,
        },
        HostDescriptorPayload::ContextAlias(_) => ItemKind::ContextAlias,
    };
    if host.id.item_kind() != expected {
        return Err(CollectionError::new(
            CollectionErrorKind::ItemKindMismatch,
            format!(
                "host item `{}` declares kind {:?} but its payload requires {expected:?}",
                host.id.item_name(),
                host.id.item_kind()
            ),
        ));
    }
    Ok(())
}

fn validate_rule_reference_provenance(host: &HostDescriptor) -> Result<(), CollectionError> {
    let HostDescriptorPayload::Rule(rule) = &host.payload else {
        return Ok(());
    };
    rule.validate_reference_keys().map_err(|error| {
        CollectionError::new(CollectionErrorKind::InvalidReferenceKey, error.to_string())
    })?;
    rule.validate_bindings().map_err(|error| {
        CollectionError::new(CollectionErrorKind::InvalidRuleBindings, error.to_string())
    })?;
    let provenance_keys = host
        .provenance
        .authored()
        .iter()
        .map(krs_ir::HostAuthoredAnchor::key)
        .collect::<BTreeSet<_>>();
    for reference in &rule.references {
        expected_reference_kind(&reference.key)?;
        if !provenance_keys.contains(&reference.key) {
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidReferenceKey,
                format!(
                    "rule reference key `{}`#{} has no shared-parser provenance node",
                    reference.key.role(),
                    reference.key.ordinal()
                ),
            ));
        }
    }
    for role in [ProvenanceRole::RuleType, ProvenanceRole::RuleResultType] {
        let required = role.key(0).map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::InvalidReferenceKey,
                format!("cannot construct required rule reference key: {error}"),
            )
        })?;
        if !rule
            .references
            .iter()
            .any(|reference| reference.key == required)
        {
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidReferenceKey,
                format!(
                    "rule descriptor lacks required reference `{}`#0",
                    role.as_str()
                ),
            ));
        }
    }
    Ok(())
}

fn declared_type_table(
    pending: &[PendingDescriptor],
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>, CollectionError> {
    let mut declarations = HashMap::new();
    for descriptor in pending {
        let kind = descriptor.id.item_kind();
        let Some(key) = descriptor.host.declared_type else {
            if matches!(
                kind,
                ItemKind::Sort | ItemKind::Constructor | ItemKind::Configuration | ItemKind::Cell
            ) {
                return Err(CollectionError::new(
                    CollectionErrorKind::MissingTypeDeclaration,
                    format!(
                        "type declaration `{}` exposes no build-local Rust type",
                        display_item(&descriptor.id)
                    ),
                ));
            }
            continue;
        };
        if !matches!(
            kind,
            ItemKind::Sort | ItemKind::Constructor | ItemKind::Configuration | ItemKind::Cell
        ) {
            return Err(CollectionError::new(
                CollectionErrorKind::ItemKindMismatch,
                format!(
                    "non-type item `{}` exposes a declared Rust type key",
                    display_item(&descriptor.id)
                ),
            ));
        }
        let resolved = key.resolve();
        if kind != ItemKind::Constructor && !matches!(resolved, HostApplicationIdentity::Nominal(_))
        {
            return Err(CollectionError::new(
                CollectionErrorKind::ItemKindMismatch,
                format!(
                    "non-constructor `{}` exposes an enum-variant declaration identity",
                    display_item(&descriptor.id)
                ),
            ));
        }
        if let Some(registry) = builtins
            && let HostApplicationIdentity::Nominal(type_id) = resolved
            && (registry.resolve_sort(type_id).is_some()
                || registry.resolve_operation(type_id).is_some()
                || registry.resolve_map_operation(type_id).is_some())
        {
            return Err(CollectionError::new(
                CollectionErrorKind::DeclarationBuiltinCollision,
                format!(
                    "authored declaration `{}` reuses a compiler builtin marker type",
                    display_item(&descriptor.id)
                ),
            ));
        }
        if let Some((previous, _)) = declarations.insert(resolved, (descriptor.id.clone(), kind)) {
            return Err(CollectionError::new(
                CollectionErrorKind::DuplicateTypeDeclaration,
                format!(
                    "items `{}` and `{}` expose the same build-local Rust type",
                    display_item(&previous),
                    display_item(&descriptor.id)
                ),
            ));
        }
    }
    Ok(declarations)
}

type HostCellKey = (TypeId, TypeId);

fn declared_cell_field_table(
    pending: &[PendingDescriptor],
) -> Result<HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>, CollectionError> {
    let mut fields = HashMap::new();
    for descriptor in pending {
        let declaration = match &descriptor.host.payload {
            HostDescriptorPayload::FixedConfiguration(configuration) => &configuration.declaration,
            HostDescriptorPayload::Cell(declaration) => declaration.as_ref(),
            HostDescriptorPayload::Sort(_)
            | HostDescriptorPayload::Constructor(_)
            | HostDescriptorPayload::Configuration(_)
            | HostDescriptorPayload::Rule(_)
            | HostDescriptorPayload::Grammar(_)
            | HostDescriptorPayload::StructuredRule(_)
            | HostDescriptorPayload::ConfigurationRule(_)
            | HostDescriptorPayload::HeadRule(_)
            | HostDescriptorPayload::ContextAlias(_) => continue,
        };
        for field in &declaration.fields {
            let key = field.reference.cell.resolve();
            let stable = krs_ir::DescriptorCellIdentity {
                owner: descriptor.id.clone(),
                field: field.rust_field.clone(),
            };
            if fields.insert(key, stable).is_some() {
                return Err(CollectionError::new(
                    CollectionErrorKind::DuplicateTypeDeclaration,
                    format!(
                        "fixed cell field `{}` on `{}` reuses an owner/field marker identity",
                        field.rust_field,
                        display_item(&descriptor.id)
                    ),
                ));
            }
        }
    }
    Ok(fields)
}

#[derive(Clone, Debug)]
struct HeadRuleCellTarget {
    identity: krs_ir::DescriptorCellIdentity,
    names: Vec<String>,
    wrapper: krs_ir::CellWrapper,
}

#[derive(Clone, Debug)]
struct HeadRuleTarget {
    configuration: StableItemId,
    cells: Vec<HeadRuleCellTarget>,
}

fn resolve_head_rule_targets(
    pending: &[PendingDescriptor],
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
) -> Result<Vec<HeadRuleTarget>, CollectionError> {
    if !pending
        .iter()
        .any(|descriptor| matches!(descriptor.host.payload, HostDescriptorPayload::HeadRule(_)))
    {
        return Ok(Vec::new());
    }
    let configurations = pending
        .iter()
        .filter_map(|descriptor| match &descriptor.host.payload {
            HostDescriptorPayload::FixedConfiguration(configuration) => {
                Some((descriptor, configuration.as_ref()))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let has_implicit_target = pending.iter().any(|descriptor| {
        matches!(
            &descriptor.host.payload,
            HostDescriptorPayload::HeadRule(rule) if rule.configuration.is_none()
        )
    });
    if has_implicit_target && configurations.len() != 1 {
        let detail = match configurations.len() {
            0 => "a `for Sort` rule requires one fixed configuration, but none was collected"
                .to_owned(),
            count => format!(
                "a `for Sort` rule requires one unambiguous fixed configuration, but {count} candidates were collected"
            ),
        };
        return Err(CollectionError::new(
            CollectionErrorKind::InvalidConfiguration,
            detail,
        ));
    }
    let targets = configurations
        .into_iter()
        .map(|(descriptor, configuration)| {
            let mut cells = Vec::new();
            for field in &configuration.declaration.fields {
                let krs_ir::ProtocolCellContent::Leaf { wrapper, .. } = &field.content else {
                    continue;
                };
                let identity = cell_fields
                    .get(&field.reference.cell.resolve())
                    .cloned()
                    .ok_or_else(|| {
                        CollectionError::new(
                            CollectionErrorKind::UnresolvedTypeReference,
                            format!(
                                "top-level fixed cell `{}` has no stable owner/field identity",
                                field.rust_field
                            ),
                        )
                    })?;
                let mut names = vec![field.rust_field.clone()];
                if let Some(emitted) = &field.emitted_name
                    && !names.contains(&emitted.value)
                {
                    names.push(emitted.value.clone());
                }
                cells.push(HeadRuleCellTarget {
                    identity,
                    names,
                    wrapper: *wrapper,
                });
            }
            Ok(HeadRuleTarget {
                configuration: descriptor.id.clone(),
                cells,
            })
        })
        .collect::<Result<Vec<_>, CollectionError>>()?;
    if has_implicit_target {
        let computations = targets[0]
            .cells
            .iter()
            .filter(|cell| cell.wrapper == krs_ir::CellWrapper::KCell)
            .count();
        if computations != 1 {
            let detail = match computations {
                0 => "selected fixed configuration has no matching top-level KCell<KSequence> computation cell"
                    .to_owned(),
                count => format!(
                    "selected fixed configuration has {count} matching top-level KCell<KSequence> computation cells"
                ),
            };
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                detail,
            ));
        }
    }
    Ok(targets)
}

#[allow(clippy::too_many_lines)] // Resolution keeps one closed head-rule transport audit together.
fn resolve_head_rule(
    rule: &krs_ir::HostHeadRule,
    targets: &[HeadRuleTarget],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorHeadRule, CollectionError> {
    let target = if let Some(configuration) = &rule.configuration {
        let selected = resolve_configuration_reference(configuration, declarations)?;
        targets
            .iter()
            .find(|target| target.configuration == selected.configuration)
            .ok_or_else(|| {
                CollectionError::new(
                    CollectionErrorKind::InvalidConfiguration,
                    "cell-record rule names a fixed configuration that was not collected",
                )
            })?
    } else {
        let [target] = targets else {
            let detail = match targets.len() {
                0 => "head-anchored rules require one fixed configuration, but none was collected"
                    .to_owned(),
                count => format!(
                    "a `for Sort` rule requires one unambiguous fixed configuration, but {count} candidates were collected; use a configuration-owned cell-record rule where appropriate"
                ),
            };
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                detail,
            ));
        };
        target
    };
    let computations = target
        .cells
        .iter()
        .filter(|cell| {
            cell.wrapper == krs_ir::CellWrapper::KCell
                && rule
                    .computation_cell_name
                    .as_ref()
                    .is_none_or(|name| cell.names.iter().any(|candidate| candidate == name))
        })
        .collect::<Vec<_>>();
    let [computation] = computations.as_slice() else {
        let detail = match computations.len() {
            0 => "selected fixed configuration has no matching top-level KCell<KSequence> computation cell"
                .to_owned(),
            count => format!(
                "selected fixed configuration has {count} matching top-level KCell<KSequence> computation cells"
            ),
        };
        return Err(CollectionError::new(
            CollectionErrorKind::InvalidConfiguration,
            detail,
        ));
    };
    let resolve_cell = |cell: &krs_ir::HostHeadRuleCellReference| {
        let matches = target
            .cells
            .iter()
            .filter(|candidate| candidate.names.iter().any(|name| name == &cell.name))
            .collect::<Vec<_>>();
        let [resolved] = matches.as_slice() else {
            let detail = match matches.len() {
                0 => format!(
                    "readable rule extra names no top-level fixed cell `{}`",
                    cell.name
                ),
                count => format!(
                    "readable rule extra cell name `{}` is ambiguous across {count} top-level cells",
                    cell.name
                ),
            };
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                detail,
            ));
        };
        if resolved.identity == computation.identity {
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                format!(
                    "readable rule extra may not mention computation cell `{}`",
                    cell.name
                ),
            ));
        }
        Ok(krs_ir::DescriptorCellReference {
            key: cell.key.clone(),
            cell: resolved.identity.clone(),
        })
    };
    let extras = rule
        .extras
        .iter()
        .map(|extra| {
            Ok(match extra {
                krs_ir::ProtocolHeadRuleExtra::HaveMap {
                    cell,
                    key,
                    value_binding,
                } => krs_ir::ProtocolHeadRuleExtra::HaveMap {
                    cell: resolve_cell(cell)?,
                    key: resolve_term(key, declarations, builtins)?,
                    value_binding: value_binding.clone(),
                },
                krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                    cell,
                    base_binding,
                    update,
                } => krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                    cell: resolve_cell(cell)?,
                    base_binding: base_binding.clone(),
                    update: resolve_term(update, declarations, builtins)?,
                },
                krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                    cell,
                    result_key,
                    before,
                    after,
                } => krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                    cell: resolve_cell(cell)?,
                    result_key: result_key.clone(),
                    before: resolve_term(before, declarations, builtins)?,
                    after: resolve_term(after, declarations, builtins)?,
                },
            })
        })
        .collect::<Result<Vec<_>, CollectionError>>()?;
    let result = match &rule.result {
        krs_ir::ProtocolHeadRuleResult::Replace(term) => {
            krs_ir::ProtocolHeadRuleResult::Replace(resolve_term(term, declarations, builtins)?)
        }
        krs_ir::ProtocolHeadRuleResult::Splice(items) => krs_ir::ProtocolHeadRuleResult::Splice(
            items
                .iter()
                .map(|term| resolve_term(term, declarations, builtins))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        krs_ir::ProtocolHeadRuleResult::Erase => krs_ir::ProtocolHeadRuleResult::Erase,
    };
    Ok(krs_ir::DescriptorHeadRule {
        sentence_kind: rule.sentence_kind,
        label: rule.label.clone(),
        pattern_key: rule.pattern_key.clone(),
        result_key: rule.result_key.clone(),
        head_sort: rule
            .head_sort
            .as_ref()
            .map(|sort| resolve_sort_reference(sort, declarations, builtins))
            .transpose()?,
        configuration: target.configuration.clone(),
        computation_cell: krs_ir::DescriptorCellReference {
            key: rule.pattern_key.clone(),
            cell: computation.identity.clone(),
        },
        bindings: rule
            .bindings
            .iter()
            .map(|binding| {
                Ok(krs_ir::ProtocolHeadRuleBinding {
                    name: binding.name.clone(),
                    refinement: binding
                        .refinement
                        .as_ref()
                        .map(|sort| resolve_sort_reference(sort, declarations, builtins))
                        .transpose()?,
                })
            })
            .collect::<Result<Vec<_>, CollectionError>>()?,
        subject: resolve_term(&rule.subject, declarations, builtins)?,
        result,
        extras,
    })
}

#[allow(clippy::too_many_lines)]
fn resolve_payload(
    payload: &HostDescriptorPayload,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    context_aliases: &HashMap<HostItemId, StableItemId>,
    builtins: Option<&HostBuiltinRegistry>,
    head_targets: &[HeadRuleTarget],
) -> Result<DescriptorPayload, CollectionError> {
    match payload {
        HostDescriptorPayload::Sort(sort) => {
            let mut parents = sort
                .parents
                .iter()
                .map(|parent| resolve_nominal_reference(parent, ItemKind::Sort, declarations))
                .collect::<Result<Vec<_>, _>>()?;
            parents.sort();
            parents.dedup();
            Ok(DescriptorPayload::Sort(SortDescriptor { parents }))
        }
        HostDescriptorPayload::Constructor(constructor) => {
            Ok(DescriptorPayload::Constructor(ConstructorDescriptor {
                sort: resolve_sort_reference(&constructor.sort, declarations, builtins)?.sort,
                syntax: constructor.syntax.clone(),
                fields: constructor
                    .fields
                    .iter()
                    .map(|field| {
                        Ok(ConstructorFieldDescriptor {
                            name: field.name.clone(),
                            sort: Some(resolve_constructor_field_sort(
                                &field.sort,
                                declarations,
                                builtins,
                            )?),
                        })
                    })
                    .collect::<Result<Vec<_>, CollectionError>>()?,
            }))
        }
        HostDescriptorPayload::Configuration(configuration) => {
            resolve_configuration(configuration, declarations).map(DescriptorPayload::Configuration)
        }
        HostDescriptorPayload::Rule(rule) => {
            rule.validate_reference_keys().map_err(|error| {
                CollectionError::new(CollectionErrorKind::InvalidReferenceKey, error.to_string())
            })?;
            let mut references = rule
                .references
                .iter()
                .map(|reference| {
                    let expected = expected_reference_kind(&reference.key)?;
                    Ok(DescriptorReference::new(
                        reference.key.clone(),
                        resolve_nominal_reference(&reference.target, expected, declarations)?,
                    ))
                })
                .collect::<Result<Vec<_>, CollectionError>>()?;
            references.sort();
            let resolved = RuleDescriptor {
                sentence_kind: rule.sentence_kind,
                parameters: rule
                    .parameters
                    .iter()
                    .map(|parameter| {
                        Ok(RuleParameterDescriptor {
                            bindings: parameter.bindings.clone(),
                            sort: resolve_nominal_reference(
                                &parameter.sort,
                                ItemKind::Sort,
                                declarations,
                            )?,
                            pattern: parameter.pattern.clone(),
                        })
                    })
                    .collect::<Result<Vec<_>, CollectionError>>()?,
                result_sort: resolve_nominal_reference(
                    &rule.result_sort,
                    ItemKind::Sort,
                    declarations,
                )?,
                references,
                lhs: rule.lhs.clone(),
                rhs: rule.rhs.clone(),
            };
            resolved.validate_reference_keys().map_err(|error| {
                CollectionError::new(CollectionErrorKind::InvalidReferenceKey, error.to_string())
            })?;
            resolved.validate_bindings().map_err(|error| {
                CollectionError::new(CollectionErrorKind::InvalidRuleBindings, error.to_string())
            })?;
            Ok(DescriptorPayload::Rule(resolved))
        }
        HostDescriptorPayload::Grammar(grammar) => Ok(DescriptorPayload::Grammar(Box::new(
            resolve_grammar(grammar, declarations, context_aliases, builtins)?,
        ))),
        HostDescriptorPayload::StructuredRule(rule) => Ok(DescriptorPayload::StructuredRule(
            Box::new(resolve_structured_rule(rule, declarations, builtins)?),
        )),
        HostDescriptorPayload::FixedConfiguration(configuration) => {
            Ok(DescriptorPayload::FixedConfiguration(Box::new(
                resolve_fixed_configuration(configuration, declarations, cell_fields, builtins)?,
            )))
        }
        HostDescriptorPayload::Cell(declaration) => Ok(DescriptorPayload::Cell(Box::new(
            resolve_cell_declaration(declaration, declarations, cell_fields, builtins)?,
        ))),
        HostDescriptorPayload::ConfigurationRule(rule) => {
            Ok(DescriptorPayload::ConfigurationRule(Box::new(
                resolve_configuration_rule(rule, declarations, cell_fields, builtins)?,
            )))
        }
        HostDescriptorPayload::HeadRule(rule) => Ok(DescriptorPayload::HeadRule(Box::new(
            resolve_head_rule(rule, head_targets, declarations, builtins)?,
        ))),
        HostDescriptorPayload::ContextAlias(alias) => {
            Ok(DescriptorPayload::ContextAlias(Box::new(
                resolve_context_alias(alias, declarations, cell_fields, builtins)?,
            )))
        }
    }
}

fn resolve_context_alias(
    alias: &krs_ir::HostContextAlias,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorContextAlias, CollectionError> {
    Ok(krs_ir::DescriptorContextAlias {
        declaration_key: alias.declaration_key.clone(),
        name_key: alias.name_key.clone(),
        name: alias.name.clone(),
        here_key: alias.here_key.clone(),
        here: alias.here.clone(),
        pattern_key: alias.pattern_key.clone(),
        configuration: resolve_configuration_reference(&alias.configuration, declarations)?,
        bindings: alias
            .bindings
            .iter()
            .map(|binding| {
                Ok(krs_ir::ProtocolContextAliasBinding {
                    name: binding.name.clone(),
                    kind: match &binding.kind {
                        krs_ir::ProtocolContextAliasBindingKind::Here => {
                            krs_ir::ProtocolContextAliasBindingKind::Here
                        }
                        krs_ir::ProtocolContextAliasBindingKind::Term { sort } => {
                            krs_ir::ProtocolContextAliasBindingKind::Term {
                                sort: resolve_sort_reference(sort, declarations, builtins)?,
                            }
                        }
                        krs_ir::ProtocolContextAliasBindingKind::KSequenceFrame => {
                            krs_ir::ProtocolContextAliasBindingKind::KSequenceFrame
                        }
                        krs_ir::ProtocolContextAliasBindingKind::MapFrame => {
                            krs_ir::ProtocolContextAliasBindingKind::MapFrame
                        }
                        krs_ir::ProtocolContextAliasBindingKind::ConfigurationFrame => {
                            krs_ir::ProtocolContextAliasBindingKind::ConfigurationFrame
                        }
                    },
                })
            })
            .collect::<Result<Vec<_>, CollectionError>>()?,
        pattern: resolve_rule_cells(&alias.pattern, declarations, cell_fields, builtins)?,
    })
}

fn resolve_configuration(
    configuration: &HostConfigurationDescriptor,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<ConfigurationDescriptor, CollectionError> {
    let main_variable = configuration
        .main_variable
        .as_ref()
        .map(|variable| {
            Ok(ConfigurationVariableDescriptor {
                binding: variable.binding.clone(),
                external_name: variable.external_name.clone(),
                sort: DescriptorReference::new(
                    variable.sort.key.clone(),
                    resolve_nominal_reference(&variable.sort.target, ItemKind::Sort, declarations)?,
                ),
            })
        })
        .transpose()?;
    let mut references = configuration
        .initializer
        .references
        .iter()
        .map(|reference| {
            Ok(DescriptorReference::new(
                reference.key.clone(),
                resolve_nominal_reference(&reference.target, ItemKind::Constructor, declarations)?,
            ))
        })
        .collect::<Result<Vec<_>, CollectionError>>()?;
    references.sort();
    let resolved = ConfigurationDescriptor {
        root: configuration.root.clone(),
        cell: configuration.cell.clone(),
        main_variable,
        initializer: ConfigurationInitializerDescriptor {
            name: configuration.initializer.name.clone(),
            term: configuration.initializer.term.clone(),
            references,
        },
    };
    resolved.validate().map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::InvalidConfiguration,
            format!("invalid resolved configuration: {error}"),
        )
    })?;
    Ok(resolved)
}

fn resolve_cell_reference(
    reference: &krs_ir::HostCellReference,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
) -> Result<krs_ir::DescriptorCellReference, CollectionError> {
    let key = reference.cell.resolve();
    let cell = cell_fields.get(&key).cloned().ok_or_else(|| {
        CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "cell reference `{}#{}` has no selected owner/field-marker declaration",
                reference.key.role(),
                reference.key.ordinal()
            ),
        )
    })?;
    Ok(krs_ir::DescriptorCellReference {
        key: reference.key.clone(),
        cell,
    })
}

fn resolve_cell_declaration_reference(
    reference: &krs_ir::HostCellDeclarationReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<krs_ir::DescriptorCellDeclarationReference, CollectionError> {
    Ok(krs_ir::DescriptorCellDeclarationReference {
        key: reference.key.clone(),
        declaration: resolve_nominal_reference(
            &reference.declaration,
            ItemKind::Cell,
            declarations,
        )?,
    })
}

fn resolve_cell_declaration(
    declaration: &krs_ir::HostCellDeclaration,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorCellDeclaration, CollectionError> {
    Ok(krs_ir::ProtocolCellDeclaration {
        key: declaration.key.clone(),
        fields: declaration
            .fields
            .iter()
            .map(|field| {
                let content = match &field.content {
                    ProtocolCellContent::Leaf {
                        wrapper_key,
                        wrapper,
                        sort,
                        arguments,
                    } => ProtocolCellContent::Leaf {
                        wrapper_key: wrapper_key.clone(),
                        wrapper: *wrapper,
                        sort: resolve_sort_reference(sort, declarations, builtins)?,
                        arguments: arguments
                            .iter()
                            .map(|argument| {
                                resolve_sort_reference(argument, declarations, builtins)
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    },
                    ProtocolCellContent::Nested { declaration } => ProtocolCellContent::Nested {
                        declaration: resolve_cell_declaration_reference(declaration, declarations)?,
                    },
                };
                Ok(krs_ir::ProtocolCellField {
                    reference: resolve_cell_reference(&field.reference, cell_fields)?,
                    rust_field: field.rust_field.clone(),
                    emitted_name: field.emitted_name.clone(),
                    color: field.color.clone(),
                    content,
                })
            })
            .collect::<Result<Vec<_>, CollectionError>>()?,
    })
}

fn resolve_fixed_configuration(
    configuration: &krs_ir::HostFixedConfiguration,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorFixedConfiguration, CollectionError> {
    let declaration = resolve_cell_declaration(
        &configuration.declaration,
        declarations,
        cell_fields,
        builtins,
    )?;
    let owner = resolve_declared_identity(
        HostApplicationIdentity::Nominal(configuration.initializer.owner.resolve()),
        "Self",
        ItemKind::Configuration,
        declarations,
    )?;
    let variables = configuration
        .initializer
        .variables
        .iter()
        .map(|variable| {
            Ok(krs_ir::ProtocolConfigurationVariable {
                binding_key: variable.binding_key.clone(),
                binding: variable.binding.clone(),
                external_name_key: variable.external_name_key.clone(),
                external_name: variable.external_name.clone(),
                sort: resolve_sort_reference(&variable.sort, declarations, builtins)?,
                main_key: variable.main_key.clone(),
            })
        })
        .collect::<Result<Vec<_>, CollectionError>>()?;
    let cells = configuration
        .initializer
        .cells
        .iter()
        .map(|cell| resolve_initializer_cell(cell, declarations, cell_fields, builtins))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(krs_ir::DescriptorFixedConfiguration {
        root: configuration.root.clone(),
        declaration,
        initializer: krs_ir::ProtocolConfigurationInitializer {
            key: configuration.initializer.key.clone(),
            owner_key: configuration.initializer.owner_key.clone(),
            owner,
            variables,
            body_key: configuration.initializer.body_key.clone(),
            cells,
        },
    })
}

fn resolve_initializer_cell(
    cell: &krs_ir::HostInitializerCell,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorInitializerCell, CollectionError> {
    let content = match &cell.content {
        ProtocolInitializerCellContent::Leaf {
            constructor_key,
            wrapper,
            value,
        } => ProtocolInitializerCellContent::Leaf {
            constructor_key: constructor_key.clone(),
            wrapper: *wrapper,
            value: resolve_initializer_state(value, declarations, builtins)?,
        },
        ProtocolInitializerCellContent::Nested {
            declaration,
            children,
        } => ProtocolInitializerCellContent::Nested {
            declaration: resolve_cell_declaration_reference(declaration, declarations)?,
            children: children
                .iter()
                .map(|child| resolve_initializer_cell(child, declarations, cell_fields, builtins))
                .collect::<Result<Vec<_>, _>>()?,
        },
    };
    Ok(krs_ir::ProtocolInitializerCell {
        key: cell.key.clone(),
        field: resolve_cell_reference(&cell.field, cell_fields)?,
        content,
    })
}

fn resolve_initializer_term(
    term: &krs_ir::ProtocolInitializerTerm<HostTerm>,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::ProtocolInitializerTerm<DescriptorTerm>, CollectionError> {
    Ok(krs_ir::ProtocolInitializerTerm {
        key: term.key.clone(),
        term: resolve_term(&term.term, declarations, builtins)?,
    })
}

fn resolve_initializer_state(
    state: &krs_ir::HostInitializerStateTerm,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorInitializerStateTerm, CollectionError> {
    Ok(match state {
        ProtocolInitializerStateTerm::Term(term) => ProtocolInitializerStateTerm::Term(
            resolve_initializer_term(term, declarations, builtins)?,
        ),
        ProtocolInitializerStateTerm::KSequence(sequence) => {
            ProtocolInitializerStateTerm::KSequence(krs_ir::ProtocolKSequence {
                payload_key: sequence.payload_key.clone(),
                dot_k_key: sequence.dot_k_key.clone(),
                notation: sequence.notation,
                items: sequence
                    .items
                    .iter()
                    .map(|item| {
                        Ok(krs_ir::ProtocolKSequenceItem {
                            key: item.key.clone(),
                            value: resolve_initializer_term(&item.value, declarations, builtins)?,
                        })
                    })
                    .collect::<Result<Vec<_>, CollectionError>>()?,
            })
        }
        ProtocolInitializerStateTerm::Map(map) => {
            ProtocolInitializerStateTerm::Map(krs_ir::ProtocolMap {
                payload_key: map.payload_key.clone(),
                body: resolve_initializer_map_body(&map.body, declarations, builtins)?,
            })
        }
    })
}

fn resolve_initializer_map_body(
    body: &krs_ir::ProtocolMapBody<HostTerm>,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::ProtocolMapBody<DescriptorTerm>, CollectionError> {
    Ok(match body {
        ProtocolMapBody::Empty { explicit_dot } => ProtocolMapBody::Empty {
            explicit_dot: *explicit_dot,
        },
        ProtocolMapBody::Items { items } => ProtocolMapBody::Items {
            items: items
                .iter()
                .map(|item| {
                    Ok(krs_ir::ProtocolMapItem {
                        key_key: item.key_key.clone(),
                        key: resolve_initializer_term(&item.key, declarations, builtins)?,
                        value_key: item.value_key.clone(),
                        value: resolve_initializer_term(&item.value, declarations, builtins)?,
                    })
                })
                .collect::<Result<Vec<_>, CollectionError>>()?,
        },
        ProtocolMapBody::Update {
            base_key,
            base,
            key_key,
            key,
            value_key,
            value,
        } => ProtocolMapBody::Update {
            base_key: base_key.clone(),
            base: resolve_initializer_term(base, declarations, builtins)?,
            key_key: key_key.clone(),
            key: resolve_initializer_term(key, declarations, builtins)?,
            value_key: value_key.clone(),
            value: resolve_initializer_term(value, declarations, builtins)?,
        },
    })
}

fn resolve_configuration_reference(
    reference: &krs_ir::HostConfigurationReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<krs_ir::DescriptorConfigurationReference, CollectionError> {
    Ok(krs_ir::DescriptorConfigurationReference {
        key: reference.key.clone(),
        configuration: resolve_nominal_reference(
            &reference.configuration,
            ItemKind::Configuration,
            declarations,
        )?,
    })
}

fn resolve_rule_frame(frame: &ProtocolRuleFrame) -> ProtocolRuleFrame {
    frame.clone()
}

fn resolve_rule_state(
    state: &krs_ir::ProtocolRuleStateTerm<HostTerm>,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::ProtocolRuleStateTerm<DescriptorTerm>, CollectionError> {
    Ok(match state {
        ProtocolRuleStateTerm::Term(term) => {
            ProtocolRuleStateTerm::Term(resolve_term(term, declarations, builtins)?)
        }
        ProtocolRuleStateTerm::KSequence(sequence) => {
            ProtocolRuleStateTerm::KSequence(krs_ir::ProtocolRuleKSequence {
                payload_key: sequence.payload_key.clone(),
                dot_k_key: sequence.dot_k_key.clone(),
                notation: sequence.notation,
                items: sequence
                    .items
                    .iter()
                    .map(|item| {
                        Ok(krs_ir::ProtocolRuleKSequenceItem {
                            key: item.key.clone(),
                            value: resolve_term(&item.value, declarations, builtins)?,
                        })
                    })
                    .collect::<Result<Vec<_>, CollectionError>>()?,
                tail: resolve_rule_frame(&sequence.tail),
            })
        }
        ProtocolRuleStateTerm::Map(map) => ProtocolRuleStateTerm::Map(krs_ir::ProtocolRuleMap {
            payload_key: map.payload_key.clone(),
            body: resolve_rule_map_body(&map.body, declarations, builtins)?,
        }),
    })
}

fn resolve_rule_map_body(
    body: &krs_ir::ProtocolRuleMapBody<HostTerm>,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::ProtocolRuleMapBody<DescriptorTerm>, CollectionError> {
    Ok(match body {
        ProtocolRuleMapBody::Empty { explicit_dot } => ProtocolRuleMapBody::Empty {
            explicit_dot: *explicit_dot,
        },
        ProtocolRuleMapBody::Items { items, remainder } => ProtocolRuleMapBody::Items {
            items: items
                .iter()
                .map(|item| {
                    Ok(krs_ir::ProtocolRuleMapItem {
                        key_key: item.key_key.clone(),
                        key: resolve_term(&item.key, declarations, builtins)?,
                        value_key: item.value_key.clone(),
                        value: resolve_term(&item.value, declarations, builtins)?,
                    })
                })
                .collect::<Result<Vec<_>, CollectionError>>()?,
            remainder: resolve_rule_frame(remainder),
        },
        ProtocolRuleMapBody::Update {
            base_key,
            base,
            key_key,
            key,
            value_key,
            value,
        } => ProtocolRuleMapBody::Update {
            base_key: base_key.clone(),
            base: resolve_term(base, declarations, builtins)?,
            key_key: key_key.clone(),
            key: resolve_term(key, declarations, builtins)?,
            value_key: value_key.clone(),
            value: resolve_term(value, declarations, builtins)?,
        },
    })
}

fn resolve_rule_cells(
    cells: &krs_ir::HostRuleCells,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorRuleCells, CollectionError> {
    Ok(krs_ir::ProtocolRuleCells {
        key: cells.key.clone(),
        cells: cells
            .cells
            .iter()
            .map(|cell| {
                Ok(krs_ir::ProtocolRuleCell {
                    field: resolve_cell_reference(&cell.field, cell_fields)?,
                    wrapper_key: cell.wrapper_key.clone(),
                    wrapper: cell.wrapper,
                    value: resolve_rule_state(&cell.value, declarations, builtins)?,
                })
            })
            .collect::<Result<Vec<_>, CollectionError>>()?,
        remainder: resolve_rule_frame(&cells.remainder),
    })
}

fn resolve_configuration_rule(
    rule: &krs_ir::HostConfigurationRule,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorConfigurationRule, CollectionError> {
    Ok(krs_ir::DescriptorConfigurationRule {
        sentence_kind: rule.sentence_kind,
        label: rule.label.clone(),
        requires: rule
            .requires
            .as_ref()
            .map(|condition| {
                Ok(krs_ir::DescriptorRuleCondition {
                    key: condition.key.clone(),
                    term: resolve_term(&condition.term, declarations, builtins)?,
                })
            })
            .transpose()?,
        claim: rule
            .claim
            .as_ref()
            .map(|claim| {
                Ok(krs_ir::DescriptorClaim {
                    declaration_key: claim.declaration_key.clone(),
                    modality_key: claim.modality_key.clone(),
                    modality: claim.modality,
                    circularity_key: claim.circularity_key.clone(),
                    universals: resolve_claim_binders(&claim.universals, declarations, builtins)?,
                    existentials: resolve_claim_binders(
                        &claim.existentials,
                        declarations,
                        builtins,
                    )?,
                    ensures: claim
                        .ensures
                        .as_ref()
                        .map(|condition| {
                            Ok(krs_ir::DescriptorRuleCondition {
                                key: condition.key.clone(),
                                term: resolve_term(&condition.term, declarations, builtins)?,
                            })
                        })
                        .transpose()?,
                    or_bool_keys: claim.or_bool_keys.clone(),
                })
            })
            .transpose()?,
        pattern_key: rule.pattern_key.clone(),
        subject_configuration: resolve_configuration_reference(
            &rule.subject_configuration,
            declarations,
        )?,
        result_key: rule.result_key.clone(),
        result_configuration: resolve_configuration_reference(
            &rule.result_configuration,
            declarations,
        )?,
        bindings: rule
            .bindings
            .iter()
            .map(|binding| {
                Ok(krs_ir::ProtocolRuleBinding {
                    name: binding.name.clone(),
                    kind: match &binding.kind {
                        krs_ir::ProtocolRuleBindingKind::Term { sort } => {
                            krs_ir::ProtocolRuleBindingKind::Term {
                                sort: resolve_sort_reference(sort, declarations, builtins)?,
                            }
                        }
                        krs_ir::ProtocolRuleBindingKind::KSequenceFrame => {
                            krs_ir::ProtocolRuleBindingKind::KSequenceFrame
                        }
                        krs_ir::ProtocolRuleBindingKind::MapFrame => {
                            krs_ir::ProtocolRuleBindingKind::MapFrame
                        }
                        krs_ir::ProtocolRuleBindingKind::ConfigurationFrame => {
                            krs_ir::ProtocolRuleBindingKind::ConfigurationFrame
                        }
                    },
                })
            })
            .collect::<Result<Vec<_>, CollectionError>>()?,
        subject: resolve_rule_cells(&rule.subject, declarations, cell_fields, builtins)?,
        result: resolve_rule_cells(&rule.result, declarations, cell_fields, builtins)?,
    })
}

fn resolve_claim_binders(
    binders: &[krs_ir::HostClaimBinder],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<Vec<krs_ir::DescriptorClaimBinder>, CollectionError> {
    binders
        .iter()
        .map(|binder| {
            Ok(krs_ir::DescriptorClaimBinder {
                declaration_key: binder.declaration_key.clone(),
                name_key: binder.name_key.clone(),
                name: binder.name.clone(),
                sort: resolve_sort_reference(&binder.sort, declarations, builtins)?,
            })
        })
        .collect()
}

fn expected_reference_kind(key: &ProvenanceKey) -> Result<ItemKind, CollectionError> {
    match key.role() {
        "rule_type" | "rule_result_type" => Ok(ItemKind::Sort),
        "rule_left_path" | "rule_right_path" => Ok(ItemKind::Constructor),
        role => Err(CollectionError::new(
            CollectionErrorKind::InvalidReferenceKey,
            format!("rule reference key uses unsupported parser role `{role}`"),
        )),
    }
}

fn resolve_nominal_reference(
    reference: &HostTypeReference,
    expected: ItemKind,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<StableItemId, CollectionError> {
    resolve_declared_identity(
        HostApplicationIdentity::Nominal(reference.key.resolve()),
        &reference.authored_path,
        expected,
        declarations,
    )
}

fn resolve_constructor_field_sort(
    reference: &HostTypeReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<DescriptorSortRef, CollectionError> {
    let type_id = reference.key.resolve();
    if let Some((id, kind)) = declarations.get(&HostApplicationIdentity::Nominal(type_id)) {
        if *kind != ItemKind::Sort {
            return Err(CollectionError::new(
                CollectionErrorKind::ReferenceKindMismatch,
                format!(
                    "Rust path `{}` resolves to {kind:?} `{}`, but Sort is required",
                    reference.authored_path,
                    display_item(id)
                ),
            ));
        }
        Ok(DescriptorSortRef::Declared(id.clone()))
    } else if let Some(sort) = builtins.and_then(|registry| registry.resolve_sort(type_id)) {
        Ok(DescriptorSortRef::Builtin(sort))
    } else {
        Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{}` resolves to neither a selected sort nor a registered builtin sort",
                reference.authored_path
            ),
        ))
    }
}

fn resolve_declared_identity(
    identity: HostApplicationIdentity,
    authored_path: &str,
    expected: ItemKind,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<StableItemId, CollectionError> {
    let Some((id, kind)) = declarations.get(&identity) else {
        return Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{authored_path}` does not resolve to a selected KRS type declaration"
            ),
        ));
    };
    if *kind != expected {
        return Err(CollectionError::new(
            CollectionErrorKind::ReferenceKindMismatch,
            format!(
                "Rust path `{}` resolves to {:?} `{}`, but {:?} is required",
                authored_path,
                kind,
                display_item(id),
                expected
            ),
        ));
    }
    Ok(id.clone())
}

fn resolve_sort_reference(
    reference: &HostSortReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<DescriptorSortReference, CollectionError> {
    let type_id = reference.target.key.resolve();
    let sort = if let Some((id, kind)) =
        declarations.get(&HostApplicationIdentity::Nominal(type_id))
    {
        if *kind != ItemKind::Sort {
            return Err(CollectionError::new(
                CollectionErrorKind::ReferenceKindMismatch,
                format!(
                    "Rust path `{}` resolves to {kind:?} `{}`, but Sort is required",
                    reference.target.authored_path,
                    display_item(id)
                ),
            ));
        }
        DescriptorSortRef::Declared(id.clone())
    } else if let Some(sort) = builtins.and_then(|registry| registry.resolve_sort(type_id)) {
        DescriptorSortRef::Builtin(sort)
    } else {
        return Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{}` resolves to neither a selected sort nor a registered builtin sort",
                reference.target.authored_path
            ),
        ));
    };
    Ok(DescriptorSortReference {
        key: reference.key.clone(),
        sort,
    })
}

fn resolve_application_reference(
    reference: &krs_ir::HostApplicationReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
    allow_builtin: bool,
) -> Result<DescriptorApplicationReference, CollectionError> {
    let identity = reference.target.resolve();
    let application = if let Some((id, kind)) = declarations.get(&identity) {
        if *kind != ItemKind::Constructor {
            return Err(CollectionError::new(
                CollectionErrorKind::ReferenceKindMismatch,
                format!(
                    "Rust path `{}` resolves to {kind:?} `{}`, but Constructor is required",
                    reference.target.authored_path(),
                    display_item(id)
                ),
            ));
        }
        DescriptorApplicationRef::Declared(id.clone())
    } else if allow_builtin {
        let HostApplicationIdentity::Nominal(type_id) = identity else {
            return Err(CollectionError::new(
                CollectionErrorKind::UnresolvedTypeReference,
                format!(
                    "enum-variant path `{}` has no selected constructor declaration",
                    reference.target.authored_path()
                ),
            ));
        };
        if let Some(operation) = builtins.and_then(|registry| registry.resolve_operation(type_id)) {
            DescriptorApplicationRef::Builtin(operation)
        } else if let Some(operation) =
            builtins.and_then(|registry| registry.resolve_map_operation(type_id))
        {
            DescriptorApplicationRef::Map(operation)
        } else if let Some(operation) =
            builtins.and_then(|registry| registry.resolve_list_operation(type_id))
        {
            DescriptorApplicationRef::List(operation)
        } else {
            return Err(CollectionError::new(
                CollectionErrorKind::UnresolvedTypeReference,
                format!(
                    "Rust path `{}` resolves to neither a selected constructor nor a registered term operation",
                    reference.target.authored_path()
                ),
            ));
        }
    } else {
        return Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{}` does not resolve to a selected constructor declaration",
                reference.target.authored_path()
            ),
        ));
    };
    Ok(DescriptorApplicationReference {
        key: reference.key.clone(),
        application,
    })
}

#[allow(clippy::too_many_lines)]
fn resolve_grammar(
    grammar: &HostGrammarDescriptor,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    context_aliases: &HashMap<HostItemId, StableItemId>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<GrammarDescriptor, CollectionError> {
    Ok(match grammar {
        HostGrammarDescriptor::Production(production) => {
            let owner = match &production.owner {
                HostProductionOwner::Constructor { constructor } => {
                    DescriptorProductionOwner::Constructor {
                        constructor: resolve_application_reference(
                            constructor,
                            declarations,
                            builtins,
                            false,
                        )?,
                    }
                }
                HostProductionOwner::TokenSort { sort } => DescriptorProductionOwner::TokenSort {
                    sort: resolve_sort_reference(sort, declarations, builtins)?,
                },
                HostProductionOwner::BracketSort { sort } => {
                    DescriptorProductionOwner::BracketSort {
                        sort: resolve_sort_reference(sort, declarations, builtins)?,
                    }
                }
            };
            let items = production
                .items
                .iter()
                .map(|item| {
                    Ok(match item {
                        HostProductionItem::Terminal { key, text } => {
                            DescriptorProductionItem::Terminal {
                                key: key.clone(),
                                text: text.clone(),
                            }
                        }
                        HostProductionItem::NonTerminal {
                            key,
                            field_key,
                            declaration_key,
                            field,
                            sort,
                        } => DescriptorProductionItem::NonTerminal {
                            key: key.clone(),
                            field_key: field_key.clone(),
                            declaration_key: declaration_key.clone(),
                            field: field.clone(),
                            sort: Box::new(resolve_sort_reference(sort, declarations, builtins)?),
                        },
                        HostProductionItem::RegexTerminal {
                            key,
                            precede_regex,
                            regex,
                            follow_regex,
                        } => DescriptorProductionItem::RegexTerminal {
                            key: key.clone(),
                            precede_regex: precede_regex.clone(),
                            regex: regex.clone(),
                            follow_regex: follow_regex.clone(),
                        },
                    })
                })
                .collect::<Result<Vec<_>, CollectionError>>()?;
            let attributes = production
                .attributes
                .iter()
                .map(|attribute| {
                    Ok(match attribute {
                        HostProductionAttribute::Documentation { key, text } => {
                            DescriptorProductionAttribute::Documentation {
                                key: key.clone(),
                                text: text.clone(),
                            }
                        }
                        HostProductionAttribute::Function { key } => {
                            DescriptorProductionAttribute::Function { key: key.clone() }
                        }
                        HostProductionAttribute::Total { key } => {
                            DescriptorProductionAttribute::Total { key: key.clone() }
                        }
                        HostProductionAttribute::Alias { key } => {
                            DescriptorProductionAttribute::Alias { key: key.clone() }
                        }
                        HostProductionAttribute::Token {
                            key,
                            lexical_precedence,
                        } => DescriptorProductionAttribute::Token {
                            key: key.clone(),
                            lexical_precedence: lexical_precedence.clone(),
                        },
                        HostProductionAttribute::Group { reference } => {
                            DescriptorProductionAttribute::Group {
                                reference: reference.clone(),
                            }
                        }
                        HostProductionAttribute::Bracket { key } => {
                            DescriptorProductionAttribute::Bracket { key: key.clone() }
                        }
                        HostProductionAttribute::Avoid { key } => {
                            DescriptorProductionAttribute::Avoid { key: key.clone() }
                        }
                        HostProductionAttribute::Format { key, fragments } => {
                            DescriptorProductionAttribute::Format {
                                key: key.clone(),
                                fragments: fragments.clone(),
                            }
                        }
                        HostProductionAttribute::Strictness {
                            key,
                            kind,
                            using,
                            fields,
                            result_sort,
                        } => DescriptorProductionAttribute::Strictness {
                            key: key.clone(),
                            kind: *kind,
                            using: using
                                .as_ref()
                                .map(|using| {
                                    let alias = context_aliases
                                        .get(&using.alias)
                                        .cloned()
                                        .ok_or_else(|| {
                                            CollectionError::new(
                                                CollectionErrorKind::UnresolvedTypeReference,
                                                format!(
                                                    "unknown context alias `{}`",
                                                    using.alias.item_name()
                                                ),
                                            )
                                        })?;
                                    Ok(krs_ir::DescriptorContextAliasReference {
                                        key: using.key.clone(),
                                        alias,
                                    })
                                })
                                .transpose()?,
                            fields: fields.clone(),
                            result_sort: Box::new(resolve_sort_reference(
                                result_sort,
                                declarations,
                                builtins,
                            )?),
                        },
                    })
                })
                .collect::<Result<Vec<_>, CollectionError>>()?;
            GrammarDescriptor::Production(DescriptorProduction {
                key: production.key.clone(),
                template_key: production.template_key.clone(),
                owner,
                result_sort: resolve_sort_reference(
                    &production.result_sort,
                    declarations,
                    builtins,
                )?,
                items,
                attributes,
            })
        }
        HostGrammarDescriptor::Subsort {
            key,
            subsort,
            supersort,
        } => GrammarDescriptor::Subsort {
            key: key.clone(),
            subsort: resolve_sort_reference(subsort, declarations, builtins)?,
            supersort: resolve_sort_reference(supersort, declarations, builtins)?,
        },
        HostGrammarDescriptor::Precedence { key, chains } => GrammarDescriptor::Precedence {
            key: key.clone(),
            chains: chains.clone(),
        },
        HostGrammarDescriptor::Associativity { key, sentences } => {
            GrammarDescriptor::Associativity {
                key: key.clone(),
                sentences: sentences.clone(),
            }
        }
    })
}

fn resolve_structured_rule(
    rule: &HostStructuredRuleDescriptor,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<StructuredRuleDescriptor, CollectionError> {
    Ok(StructuredRuleDescriptor {
        sentence_kind: rule.sentence_kind,
        label: rule.label.clone(),
        requires: rule
            .requires
            .as_ref()
            .map(|condition| {
                Ok(krs_ir::DescriptorRuleCondition {
                    key: condition.key.clone(),
                    term: resolve_term(&condition.term, declarations, builtins)?,
                })
            })
            .transpose()?,
        priority: rule.priority.clone(),
        simplification: rule.simplification.clone(),
        pattern_key: rule.pattern_key.clone(),
        result_key: rule.result_key.clone(),
        subject_sort: resolve_sort_reference(&rule.subject_sort, declarations, builtins)?,
        result_sort: resolve_sort_reference(&rule.result_sort, declarations, builtins)?,
        bindings: rule.bindings.clone(),
        subject: resolve_term(&rule.subject, declarations, builtins)?,
        result: resolve_term(&rule.result, declarations, builtins)?,
    })
}

fn resolve_term(
    term: &HostTerm,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<DescriptorTerm, CollectionError> {
    Ok(match term {
        HostTerm::Variable {
            key,
            path_key,
            name,
        } => DescriptorTerm::Variable {
            key: key.clone(),
            path_key: path_key.clone(),
            name: name.clone(),
        },
        HostTerm::Application {
            head_class,
            reference,
            path_key,
            arguments,
        } => DescriptorTerm::Application {
            head_class: *head_class,
            reference: resolve_application_reference(reference, declarations, builtins, true)?,
            path_key: path_key.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    Ok(match argument {
                        HostTermArgument::Positional { value } => {
                            DescriptorTermArgument::Positional {
                                value: Box::new(resolve_term(value, declarations, builtins)?),
                            }
                        }
                        HostTermArgument::Named { key, field, value } => {
                            DescriptorTermArgument::Named {
                                key: key.clone(),
                                field: field.clone(),
                                value: Box::new(resolve_term(value, declarations, builtins)?),
                            }
                        }
                    })
                })
                .collect::<Result<Vec<_>, CollectionError>>()?,
        },
        HostTerm::Literal { key, literal } => DescriptorTerm::Literal {
            key: key.clone(),
            literal: literal.clone(),
        },
        HostTerm::Wildcard { key } => DescriptorTerm::Wildcard { key: key.clone() },
        HostTerm::BuiltinToken { key, sort, value } => DescriptorTerm::BuiltinToken {
            key: key.clone(),
            sort: *sort,
            value: value.clone(),
        },
        HostTerm::Anonymous {
            key,
            sort,
            spelling,
        } => DescriptorTerm::Anonymous {
            key: key.clone(),
            sort: resolve_sort_reference(sort, declarations, builtins)?,
            spelling: spelling.clone(),
        },
        HostTerm::OrBool { key, arguments } => DescriptorTerm::OrBool {
            key: key.clone(),
            arguments: arguments
                .iter()
                .map(|argument| resolve_term(argument, declarations, builtins))
                .collect::<Result<Vec<_>, _>>()?,
        },
    })
}

fn materialize_descriptor_provenance(
    host: &HostDescriptor,
    payload: &HostDescriptorPayload,
    id: &StableItemId,
    context_index: usize,
    contexts: &[PreparedContext],
    source_cache: &mut BTreeMap<(usize, String), SourceDocument>,
) -> Result<
    (
        DescriptorProvenance,
        RustVisibility,
        Option<krs_ir::ExplicitSymbol>,
    ),
    CollectionError,
> {
    let primary = payload_primary_key(payload, id.item_kind())?;
    let (parsed, mut origins) = materialize_invocation(
        &host.provenance,
        &primary,
        id.item_name(),
        descriptor_label(id.item_kind()),
        id,
        matches!(payload, HostDescriptorPayload::Rule(_)),
        context_index,
        contexts,
        source_cache,
    )?;
    validate_reparsed_payload(payload, &parsed, id)?;

    if let HostDescriptorPayload::Configuration(configuration) = payload {
        let initializer_primary = ProvenanceRole::InitializerDeclaration
            .key(0)
            .map_err(|error| invalid_provenance_key(&error))?;
        let (initializer, initializer_origins) = materialize_invocation(
            &configuration.initializer.provenance,
            &initializer_primary,
            &configuration.initializer.name,
            "initializer",
            id,
            false,
            context_index,
            contexts,
            source_cache,
        )?;
        validate_reparsed_initializer(configuration, &initializer, id)?;
        origins.extend(initializer_origins);
    }

    let provenance = DescriptorProvenance::new(primary, origins).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::ProvenanceMismatch,
            format!(
                "invalid materialized provenance for `{}`: {error}",
                display_item(id)
            ),
        )
    })?;
    Ok((provenance, parsed.visibility, parsed.explicit_symbol))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn materialize_invocation(
    provenance: &HostProvenance,
    primary_key: &ProvenanceKey,
    expected_item_name: &str,
    label: &str,
    id: &StableItemId,
    legacy_catalog: bool,
    context_index: usize,
    contexts: &[PreparedContext],
    source_cache: &mut BTreeMap<(usize, String), SourceDocument>,
) -> Result<(ParsedInvocation, Vec<DescriptorNodeOrigin>), CollectionError> {
    let display_file = provenance.invocation().display_file();
    let relative = normalize_display_file(display_file)?;
    let cache_key = (context_index, relative.clone());
    if !source_cache.contains_key(&cache_key) {
        let document = load_source_document(&contexts[context_index], &relative)?;
        source_cache.insert(cache_key.clone(), document);
    }
    let invocation_document = source_cache.get(&cache_key).ok_or_else(|| {
        CollectionError::new(
            CollectionErrorKind::HostIo,
            "internal source cache insertion failed",
        )
    })?;
    let invocation_range = source_range(invocation_document, provenance.invocation())?;

    let mut authored_documents = BTreeMap::new();
    for authored in provenance.authored() {
        let authored_relative = normalize_display_file(authored.anchor().display_file())?;
        let authored_cache_key = (context_index, authored_relative.clone());
        if !source_cache.contains_key(&authored_cache_key) {
            let document = load_source_document(&contexts[context_index], &authored_relative)?;
            source_cache.insert(authored_cache_key.clone(), document);
        }
        authored_documents.insert(authored.key().clone(), authored_cache_key);
    }

    let mut materialized = BTreeMap::new();
    for authored in provenance.authored() {
        let authored_cache_key = authored_documents
            .get(authored.key())
            .expect("every authored key has a loaded document");
        let document = source_cache.get(authored_cache_key).ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::HostIo,
                "internal authored source cache insertion failed",
            )
        })?;
        materialized.insert(
            authored.key().clone(),
            source_range(document, authored.anchor())?,
        );
    }
    let primary_host = provenance
        .authored()
        .iter()
        .find(|anchor| anchor.key() == primary_key)
        .ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::ProvenanceMismatch,
                format!(
                    "descriptor `{}` lacks primary provenance key `{}`#{}",
                    display_item(id),
                    primary_key.role(),
                    primary_key.ordinal()
                ),
            )
        })?;
    let primary_coordinates = host_coordinates(primary_host.anchor());
    let primary_cache_key = authored_documents
        .get(primary_key)
        .expect("the primary authored key has a loaded document");
    let primary_document = source_cache.get(primary_cache_key).ok_or_else(|| {
        CollectionError::new(
            CollectionErrorKind::HostIo,
            "internal primary source cache insertion failed",
        )
    })?;
    let primary_candidates = primary_document
        .invocations
        .iter()
        .enumerate()
        .filter(|invocation| {
            let invocation = invocation.1;
            let anchors = if legacy_catalog {
                invocation
                    .legacy_anchors
                    .as_ref()
                    .unwrap_or(&invocation.anchors)
            } else {
                &invocation.anchors
            };
            (id.item_kind() == ItemKind::Grammar || invocation.item_name == expected_item_name)
                && &invocation.primary == primary_key
                && anchors.get(primary_key) == Some(&primary_coordinates)
        })
        .collect::<Vec<_>>();
    let (primary_invocation_index, invocation) = match primary_candidates.as_slice() {
        [] => {
            return Err(CollectionError::new(
                CollectionErrorKind::StaleAnchor,
                format!(
                    "primary anchor for `{}` does not match the reparsed `{}` source",
                    display_item(id),
                    relative
                ),
            ));
        }
        [invocation] => *invocation,
        _ => {
            return Err(CollectionError::new(
                CollectionErrorKind::AmbiguousAnchor,
                format!(
                    "primary anchor for `{}` matches multiple shared-parser invocations",
                    display_item(id)
                ),
            ));
        }
    };
    if id.item_kind() != ItemKind::Grammar && invocation.item_name != expected_item_name {
        return Err(CollectionError::new(
            CollectionErrorKind::StaleAnchor,
            format!(
                "reparsed item name `{}` does not match host identity `{}`",
                invocation.item_name, expected_item_name
            ),
        ));
    }
    let host_keys = provenance
        .authored()
        .iter()
        .map(|anchor| anchor.key().clone())
        .collect::<BTreeSet<_>>();
    let mut parser_keys = BTreeSet::new();
    let mut matched_invocations = BTreeSet::new();
    for authored in provenance.authored() {
        if authored.anchor().precision() != AnchorPrecision::Exact {
            return Err(CollectionError::new(
                CollectionErrorKind::ImpreciseAuthoredAnchor,
                format!(
                    "M1 provenance `{}`#{} for `{}` is not leaf-exact",
                    authored.key().role(),
                    authored.key().ordinal(),
                    display_item(id)
                ),
            ));
        }
        let authored_cache_key = authored_documents
            .get(authored.key())
            .expect("every authored key has a loaded document");
        let document = source_cache.get(authored_cache_key).ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::HostIo,
                "internal authored source cache lookup failed",
            )
        })?;
        let coordinates = host_coordinates(authored.anchor());
        let primary_anchors = if legacy_catalog {
            invocation
                .legacy_anchors
                .as_ref()
                .unwrap_or(&invocation.anchors)
        } else {
            &invocation.anchors
        };
        let candidate_hits = if authored_cache_key == primary_cache_key
            && primary_anchors.get(authored.key()) == Some(&coordinates)
        {
            vec![(primary_invocation_index, invocation)]
        } else {
            document
                .invocations
                .iter()
                .enumerate()
                .filter(|(_, candidate)| {
                    let anchors = if legacy_catalog {
                        candidate
                            .legacy_anchors
                            .as_ref()
                            .unwrap_or(&candidate.anchors)
                    } else {
                        &candidate.anchors
                    };
                    anchors.get(authored.key()) == Some(&coordinates)
                })
                .collect::<Vec<_>>()
        };
        let (invocation_index, parsed_invocation) = match candidate_hits.as_slice() {
            [] => {
                return Err(CollectionError::new(
                    CollectionErrorKind::StaleAnchor,
                    format!(
                        "anchor `{}`#{} for `{}` no longer matches reparsed source",
                        authored.key().role(),
                        authored.key().ordinal(),
                        display_item(id)
                    ),
                ));
            }
            [candidate] => *candidate,
            _ => {
                return Err(CollectionError::new(
                    CollectionErrorKind::AmbiguousAnchor,
                    format!(
                        "anchor `{}`#{} for `{}` matches multiple shared-parser invocations",
                        authored.key().role(),
                        authored.key().ordinal(),
                        display_item(id)
                    ),
                ));
            }
        };
        if matched_invocations.insert((authored_cache_key.clone(), invocation_index)) {
            let anchors = if legacy_catalog {
                parsed_invocation
                    .legacy_anchors
                    .as_ref()
                    .unwrap_or(&parsed_invocation.anchors)
            } else {
                &parsed_invocation.anchors
            };
            parser_keys.extend(anchors.keys().cloned());
        }
    }
    if host_keys != parser_keys {
        return Err(CollectionError::new(
            CollectionErrorKind::ProvenanceMismatch,
            format!(
                "macro and shared parser disagree about provenance keys for `{}`",
                display_item(id)
            ),
        ));
    }

    let origins = materialized
        .into_iter()
        .map(|(key, range)| {
            let mut origin = OriginStack::authored(range);
            origin.push(OriginFrame::Ranged {
                kind: RangedOriginKind::MacroInvocation,
                range: invocation_range.clone(),
                item: Some(id.clone()),
                label: Some(label.to_owned()),
            });
            origin.push(OriginFrame::Transformation {
                kind: TransformationOriginKind::GeneratedDescriptor,
                item: Some(id.clone()),
                label: Some(format!("{label}.{}#{}", key.role(), key.ordinal())),
            });
            DescriptorNodeOrigin::new(key, origin)
        })
        .collect();
    Ok((invocation.clone(), origins))
}

fn load_source_document(
    context: &PreparedContext,
    display_hint: &str,
) -> Result<SourceDocument, CollectionError> {
    let (canonical, package_relative) = resolve_display_source(context, display_hint)?;
    let bytes = fs::read(&canonical).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::HostIo,
            format!(
                "cannot read authored source `{}`: {error}",
                canonical.display()
            ),
        )
    })?;
    let text = String::from_utf8(bytes).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::SourceSyntax,
            format!("authored Rust source `{display_hint}` is not UTF-8: {error}"),
        )
    })?;
    let digest = Sha256::digest(text.as_bytes());
    let digest = Sha256Digest::new(format!("{digest:x}")).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::InvalidStableIdentity,
            format!("cannot construct source content identity: {error}"),
        )
    })?;
    let file =
        SourceFileId::new(context.package.clone(), &package_relative, digest).map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::InvalidDisplayFile,
                format!("invalid package-relative source `{package_relative}`: {error}"),
            )
        })?;
    let syntax = syn::parse_file(&text).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::SourceSyntax,
            format!("cannot parse authored Rust source `{display_hint}`: {error}"),
        )
    })?;
    validate_dsl_trivia(&syntax, &text)?;
    let mut invocations = Vec::new();
    collect_invocations(&syntax.items, &mut invocations)?;
    Ok(SourceDocument {
        text,
        file,
        invocations,
    })
}

struct DslTriviaVisitor<'source> {
    source: &'source str,
    error: Option<CollectionError>,
}

impl<'ast> Visit<'ast> for DslTriviaVisitor<'_> {
    fn visit_macro(&mut self, invocation: &'ast syn::Macro) {
        if self.error.is_some() {
            return;
        }
        let Some(name) = invocation
            .path
            .segments
            .last()
            .map(|segment| &segment.ident)
        else {
            return;
        };
        let result = match name.to_string().as_str() {
            "rules" => macro_body_source(self.source, invocation).and_then(|body| {
                parse_rule_block_source_with_trivia(body.source)
                    .map(|_| ())
                    .map_err(|error| source_syntax_at(error, body.byte_offset))
            }),
            "cells" => macro_body_source(self.source, invocation).and_then(validate_cells_trivia),
            "map" => macro_body_source(self.source, invocation).and_then(validate_map_trivia),
            _ => Ok(()),
        };
        if let Err(error) = result {
            self.error = Some(error);
            return;
        }
        syn::visit::visit_macro(self, invocation);
    }
}

fn validate_dsl_trivia(syntax: &syn::File, source: &str) -> Result<(), CollectionError> {
    let mut visitor = DslTriviaVisitor {
        source,
        error: None,
    };
    visitor.visit_file(syntax);
    visitor.error.map_or(Ok(()), Err)
}

#[derive(Clone, Copy)]
struct MacroBody<'source> {
    source: &'source str,
    byte_offset: usize,
}

fn validate_cells_trivia(body: MacroBody<'_>) -> Result<(), CollectionError> {
    let expression = parse_cells_expression_source_with_trivia(body.source);
    if expression.is_ok() {
        return Ok(());
    }
    let expression_error = expression.expect_err("the success case returned above");
    if matches!(
        expression_error.kind(),
        krs_syntax::SyntaxErrorKind::UnsupportedDslBlockComment { .. }
    ) {
        return Err(source_syntax_at(expression_error, body.byte_offset));
    }
    match parse_cells_pattern_source_with_trivia(body.source) {
        Err(error)
            if matches!(
                error.kind(),
                krs_syntax::SyntaxErrorKind::UnsupportedDslBlockComment { .. }
            ) =>
        {
            Err(source_syntax_at(error, body.byte_offset))
        }
        Ok(_) | Err(_) => Ok(()),
    }
}

fn validate_map_trivia(body: MacroBody<'_>) -> Result<(), CollectionError> {
    let expression = parse_map_expression_source_with_trivia(body.source);
    if expression.is_ok() {
        return Ok(());
    }
    let expression_error = expression.expect_err("the success case returned above");
    if matches!(
        expression_error.kind(),
        krs_syntax::SyntaxErrorKind::UnsupportedDslBlockComment { .. }
    ) {
        return Err(source_syntax_at(expression_error, body.byte_offset));
    }
    match parse_map_pattern_source_with_trivia(body.source) {
        Err(error)
            if matches!(
                error.kind(),
                krs_syntax::SyntaxErrorKind::UnsupportedDslBlockComment { .. }
            ) =>
        {
            Err(source_syntax_at(error, body.byte_offset))
        }
        Ok(_) | Err(_) => Ok(()),
    }
}

fn macro_body_source<'source>(
    source: &'source str,
    invocation: &syn::Macro,
) -> Result<MacroBody<'source>, CollectionError> {
    let start = invocation.delimiter.span().open().end();
    let end = invocation.delimiter.span().close().start();
    let start = position_to_byte(
        source,
        u32::try_from(start.line).map_err(|_| coordinate_overflow())?,
        u32::try_from(
            start
                .column
                .checked_add(1)
                .ok_or_else(coordinate_overflow)?,
        )
        .map_err(|_| coordinate_overflow())?,
    )?;
    let end = position_to_byte(
        source,
        u32::try_from(end.line).map_err(|_| coordinate_overflow())?,
        u32::try_from(end.column.checked_add(1).ok_or_else(coordinate_overflow)?)
            .map_err(|_| coordinate_overflow())?,
    )?;
    source
        .get(start..end)
        .map(|body| MacroBody {
            source: body,
            byte_offset: start,
        })
        .ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::SourcePositionOutOfBounds,
                "a DSL macro delimiter span is outside the exact authored source",
            )
        })
}

fn resolve_display_source(
    context: &PreparedContext,
    display_hint: &str,
) -> Result<(PathBuf, String), CollectionError> {
    let mut lexical_candidates = BTreeSet::new();
    let mut valid = BTreeSet::new();
    let mut outside = BTreeSet::new();
    for base in context.package_dir.ancestors() {
        let lexical = base.join(display_hint);
        if !lexical_candidates.insert(lexical.clone()) {
            continue;
        }
        let canonical = match fs::canonicalize(&lexical) {
            Ok(canonical) => canonical,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => {
                return Err(CollectionError::new(
                    CollectionErrorKind::HostIo,
                    format!(
                        "cannot canonicalize source candidate for display hint `{display_hint}`: {error}"
                    ),
                ));
            }
        };
        if !canonical.is_file() {
            continue;
        }
        if canonical.starts_with(&context.package_dir) {
            valid.insert(canonical);
        } else {
            outside.insert(canonical);
        }
    }

    let canonical = match valid.len() {
        0 if !outside.is_empty() => {
            return Err(CollectionError::new(
                CollectionErrorKind::SourceOutsidePackage,
                format!(
                    "display source `{display_hint}` resolves only outside selected package `{}`",
                    context.package.cargo_name()
                ),
            ));
        }
        0 => {
            return Err(CollectionError::new(
                CollectionErrorKind::HostIo,
                format!(
                    "display source `{display_hint}` does not resolve to an existing file in selected package `{}`",
                    context.package.cargo_name()
                ),
            ));
        }
        1 => valid.into_iter().next().ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::HostIo,
                "internal source candidate selection failed",
            )
        })?,
        count => {
            return Err(CollectionError::new(
                CollectionErrorKind::AmbiguousSourcePath,
                format!(
                    "display source `{display_hint}` resolves to {count} distinct files in selected package `{}`",
                    context.package.cargo_name()
                ),
            ));
        }
    };
    let relative = canonical
        .strip_prefix(&context.package_dir)
        .map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::SourceOutsidePackage,
                format!("resolved source escaped its selected package: {error}"),
            )
        })?;
    let relative = normalized_relative_path(relative)?;
    Ok((canonical, relative))
}

fn normalized_relative_path(path: &Path) -> Result<String, CollectionError> {
    let mut components = Vec::new();
    for component in path.components() {
        let Component::Normal(component) = component else {
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidDisplayFile,
                format!(
                    "resolved package source `{}` is not a normalized relative path",
                    path.display()
                ),
            ));
        };
        let component = component.to_str().ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::InvalidDisplayFile,
                "resolved package source path is not UTF-8",
            )
        })?;
        components.push(component);
    }
    if components.is_empty() {
        return Err(CollectionError::new(
            CollectionErrorKind::InvalidDisplayFile,
            "resolved package source path is empty",
        ));
    }
    Ok(components.join("/"))
}

#[allow(clippy::too_many_lines)]
fn collect_invocations(
    items: &[Item],
    output: &mut Vec<ParsedInvocation>,
) -> Result<(), CollectionError> {
    for item in items {
        match item {
            Item::Trait(item_trait) => {
                let (sort_visibility, sort_symbol) =
                    declaration_metadata(&item_trait.vis, &item_trait.attrs, "sort")?;
                for attribute in item_trait
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "sort"))
                {
                    let sort_attribute = parse_sort_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let declaration =
                        SortDeclaration::from_item(item_trait.clone()).map_err(source_syntax)?;
                    if sort_attribute.is_reference()
                        && sort_attribute.parents().len() != declaration.parents().len()
                    {
                        return Err(CollectionError::new(
                            CollectionErrorKind::SourceSyntax,
                            "a reference sort must materialize one semantic parent path for each Rust marker supertrait",
                        ));
                    }
                    let mut anchors = if let Some(alias) = sort_attribute.alias() {
                        let mut anchors = vec![ProvenanceAnchor::new(
                            ProvenanceRole::SortDeclaration,
                            0,
                            TokenRange::for_tokens(alias).map_err(source_syntax)?,
                        )];
                        for (ordinal, parent) in sort_attribute.parents().iter().enumerate() {
                            let ordinal = u32::try_from(ordinal).map_err(|_| {
                                CollectionError::new(
                                    CollectionErrorKind::SourceSyntax,
                                    "reference sort has too many semantic parents",
                                )
                            })?;
                            anchors.push(ProvenanceAnchor::new(
                                ProvenanceRole::SortParent,
                                ordinal,
                                TokenRange::for_tokens(parent).map_err(source_syntax)?,
                            ));
                        }
                        anchors
                    } else {
                        declaration.provenance().map_err(source_syntax)?
                    };
                    if let Some(symbol) = &sort_symbol {
                        anchors.extend(symbol.provenance().map_err(source_syntax)?);
                    }
                    output.push(with_declaration_metadata(
                        parsed_invocation(
                            ProvenanceRole::SortDeclaration,
                            sort_attribute
                                .alias()
                                .map_or_else(|| item_trait.ident.to_string(), ToString::to_string),
                            anchors,
                            ParsedInvocationPayload::Declaration,
                        )?,
                        sort_visibility.clone(),
                        sort_symbol.as_ref(),
                    ));
                }
                for attribute in item_trait
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "bracket"))
                {
                    let bracket = parse_bracket_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let sort_attribute = item_trait
                        .attrs
                        .iter()
                        .find(|candidate| attribute_named(candidate, "sort"))
                        .map(|candidate| {
                            parse_sort_attribute(attribute_tokens(candidate)?)
                                .map_err(source_syntax)
                        })
                        .transpose()?;
                    let semantic_name = sort_attribute.as_ref().map_or_else(
                        || item_trait.ident.to_string(),
                        |parsed| {
                            parsed
                                .alias()
                                .map_or_else(|| item_trait.ident.to_string(), ToString::to_string)
                        },
                    );
                    let mut anchors = bracket.provenance().map_err(source_syntax)?;
                    let semantic_anchor = sort_attribute
                        .as_ref()
                        .and_then(krs_syntax::SortAttribute::alias)
                        .map_or_else(
                            || TokenRange::for_tokens(&item_trait.ident),
                            TokenRange::for_tokens,
                        )
                        .map_err(source_syntax)?;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::SortDeclaration,
                        0,
                        semantic_anchor,
                    ));
                    output.push(parsed_invocation(
                        ProvenanceRole::BracketDeclaration,
                        semantic_name,
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
            }
            Item::Struct(item_struct) => {
                let (constructor_visibility, constructor_symbol) =
                    declaration_metadata(&item_struct.vis, &item_struct.attrs, "constructor")?;
                for attribute in item_struct
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "function"))
                {
                    let parsed = parse_function_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let declaration = ConstructorDeclaration::from_item(item_struct.clone())
                        .map_err(source_syntax)?;
                    parsed
                        .production()
                        .validate_declaration(&declaration)
                        .map_err(source_syntax)?;
                    let mut anchors = parsed.production().provenance().map_err(source_syntax)?;
                    anchors.extend(declaration.provenance().map_err(source_syntax)?);
                    let mut grammar_anchors = parsed.provenance().map_err(source_syntax)?;
                    grammar_anchors.extend(declaration.m3a_provenance().map_err(source_syntax)?);
                    if parsed.is_total() {
                        grammar_anchors.push(ProvenanceAnchor::new(
                            ProvenanceRole::FunctionDeclaration,
                            0,
                            TokenRange::for_tokens(&item_struct.ident).map_err(source_syntax)?,
                        ));
                    }
                    output.push(parsed_invocation(
                        ProvenanceRole::ConstructorSort,
                        item_struct.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                    output.push(parsed_invocation(
                        ProvenanceRole::ConstructorDeclaration,
                        item_struct.ident.to_string(),
                        grammar_anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for attribute in item_struct
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "constructor"))
                {
                    let parsed = parse_constructor_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let declaration = ConstructorDeclaration::from_item(item_struct.clone())
                        .map_err(source_syntax)?;
                    let mut anchors = parsed.provenance().map_err(source_syntax)?;
                    anchors.extend(declaration.provenance().map_err(source_syntax)?);
                    let mut grammar_anchors = parsed.m3a_provenance().map_err(source_syntax)?;
                    grammar_anchors.extend(declaration.m3a_provenance().map_err(source_syntax)?);
                    if let Some(symbol) = &constructor_symbol {
                        let symbol_anchors = symbol.provenance().map_err(source_syntax)?;
                        anchors.extend(symbol_anchors.clone());
                        grammar_anchors.extend(symbol_anchors);
                    }
                    for helper in item_struct
                        .attrs
                        .iter()
                        .filter(|attribute| attribute_named(attribute, "alias"))
                    {
                        parse_alias_attribute(attribute_tokens(helper)?).map_err(source_syntax)?;
                        let marker = helper
                            .path()
                            .segments
                            .last()
                            .expect("named attributes have a final path segment");
                        grammar_anchors.push(ProvenanceAnchor::new(
                            ProvenanceRole::AliasProduction,
                            0,
                            TokenRange::for_tokens(&marker.ident).map_err(source_syntax)?,
                        ));
                    }
                    for helper in item_struct
                        .attrs
                        .iter()
                        .filter(|attribute| attribute_named(attribute, "strict"))
                    {
                        grammar_anchors.extend(
                            parse_strict_attribute(attribute_tokens(helper)?)
                                .map_err(source_syntax)?
                                .provenance()
                                .map_err(source_syntax)?,
                        );
                    }
                    for helper in item_struct
                        .attrs
                        .iter()
                        .filter(|attribute| attribute_named(attribute, "seqstrict"))
                    {
                        grammar_anchors.extend(
                            parse_seqstrict_attribute(attribute_tokens(helper)?)
                                .map_err(source_syntax)?
                                .provenance()
                                .map_err(source_syntax)?,
                        );
                    }
                    output.push(with_declaration_metadata(
                        parsed_invocation(
                            ProvenanceRole::ConstructorSort,
                            item_struct.ident.to_string(),
                            anchors.clone(),
                            ParsedInvocationPayload::Declaration,
                        )?,
                        constructor_visibility.clone(),
                        constructor_symbol.as_ref(),
                    ));
                    output.push(with_declaration_metadata(
                        parsed_invocation(
                            ProvenanceRole::ConstructorDeclaration,
                            item_struct.ident.to_string(),
                            grammar_anchors,
                            ParsedInvocationPayload::Declaration,
                        )?,
                        constructor_visibility.clone(),
                        constructor_symbol.as_ref(),
                    ));
                }
                for attribute in item_struct
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "token"))
                {
                    let token_attribute = parse_token_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let token =
                        TokenDeclaration::from_item(item_struct.clone()).map_err(source_syntax)?;
                    let mut anchors = token_attribute.provenance().map_err(source_syntax)?;
                    anchors.extend(token.provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::SortDeclaration,
                        item_struct.ident.to_string(),
                        vec![ProvenanceAnchor::new(
                            ProvenanceRole::SortDeclaration,
                            0,
                            TokenRange::for_tokens(token.name()).map_err(source_syntax)?,
                        )],
                        ParsedInvocationPayload::Declaration,
                    )?);
                    output.push(parsed_invocation(
                        ProvenanceRole::TokenDeclaration,
                        item_struct.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for attribute in item_struct
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "configuration"))
                {
                    let parsed = parse_configuration_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let declaration = ConfigurationDeclaration::from_item(item_struct.clone())
                        .map_err(source_syntax)?;
                    let mut anchors = parsed.provenance().map_err(source_syntax)?;
                    anchors.extend(declaration.provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::ConfigurationDeclaration,
                        item_struct.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Configuration {
                            root: parsed
                                .optional_root()
                                .map_or_else(|| item_struct.ident.to_string(), syn::LitStr::value),
                            cell_name: declaration.cell().name().to_string(),
                        },
                    )?);
                }
                for _attribute in item_struct
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "cell"))
                {
                    let declaration = ConfigurationDeclaration::from_item(item_struct.clone())
                        .map_err(source_syntax)?;
                    output.push(parsed_invocation(
                        ProvenanceRole::ConfigurationDeclaration,
                        item_struct.ident.to_string(),
                        declaration.provenance().map_err(source_syntax)?,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
            }
            Item::Enum(item_enum)
                if item_enum
                    .attrs
                    .iter()
                    .any(|attribute| attribute_named(attribute, "constructors")) =>
            {
                let invoking = item_enum
                    .attrs
                    .iter()
                    .find(|attribute| attribute_named(attribute, "constructors"))
                    .expect("the match guard found a constructors attribute");
                let attribute = parse_constructors_attribute(attribute_tokens(invoking)?)
                    .map_err(source_syntax)?;
                let mut reparsed = item_enum.clone();
                reparsed
                    .attrs
                    .retain(|attribute| !attribute_named(attribute, "constructors"));
                let declaration = EnumConstructorDeclaration::from_parts(&attribute, reparsed)
                    .map_err(source_syntax)?;
                if !declaration.is_open_family() {
                    output.push(parsed_invocation(
                        ProvenanceRole::SortDeclaration,
                        declaration.sort_name().to_string(),
                        declaration.sort_provenance().map_err(source_syntax)?,
                        ParsedInvocationPayload::Declaration,
                    )?);
                    output.push(parsed_invocation(
                        ProvenanceRole::SubsortDeclaration,
                        declaration.sort_name().to_string(),
                        declaration.membership_provenance().map_err(source_syntax)?,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for variant in declaration.variants() {
                    let anchors = declaration
                        .variant_provenance(variant)
                        .map_err(source_syntax)?;
                    output.push(parsed_invocation(
                        ProvenanceRole::ConstructorSort,
                        variant.name().to_string(),
                        anchors.clone(),
                        ParsedInvocationPayload::Declaration,
                    )?);
                    output.push(parsed_invocation(
                        ProvenanceRole::ConstructorDeclaration,
                        variant.name().to_string(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                if let Some(anchors) = declaration.precedence_provenance().map_err(source_syntax)? {
                    output.push(parsed_invocation(
                        ProvenanceRole::PrecedenceDeclaration,
                        String::new(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                if let Some(anchors) = declaration
                    .associativity_provenance()
                    .map_err(source_syntax)?
                {
                    output.push(parsed_invocation(
                        ProvenanceRole::AssociativityDeclaration,
                        String::new(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
            }
            Item::Fn(item_fn) => {
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "claim"))
                {
                    let parsed = parse_claim_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let claim =
                        StateClaimItem::from_item(item_fn.clone()).map_err(source_syntax)?;
                    let mut anchors = claim.provenance().map_err(source_syntax)?;
                    anchors.extend(parsed.provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::ClaimDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "context_alias"))
                {
                    let parsed =
                        krs_syntax::parse_context_alias_attribute(attribute_tokens(attribute)?)
                            .map_err(source_syntax)?;
                    let alias = StateContextAliasItem::from_item(item_fn.clone(), parsed.here())
                        .map_err(source_syntax)?;
                    let mut anchors = parsed.provenance().map_err(source_syntax)?;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::ContextAliasDeclaration,
                        0,
                        TokenRange::for_tokens(&item_fn.sig.ident).map_err(source_syntax)?,
                    ));
                    anchors.extend(alias.provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::ContextAliasDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "simplification"))
                {
                    let parsed = parse_simplification_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let rule = RuleItem::from_item(item_fn.clone()).map_err(source_syntax)?;
                    let bindings = rule
                        .parameter()
                        .pattern
                        .bindings()
                        .iter()
                        .map(ToString::to_string)
                        .collect();
                    let references = rule
                        .reference_candidates()
                        .map_err(source_syntax)?
                        .into_iter()
                        .map(|candidate| (candidate.key().clone(), candidate.path_spelling()))
                        .collect();
                    let legacy_anchors =
                        parsed_anchor_map(rule.provenance().map_err(source_syntax)?)?;
                    let mut anchors = rule.m3a_provenance().map_err(source_syntax)?;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::SimplificationMarker,
                        0,
                        TokenRange::for_tokens(&item_fn.sig.ident).map_err(source_syntax)?,
                    ));
                    anchors.extend(parsed.provenance().map_err(source_syntax)?);
                    let mut invocation = parsed_invocation(
                        ProvenanceRole::RuleDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Rule {
                            bindings,
                            references,
                            lhs: rule.parameter().pattern.spelling(),
                            rhs: rule.result().spelling(),
                        },
                    )?;
                    invocation.legacy_anchors = Some(legacy_anchors);
                    output.push(invocation);
                }
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "equation"))
                {
                    parse_equation_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let rule = RuleItem::from_item(item_fn.clone()).map_err(source_syntax)?;
                    let bindings = rule
                        .parameter()
                        .pattern
                        .bindings()
                        .iter()
                        .map(ToString::to_string)
                        .collect();
                    let references = rule
                        .reference_candidates()
                        .map_err(source_syntax)?
                        .into_iter()
                        .map(|candidate| (candidate.key().clone(), candidate.path_spelling()))
                        .collect();
                    let legacy_anchors =
                        parsed_anchor_map(rule.provenance().map_err(source_syntax)?)?;
                    let mut anchors = rule.m3a_provenance().map_err(source_syntax)?;
                    for priority in item_fn
                        .attrs
                        .iter()
                        .filter(|attribute| attribute_named(attribute, "priority"))
                    {
                        anchors.extend(
                            parse_priority_attribute(attribute_tokens(priority)?)
                                .map_err(source_syntax)?
                                .provenance()
                                .map_err(source_syntax)?,
                        );
                    }
                    let mut invocation = parsed_invocation(
                        ProvenanceRole::RuleDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Rule {
                            bindings,
                            references,
                            lhs: rule.parameter().pattern.spelling(),
                            rhs: rule.result().spelling(),
                        },
                    )?;
                    invocation.legacy_anchors = Some(legacy_anchors);
                    output.push(invocation);
                }
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "alias"))
                {
                    parse_alias_attribute(attribute_tokens(attribute)?).map_err(source_syntax)?;
                    let rule = RuleItem::from_item(item_fn.clone()).map_err(source_syntax)?;
                    let bindings = rule
                        .parameter()
                        .pattern
                        .bindings()
                        .iter()
                        .map(ToString::to_string)
                        .collect();
                    let references = rule
                        .reference_candidates()
                        .map_err(source_syntax)?
                        .into_iter()
                        .map(|candidate| (candidate.key().clone(), candidate.path_spelling()))
                        .collect();
                    let legacy_anchors =
                        parsed_anchor_map(rule.provenance().map_err(source_syntax)?)?;
                    let mut anchors = rule.m3a_provenance().map_err(source_syntax)?;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::AliasClause,
                        0,
                        TokenRange::for_tokens(&item_fn.sig.ident).map_err(source_syntax)?,
                    ));
                    let mut invocation = parsed_invocation(
                        ProvenanceRole::RuleDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Rule {
                            bindings,
                            references,
                            lhs: rule.parameter().pattern.spelling(),
                            rhs: rule.result().spelling(),
                        },
                    )?;
                    invocation.legacy_anchors = Some(legacy_anchors);
                    output.push(invocation);
                }
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| attribute_named(attr, "rule"))
                {
                    let rule_attribute = parse_rule_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    if let Ok(rule) = StateRuleItem::from_item(item_fn.clone()) {
                        let mut anchors = rule.provenance().map_err(source_syntax)?;
                        anchors.extend(rule_attribute.provenance().map_err(source_syntax)?);
                        output.push(parsed_invocation(
                            ProvenanceRole::RuleDeclaration,
                            item_fn.sig.ident.to_string(),
                            anchors,
                            ParsedInvocationPayload::Declaration,
                        )?);
                        continue;
                    }
                    let rule = RuleItem::from_item(item_fn.clone()).map_err(source_syntax)?;
                    let bindings = rule
                        .parameter()
                        .pattern
                        .bindings()
                        .iter()
                        .map(ToString::to_string)
                        .collect();
                    let references = rule
                        .reference_candidates()
                        .map_err(source_syntax)?
                        .into_iter()
                        .map(|candidate| (candidate.key().clone(), candidate.path_spelling()))
                        .collect();
                    let legacy_anchors =
                        parsed_anchor_map(rule.provenance().map_err(source_syntax)?)?;
                    let mut anchors = rule.m3a_provenance().map_err(source_syntax)?;
                    anchors.extend(rule_attribute.provenance().map_err(source_syntax)?);
                    let mut invocation = parsed_invocation(
                        ProvenanceRole::RuleDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Rule {
                            bindings,
                            references,
                            lhs: rule.parameter().pattern.spelling(),
                            rhs: rule.result().spelling(),
                        },
                    )?;
                    invocation.legacy_anchors = Some(legacy_anchors);
                    output.push(invocation);
                }
            }
            Item::Impl(item_impl) => {
                for attribute in item_impl
                    .attrs
                    .iter()
                    .filter(|attribute| attribute_named(attribute, "subsort"))
                {
                    let mut reparsed_item = item_impl.clone();
                    reparsed_item
                        .attrs
                        .retain(|candidate| !attribute_named(candidate, "subsort"));
                    let declaration =
                        SubsortDeclaration::from_item(reparsed_item).map_err(source_syntax)?;
                    let tokens = attribute_tokens(attribute)?;
                    let anchors = if tokens.is_empty() {
                        declaration.provenance().map_err(source_syntax)?
                    } else {
                        let reference = parse_subsort_attribute(tokens).map_err(source_syntax)?;
                        vec![
                            ProvenanceAnchor::new(
                                ProvenanceRole::SubsortDeclaration,
                                0,
                                TokenRange::for_tokens(declaration.item())
                                    .map_err(source_syntax)?,
                            ),
                            ProvenanceAnchor::new(
                                ProvenanceRole::SubsortSuperSort,
                                0,
                                TokenRange::for_tokens(reference.sort()).map_err(source_syntax)?,
                            ),
                            ProvenanceAnchor::new(
                                ProvenanceRole::SubsortSubSort,
                                0,
                                TokenRange::for_tokens(declaration.sub_sort())
                                    .map_err(source_syntax)?,
                            ),
                        ]
                    };
                    output.push(parsed_invocation(
                        ProvenanceRole::SubsortDeclaration,
                        String::new(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for implementation_item in &item_impl.items {
                    let ImplItem::Fn(method) = implementation_item else {
                        continue;
                    };
                    for attribute in method
                        .attrs
                        .iter()
                        .filter(|attribute| attribute_named(attribute, "init"))
                    {
                        parse_init_attribute(attribute_tokens(attribute)?)
                            .map_err(source_syntax)?;
                        let mut method = method.clone();
                        method
                            .attrs
                            .retain(|attribute| !attribute_named(attribute, "init"));
                        let initializer =
                            InitializerFunction::from_item(method).map_err(source_syntax)?;
                        let references = initializer
                            .reference_candidates()
                            .map_err(source_syntax)?
                            .into_iter()
                            .filter(|candidate| {
                                matches!(
                                    candidate.key().role(),
                                    "configuration_variable_type" | "initializer_term_path"
                                )
                            })
                            .map(|candidate| (candidate.key().clone(), candidate.path_spelling()))
                            .collect();
                        let variable = initializer.variables().first().map(|variable| {
                            ParsedConfigurationVariable {
                                binding: variable.binding().to_string(),
                                external_name: variable.attribute().name().value(),
                                sort_key: ProvenanceRole::ConfigurationVariableType
                                    .key(0)
                                    .expect("the static provenance role is valid"),
                            }
                        });
                        output.push(parsed_invocation(
                            ProvenanceRole::InitializerDeclaration,
                            initializer.item().sig.ident.to_string(),
                            initializer.provenance().map_err(source_syntax)?,
                            ParsedInvocationPayload::Initializer {
                                term: initializer
                                    .legacy_cell()
                                    .map_or_else(String::new, |cell| cell.term().spelling()),
                                variable,
                                references,
                            },
                        )?);
                    }
                }
            }
            Item::Macro(item_macro)
                if item_macro
                    .mac
                    .path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.ident == "rules") =>
            {
                let block =
                    parse_rule_block(item_macro.mac.tokens.clone()).map_err(source_syntax)?;
                for clause in block.clauses() {
                    let rule = clause.rule();
                    let bindings = clause.bindings().iter().map(ToString::to_string).collect();
                    let extras = clause
                        .extras()
                        .iter()
                        .map(|extra| match extra {
                            krs_syntax::RuleExtra::HaveMap { cell, .. } => {
                                ("have".to_owned(), cell.to_string())
                            }
                            krs_syntax::RuleExtra::UpdateMap { cell, .. } => {
                                ("update".to_owned(), cell.to_string())
                            }
                            krs_syntax::RuleExtra::RewriteCell { cell, .. } => {
                                ("rewrite".to_owned(), cell.to_string())
                            }
                        })
                        .collect();
                    let mut anchors = clause.provenance().map_err(source_syntax)?;
                    anchors.extend(clause.attribute().provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::RuleDeclaration,
                        rule.item()
                            .sig
                            .ident
                            .to_string()
                            .trim_start_matches("r#")
                            .to_owned(),
                        anchors,
                        ParsedInvocationPayload::HeadRule {
                            bindings,
                            lhs: rule.parameter().pattern.spelling(),
                            result_kind: match clause.head_result() {
                                krs_syntax::RuleHeadResult::Replace(_) => "replace",
                                krs_syntax::RuleHeadResult::Splice { .. } => "splice",
                                krs_syntax::RuleHeadResult::Erase(_) => "erase",
                            }
                            .to_owned(),
                            extras,
                        },
                    )?);
                }
            }
            Item::Macro(item_macro)
                if item_macro
                    .mac
                    .path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.ident == "sorts") =>
            {
                let declaration = parse_sorts_declaration(item_macro.mac.tokens.clone())
                    .map_err(source_syntax)?;
                for entry in declaration.entries() {
                    match entry {
                        SortsEntry::Sort(sort) => {
                            output.push(with_visibility(
                                parsed_invocation(
                                    ProvenanceRole::SortDeclaration,
                                    sort.name().to_string(),
                                    sort.provenance().map_err(source_syntax)?,
                                    ParsedInvocationPayload::Declaration,
                                )?,
                                RustVisibility::Public,
                            ));
                            for bracket in sort.brackets() {
                                output.push(parsed_invocation(
                                    ProvenanceRole::BracketDeclaration,
                                    sort.name().to_string(),
                                    sort.bracket_provenance(bracket).map_err(source_syntax)?,
                                    ParsedInvocationPayload::Declaration,
                                )?);
                            }
                        }
                        SortsEntry::Membership(membership) => {
                            for member in membership.members() {
                                output.push(parsed_invocation(
                                    ProvenanceRole::SubsortDeclaration,
                                    String::new(),
                                    membership
                                        .member_provenance(member)
                                        .map_err(source_syntax)?,
                                    ParsedInvocationPayload::Declaration,
                                )?);
                            }
                        }
                    }
                }
            }
            Item::Macro(item_macro)
                if item_macro
                    .mac
                    .path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.ident == "precedence") =>
            {
                let declaration = parse_precedence_declaration(item_macro.mac.tokens.clone())
                    .map_err(source_syntax)?;
                output.push(parsed_invocation(
                    ProvenanceRole::PrecedenceDeclaration,
                    String::new(),
                    declaration.provenance().map_err(source_syntax)?,
                    ParsedInvocationPayload::Declaration,
                )?);
            }
            Item::Macro(item_macro)
                if item_macro
                    .mac
                    .path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.ident == "associativity") =>
            {
                let declaration = parse_associativity_declaration(item_macro.mac.tokens.clone())
                    .map_err(source_syntax)?;
                output.push(parsed_invocation(
                    ProvenanceRole::AssociativityDeclaration,
                    String::new(),
                    declaration.provenance().map_err(source_syntax)?,
                    ParsedInvocationPayload::Declaration,
                )?);
            }
            Item::Mod(module) => {
                if let Some((_, nested)) = &module.content {
                    collect_invocations(nested, output)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn with_visibility(
    mut invocation: ParsedInvocation,
    visibility: RustVisibility,
) -> ParsedInvocation {
    invocation.visibility = visibility;
    invocation
}

fn parsed_invocation(
    primary_role: ProvenanceRole,
    item_name: String,
    anchors: Vec<ProvenanceAnchor>,
    payload: ParsedInvocationPayload,
) -> Result<ParsedInvocation, CollectionError> {
    let primary = primary_role.key(0).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::SourceSyntax,
            format!("invalid shared-parser provenance key: {error}"),
        )
    })?;
    let parsed = parsed_anchor_map(anchors)?;
    Ok(ParsedInvocation {
        primary,
        item_name,
        anchors: parsed,
        legacy_anchors: None,
        payload,
        visibility: RustVisibility::Inherited,
        explicit_symbol: None,
    })
}

fn parsed_anchor_map(
    anchors: Vec<ProvenanceAnchor>,
) -> Result<BTreeMap<ProvenanceKey, Coordinates>, CollectionError> {
    let mut parsed = BTreeMap::new();
    for anchor in anchors {
        let key = anchor.key().map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::SourceSyntax,
                format!("invalid shared-parser provenance key: {error}"),
            )
        })?;
        let coordinates = token_coordinates(anchor.range())?;
        if parsed.insert(key.clone(), coordinates).is_some() {
            return Err(CollectionError::new(
                CollectionErrorKind::SourceSyntax,
                format!(
                    "shared parser repeated provenance key `{}`#{}",
                    key.role(),
                    key.ordinal()
                ),
            ));
        }
    }
    Ok(parsed)
}

#[allow(clippy::match_same_arms, clippy::too_many_lines)]
fn validate_reparsed_payload(
    payload: &HostDescriptorPayload,
    invocation: &ParsedInvocation,
    id: &StableItemId,
) -> Result<(), CollectionError> {
    match (payload, &invocation.payload) {
        (
            HostDescriptorPayload::Sort(_)
            | HostDescriptorPayload::Constructor(_)
            | HostDescriptorPayload::Grammar(_)
            | HostDescriptorPayload::Cell(_)
            | HostDescriptorPayload::ConfigurationRule(_)
            | HostDescriptorPayload::ContextAlias(_),
            ParsedInvocationPayload::Declaration,
        ) => Ok(()),
        (
            HostDescriptorPayload::FixedConfiguration(_),
            ParsedInvocationPayload::Configuration { .. },
        ) => Ok(()),
        (
            HostDescriptorPayload::HeadRule(rule),
            ParsedInvocationPayload::HeadRule {
                bindings,
                lhs,
                result_kind,
                extras,
            },
        ) => {
            let host_bindings = rule
                .bindings
                .iter()
                .map(|binding| binding.name.clone())
                .collect::<Vec<_>>();
            let host_extras = rule
                .extras
                .iter()
                .map(|extra| match extra {
                    krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, .. } => {
                        ("have".to_owned(), cell.name.clone())
                    }
                    krs_ir::ProtocolHeadRuleExtra::UpdateMap { cell, .. } => {
                        ("update".to_owned(), cell.name.clone())
                    }
                    krs_ir::ProtocolHeadRuleExtra::RewriteCell { cell, .. } => {
                        ("rewrite".to_owned(), cell.name.clone())
                    }
                })
                .collect::<Vec<_>>();
            let host_rhs = match &rule.result {
                krs_ir::ProtocolHeadRuleResult::Replace(_) => "replace",
                krs_ir::ProtocolHeadRuleResult::Splice(_) => "splice",
                krs_ir::ProtocolHeadRuleResult::Erase => "erase",
            };
            if host_bindings != *bindings
                || host_extras != *extras
                || host_rhs != result_kind
                || lhs.trim().is_empty()
            {
                return Err(provenance_mismatch(id, "head-anchored rule structure"));
            }
            Ok(())
        }
        (
            HostDescriptorPayload::Rule(rule),
            ParsedInvocationPayload::Rule {
                bindings,
                references,
                lhs,
                rhs,
            },
        ) => {
            if rule.parameters.len() != 1 || rule.parameters[0].bindings != *bindings {
                return Err(provenance_mismatch(id, "authored rule bindings"));
            }
            let host_parameter = canonical_term_spelling(&rule.parameters[0].pattern)?;
            let host_lhs = canonical_term_spelling(&rule.lhs)?;
            let host_rhs = canonical_term_spelling(&rule.rhs)?;
            let parsed_lhs = canonical_term_spelling(lhs)?;
            let parsed_rhs = canonical_term_spelling(rhs)?;
            if host_parameter != parsed_lhs || host_lhs != parsed_lhs || host_rhs != parsed_rhs {
                return Err(CollectionError::new(
                    CollectionErrorKind::ProvenanceMismatch,
                    format!(
                        "macro and shared parser disagree about rule spelling for `{}`: host parameter={:?}, host lhs={:?}, host rhs={:?}, parsed lhs={lhs:?}, parsed rhs={rhs:?}",
                        display_item(id),
                        rule.parameters[0].pattern,
                        rule.lhs,
                        rule.rhs,
                    ),
                ));
            }
            let host_references = rule
                .references
                .iter()
                .map(|reference| {
                    (
                        reference.key.clone(),
                        reference.target.authored_path.clone(),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            if references != &host_references {
                return Err(provenance_mismatch(id, "explicit rule references"));
            }
            Ok(())
        }
        (
            HostDescriptorPayload::StructuredRule(rule),
            ParsedInvocationPayload::Rule { bindings, .. },
        ) if rule.bindings == *bindings => Ok(()),
        (HostDescriptorPayload::StructuredRule(_), ParsedInvocationPayload::Rule { .. }) => {
            Err(provenance_mismatch(id, "authored structured-rule bindings"))
        }
        (
            HostDescriptorPayload::Configuration(configuration),
            ParsedInvocationPayload::Configuration { root, cell_name },
        ) if configuration.root == *root && configuration.cell.name == *cell_name => Ok(()),
        (
            HostDescriptorPayload::Configuration(_),
            ParsedInvocationPayload::Configuration { .. },
        ) => Err(provenance_mismatch(
            id,
            "configuration root or cell spelling",
        )),
        _ => Err(CollectionError::new(
            CollectionErrorKind::ProvenanceMismatch,
            format!(
                "reparsed source for `{}` has a different KRS declaration kind",
                display_item(id)
            ),
        )),
    }
}

fn validate_reparsed_initializer(
    configuration: &HostConfigurationDescriptor,
    invocation: &ParsedInvocation,
    id: &StableItemId,
) -> Result<(), CollectionError> {
    let ParsedInvocationPayload::Initializer {
        term,
        variable,
        references,
    } = &invocation.payload
    else {
        return Err(provenance_mismatch(id, "paired initializer declaration"));
    };
    let host_variable =
        configuration
            .main_variable
            .as_ref()
            .map(|variable| ParsedConfigurationVariable {
                binding: variable.binding.clone(),
                external_name: variable.external_name.clone(),
                sort_key: variable.sort.key.clone(),
            });
    if &host_variable != variable {
        return Err(provenance_mismatch(
            id,
            "main configuration variable metadata",
        ));
    }
    if canonical_term_spelling(&configuration.initializer.term)? != canonical_term_spelling(term)? {
        return Err(provenance_mismatch(id, "initializer term spelling"));
    }
    let host_references = configuration
        .main_variable
        .iter()
        .map(|variable| {
            (
                variable.sort.key.clone(),
                variable.sort.target.authored_path.clone(),
            )
        })
        .chain(
            configuration
                .initializer
                .references
                .iter()
                .map(|reference| {
                    (
                        reference.key.clone(),
                        reference.target.authored_path.clone(),
                    )
                }),
        )
        .collect::<BTreeMap<_, _>>();
    if references != &host_references {
        return Err(provenance_mismatch(id, "initializer semantic references"));
    }
    Ok(())
}

fn provenance_mismatch(id: &StableItemId, field: &str) -> CollectionError {
    CollectionError::new(
        CollectionErrorKind::ProvenanceMismatch,
        format!(
            "macro and shared parser disagree about {field} for `{}`",
            display_item(id)
        ),
    )
}

fn canonical_term_spelling(spelling: &str) -> Result<String, CollectionError> {
    parse_term_expression_source(spelling)
        .map(|term| term.spelling())
        .map_err(source_syntax)
}

fn attribute_tokens(attribute: &Attribute) -> Result<TokenStream, CollectionError> {
    match &attribute.meta {
        Meta::Path(_) => Ok(TokenStream::new()),
        Meta::List(list) => Ok(list.tokens.clone()),
        Meta::NameValue(_) => Err(CollectionError::new(
            CollectionErrorKind::SourceSyntax,
            format!(
                "KRS attribute `{}` must use path or list syntax",
                path_spelling(attribute.path())
            ),
        )),
    }
}

fn attribute_named(attribute: &Attribute, name: &str) -> bool {
    attribute
        .path()
        .segments
        .last()
        .is_some_and(|segment| segment.ident == name)
}

fn declaration_metadata(
    visibility: &syn::Visibility,
    attributes: &[Attribute],
    target_name: &str,
) -> Result<(RustVisibility, Option<krs_syntax::SymbolAttribute>), CollectionError> {
    let visibility = match visibility {
        syn::Visibility::Inherited => RustVisibility::Inherited,
        syn::Visibility::Public(_) => RustVisibility::Public,
        syn::Visibility::Restricted(restricted) => {
            let path = path_spelling(&restricted.path).replace(' ', "");
            RustVisibility::restricted(path, restricted.in_token.is_some()).map_err(|error| {
                CollectionError::new(
                    CollectionErrorKind::SourceSyntax,
                    format!("invalid Rust declaration visibility: {error}"),
                )
            })?
        }
    };
    let symbols = attributes
        .iter()
        .enumerate()
        .filter(|(_, attribute)| attribute_named(attribute, "symbol"))
        .collect::<Vec<_>>();
    let symbol = match symbols.as_slice() {
        [] => None,
        [(symbol_index, symbol)] => {
            let targets = attributes
                .iter()
                .enumerate()
                .filter(|(_, attribute)| attribute_named(attribute, target_name))
                .map(|(index, _)| index)
                .collect::<Vec<_>>();
            let [target_index] = targets.as_slice() else {
                return Err(CollectionError::new(
                    CollectionErrorKind::SourceSyntax,
                    format!(
                        "#[k::symbol] requires exactly one #[k::{target_name}] target on its declaration"
                    ),
                ));
            };
            if symbol_index.checked_add(1) != Some(*target_index) {
                return Err(CollectionError::new(
                    CollectionErrorKind::SourceSyntax,
                    format!(
                        "#[k::symbol] must immediately precede #[k::{target_name}] so attribute order is unambiguous"
                    ),
                ));
            }
            Some(parse_symbol_attribute(attribute_tokens(symbol)?).map_err(source_syntax)?)
        }
        _ => {
            return Err(CollectionError::new(
                CollectionErrorKind::SourceSyntax,
                "a declaration may carry only one #[k::symbol] attribute",
            ));
        }
    };
    Ok((visibility, symbol))
}

fn with_declaration_metadata(
    mut invocation: ParsedInvocation,
    visibility: RustVisibility,
    symbol: Option<&krs_syntax::SymbolAttribute>,
) -> ParsedInvocation {
    invocation.visibility = visibility;
    invocation.explicit_symbol = symbol.map(|symbol| symbol.value().clone());
    invocation
}

#[allow(clippy::needless_pass_by_value)]
fn source_syntax(error: krs_syntax::SyntaxError) -> CollectionError {
    source_syntax_at(error, 0)
}

#[allow(clippy::needless_pass_by_value)]
fn source_syntax_at(error: krs_syntax::SyntaxError, byte_offset: usize) -> CollectionError {
    let range = error.source_range().and_then(|range| {
        Some((
            byte_offset.checked_add(range.start())?,
            byte_offset.checked_add(range.end())?,
        ))
    });
    let detail = range.map_or_else(
        || format!("shared KRS source parser rejected authored source: {error}"),
        |(start, end)| {
            format!(
                "shared KRS source parser rejected authored source at bytes {start}..{end}: {error}"
            )
        },
    );
    CollectionError::new(CollectionErrorKind::SourceSyntax, detail)
}

fn token_coordinates(range: TokenRange) -> Result<Coordinates, CollectionError> {
    let start = range.start();
    let end = range.end();
    Ok(Coordinates {
        start_line: u32::try_from(start.line).map_err(|_| coordinate_overflow())?,
        start_column: u32::try_from(start.column + 1).map_err(|_| coordinate_overflow())?,
        end_line: u32::try_from(end.line).map_err(|_| coordinate_overflow())?,
        end_column: u32::try_from(end.column + 1).map_err(|_| coordinate_overflow())?,
    })
}

fn coordinate_overflow() -> CollectionError {
    CollectionError::new(
        CollectionErrorKind::SourcePositionOutOfBounds,
        "source coordinate exceeds protocol limits",
    )
}

fn host_coordinates(anchor: &HostSourceAnchor) -> Coordinates {
    Coordinates {
        start_line: anchor.start().line(),
        start_column: anchor.start().scalar_column(),
        end_line: anchor.end().line(),
        end_column: anchor.end().scalar_column(),
    }
}

fn source_range(
    document: &SourceDocument,
    anchor: &HostSourceAnchor,
) -> Result<SourceRange, CollectionError> {
    let start = position_to_byte(
        &document.text,
        anchor.start().line(),
        anchor.start().scalar_column(),
    )?;
    let end = position_to_byte(
        &document.text,
        anchor.end().line(),
        anchor.end().scalar_column(),
    )?;
    if start >= end {
        return Err(CollectionError::new(
            CollectionErrorKind::SourcePositionOutOfBounds,
            "materialized source anchor is empty or reversed",
        ));
    }
    SourceRange::new(
        document.file.clone(),
        u32::try_from(start).map_err(|_| coordinate_overflow())?,
        u32::try_from(end).map_err(|_| coordinate_overflow())?,
    )
    .map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::SourcePositionOutOfBounds,
            error.to_string(),
        )
    })
}

fn position_to_byte(text: &str, line: u32, scalar_column: u32) -> Result<usize, CollectionError> {
    let requested_line = usize::try_from(line).map_err(|_| coordinate_overflow())?;
    let requested_column = usize::try_from(scalar_column).map_err(|_| coordinate_overflow())?;
    let line_start = if requested_line == 1 {
        0
    } else {
        text.match_indices('\n')
            .nth(requested_line - 2)
            .map(|(offset, _)| offset + 1)
            .ok_or_else(|| {
                CollectionError::new(
                    CollectionErrorKind::SourcePositionOutOfBounds,
                    format!("source line {line} is outside the exact file revision"),
                )
            })?
    };
    let line_end = text[line_start..]
        .find('\n')
        .map_or(text.len(), |offset| line_start + offset);
    let line_text = &text[line_start..line_end];
    if requested_column == 0 {
        return Err(CollectionError::new(
            CollectionErrorKind::SourcePositionOutOfBounds,
            "source scalar columns are one-based",
        ));
    }
    if requested_column == 1 {
        return Ok(line_start);
    }
    line_text
        .char_indices()
        .nth(requested_column - 1)
        .map(|(offset, _)| line_start + offset)
        .or_else(|| {
            (requested_column == line_text.chars().count() + 1).then_some(line_end)
        })
        .ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::SourcePositionOutOfBounds,
                format!(
                    "source scalar column {scalar_column} is outside line {line} of the exact file revision"
                ),
            )
        })
}

fn payload_primary_key(
    payload: &HostDescriptorPayload,
    kind: ItemKind,
) -> Result<ProvenanceKey, CollectionError> {
    let role = match payload {
        HostDescriptorPayload::Grammar(grammar) => match grammar.as_ref() {
            HostGrammarDescriptor::Production(production) => match production.owner {
                HostProductionOwner::Constructor { .. } => ProvenanceRole::ConstructorDeclaration,
                HostProductionOwner::TokenSort { .. } => ProvenanceRole::TokenDeclaration,
                HostProductionOwner::BracketSort { .. } => ProvenanceRole::BracketDeclaration,
            },
            HostGrammarDescriptor::Subsort { .. } => ProvenanceRole::SubsortDeclaration,
            HostGrammarDescriptor::Precedence { .. } => ProvenanceRole::PrecedenceDeclaration,
            HostGrammarDescriptor::Associativity { .. } => ProvenanceRole::AssociativityDeclaration,
        },
        HostDescriptorPayload::StructuredRule(_) => ProvenanceRole::RuleDeclaration,
        _ => return primary_key(kind),
    };
    role.key(0).map_err(|error| invalid_provenance_key(&error))
}

fn primary_key(kind: ItemKind) -> Result<ProvenanceKey, CollectionError> {
    let role = match kind {
        ItemKind::Sort => ProvenanceRole::SortDeclaration,
        ItemKind::Constructor => ProvenanceRole::ConstructorSort,
        ItemKind::Configuration | ItemKind::Cell => ProvenanceRole::ConfigurationDeclaration,
        ItemKind::Rule | ItemKind::Equation | ItemKind::Simplification | ItemKind::Alias => {
            ProvenanceRole::RuleDeclaration
        }
        ItemKind::Claim => ProvenanceRole::ClaimDeclaration,
        ItemKind::ContextAlias => ProvenanceRole::ContextAliasDeclaration,
        ItemKind::Grammar => {
            return Err(CollectionError::new(
                CollectionErrorKind::ProvenanceMismatch,
                "grammar primary provenance depends on its typed payload",
            ));
        }
    };
    role.key(0).map_err(|error| invalid_provenance_key(&error))
}

fn invalid_provenance_key(error: &krs_ir::HostProvenanceError) -> CollectionError {
    CollectionError::new(
        CollectionErrorKind::ProvenanceMismatch,
        format!("cannot construct primary provenance key: {error}"),
    )
}

fn descriptor_label(kind: ItemKind) -> &'static str {
    match kind {
        ItemKind::Sort => "sort",
        ItemKind::Constructor => "constructor",
        ItemKind::Configuration => "configuration",
        ItemKind::Cell => "cell",
        ItemKind::Rule => "rule",
        ItemKind::Equation => "equation",
        ItemKind::Simplification => "simplification",
        ItemKind::Alias => "alias",
        ItemKind::ContextAlias => "context alias",
        ItemKind::Claim => "claim",
        ItemKind::Grammar => "grammar",
    }
}

fn normalize_display_file(display_file: &str) -> Result<String, CollectionError> {
    let normalized = display_file.replace('\\', "/");
    let path = Path::new(&normalized);
    if normalized.is_empty()
        || path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
        || normalized.split('/').any(str::is_empty)
    {
        return Err(CollectionError::new(
            CollectionErrorKind::InvalidDisplayFile,
            format!("display filename `{display_file}` is not normalized and package-relative"),
        ));
    }
    Ok(normalized)
}

fn canonicalize_path(path: &Path, role: &str) -> Result<PathBuf, CollectionError> {
    fs::canonicalize(path).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::HostIo,
            format!("cannot canonicalize {role} `{}`: {error}", path.display()),
        )
    })
}

fn is_rust_identifier(value: &str) -> bool {
    let mut characters = value.chars();
    characters
        .next()
        .is_some_and(|first| first == '_' || first.is_alphabetic())
        && characters.all(|character| character == '_' || character.is_alphanumeric())
}

fn display_item(id: &StableItemId) -> String {
    let module = if id.module_path().is_empty() {
        String::new()
    } else {
        format!("{}::", id.module_path().join("::"))
    };
    format!(
        "{}::{module}{}#{:?}",
        id.package().k_namespace(),
        id.item_name(),
        id.item_kind()
    )
}

fn path_spelling(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
}

#[cfg(test)]
mod protocol_v6_tests {
    use std::any::TypeId;

    use super::*;
    use krs_ir::{
        BuiltinSort, HostApplicationReference, HostApplicationTarget,
        HostBuiltinOperationRegistration, HostBuiltinSortRegistration, HostEnumVariantReference,
        HostListOperationRegistration, HostMapOperationRegistration, HostTypeKey, ListOperation,
        MapOperation,
    };

    struct Boolean;
    struct OtherBoolean;
    struct FalseMarker;
    struct SortK;
    struct SortInt;
    struct SortBool;
    struct SortMap;
    struct SortId;
    struct SortBytes;
    struct SortList;
    struct Op0;
    struct Op1;
    struct Op2;
    struct Op3;
    struct Op4;
    struct Op5;
    struct Op6;
    struct Op7;
    struct Op8;
    struct Op9;
    struct Op10;
    struct Op11;
    struct Op12;
    struct Op13;
    struct Op14;
    struct Op15;
    struct Op16;
    struct MapUpdateOp;
    struct ListOp0;
    struct ListOp1;
    struct ListOp2;
    struct ListOp3;
    struct ListOp4;
    struct ListOp5;

    fn marker_key<T: 'static>() -> TypeId {
        TypeId::of::<T>()
    }

    fn registry() -> HostBuiltinRegistry {
        let sort_keys = [
            HostTypeKey(marker_key::<SortK>),
            HostTypeKey(marker_key::<SortInt>),
            HostTypeKey(marker_key::<SortBool>),
            HostTypeKey(marker_key::<SortMap>),
            HostTypeKey(marker_key::<SortId>),
            HostTypeKey(marker_key::<SortBytes>),
            HostTypeKey(marker_key::<SortList>),
        ];
        let operation_keys = [
            HostTypeKey(marker_key::<Op0>),
            HostTypeKey(marker_key::<Op1>),
            HostTypeKey(marker_key::<Op2>),
            HostTypeKey(marker_key::<Op3>),
            HostTypeKey(marker_key::<Op4>),
            HostTypeKey(marker_key::<Op5>),
            HostTypeKey(marker_key::<Op6>),
            HostTypeKey(marker_key::<Op7>),
            HostTypeKey(marker_key::<Op8>),
            HostTypeKey(marker_key::<Op9>),
            HostTypeKey(marker_key::<Op10>),
            HostTypeKey(marker_key::<Op11>),
            HostTypeKey(marker_key::<Op12>),
            HostTypeKey(marker_key::<Op13>),
            HostTypeKey(marker_key::<Op14>),
            HostTypeKey(marker_key::<Op15>),
            HostTypeKey(marker_key::<Op16>),
        ];
        HostBuiltinRegistry {
            sorts: BuiltinSort::ALL
                .into_iter()
                .zip(sort_keys)
                .map(|(sort, target)| HostBuiltinSortRegistration { sort, target })
                .collect(),
            operations: krs_ir::BuiltinOperation::ALL
                .into_iter()
                .zip(operation_keys)
                .map(|(operation, target)| HostBuiltinOperationRegistration { operation, target })
                .collect(),
            map_operations: vec![HostMapOperationRegistration {
                operation: MapOperation::Update,
                target: HostTypeKey(marker_key::<MapUpdateOp>),
            }],
            list_operations: ListOperation::TERM_APPLICATIONS
                .into_iter()
                .zip([
                    HostTypeKey(marker_key::<ListOp0>),
                    HostTypeKey(marker_key::<ListOp1>),
                    HostTypeKey(marker_key::<ListOp2>),
                    HostTypeKey(marker_key::<ListOp3>),
                    HostTypeKey(marker_key::<ListOp4>),
                    HostTypeKey(marker_key::<ListOp5>),
                ])
                .map(|(operation, target)| HostListOperationRegistration { operation, target })
                .collect(),
        }
    }

    fn boolean_key() -> TypeId {
        TypeId::of::<Boolean>()
    }

    fn other_boolean_key() -> TypeId {
        TypeId::of::<OtherBoolean>()
    }

    fn false_key() -> TypeId {
        TypeId::of::<FalseMarker>()
    }

    fn test_id(name: &str) -> StableItemId {
        StableItemId::new(
            PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap(),
            ["model"],
            name,
            ItemKind::Constructor,
            "enum:Boolean",
        )
        .unwrap()
    }

    #[test]
    fn enum_variant_join_uses_owner_and_marker_identity_not_alias_spelling() {
        let false_id = test_id("False");
        let identity = HostApplicationIdentity::EnumVariant {
            enum_type: boolean_key(),
            variant: false_key(),
        };
        let declarations = HashMap::from([(identity, (false_id.clone(), ItemKind::Constructor))]);
        let target = HostEnumVariantReference::new(
            HostTypeReference {
                key: HostTypeKey(boolean_key),
                authored_path: "Alias".into(),
            },
            HostTypeKey(false_key),
            "Alias::RenamedFalse",
        )
        .unwrap();
        let resolved = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new("rule_right_reference", 0).unwrap(),
                target: HostApplicationTarget::EnumVariant(target),
            },
            &declarations,
            None,
            false,
        )
        .unwrap();
        assert_eq!(
            resolved.application,
            DescriptorApplicationRef::Declared(false_id)
        );

        let wrong_owner = HostEnumVariantReference::new(
            HostTypeReference {
                key: HostTypeKey(other_boolean_key),
                authored_path: "OtherAlias".into(),
            },
            HostTypeKey(false_key),
            "OtherAlias::RenamedFalse",
        )
        .unwrap();
        let error = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new("rule_right_reference", 0).unwrap(),
                target: HostApplicationTarget::EnumVariant(wrong_owner),
            },
            &declarations,
            None,
            false,
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::UnresolvedTypeReference);
    }

    #[test]
    fn complete_builtin_registry_joins_aliases_by_exact_type_identity() {
        let registry = registry();
        registry.validate().unwrap();
        let sort = resolve_sort_reference(
            &HostSortReference {
                key: ProvenanceKey::new("rule_type", 0).unwrap(),
                target: HostTypeReference {
                    key: HostTypeKey(marker_key::<SortInt>),
                    authored_path: "RenamedInt".into(),
                },
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap();
        assert_eq!(sort.sort, DescriptorSortRef::Builtin(BuiltinSort::Int));

        let bytes_sort = resolve_sort_reference(
            &HostSortReference {
                key: ProvenanceKey::new("rule_type", 1).unwrap(),
                target: HostTypeReference {
                    key: HostTypeKey(marker_key::<SortBytes>),
                    authored_path: "RenamedBytes".into(),
                },
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap();
        assert_eq!(
            bytes_sort.sort,
            DescriptorSortRef::Builtin(BuiltinSort::Bytes)
        );

        let application = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new("rule_right_application_head", 0).unwrap(),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: HostTypeKey(marker_key::<Op0>),
                    authored_path: "RenamedAdd".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap();
        assert_eq!(
            application.application,
            DescriptorApplicationRef::Builtin(krs_ir::BuiltinOperation::IntAdd)
        );

        let map_update = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new("rule_right_application_head", 0).unwrap(),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: HostTypeKey(marker_key::<MapUpdateOp>),
                    authored_path: "persistent_update".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap();
        assert_eq!(
            map_update.application,
            DescriptorApplicationRef::Map(MapOperation::Update)
        );

        let list_get = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new("rule_right_application_head", 1).unwrap(),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: HostTypeKey(marker_key::<ListOp3>),
                    authored_path: "indexed_lookup".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap();
        assert_eq!(
            list_get.application,
            DescriptorApplicationRef::List(ListOperation::Get)
        );

        let lookalike = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new("rule_right_application_head", 0).unwrap(),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: HostTypeKey(marker_key::<OtherBoolean>),
                    authored_path: "map::update".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap_err();
        assert_eq!(
            lookalike.kind(),
            CollectionErrorKind::UnresolvedTypeReference
        );
    }

    #[test]
    fn constructor_field_sort_preserves_builtin_identity_and_rejects_lookalikes() {
        let registry = registry();
        let builtin = resolve_constructor_field_sort(
            &HostTypeReference {
                key: HostTypeKey(marker_key::<SortId>),
                authored_path: "RenamedId".into(),
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap();
        assert_eq!(builtin, DescriptorSortRef::Builtin(BuiltinSort::Id));

        let error = resolve_constructor_field_sort(
            &HostTypeReference {
                key: HostTypeKey(marker_key::<OtherBoolean>),
                authored_path: "BuiltinLookingButUnregistered".into(),
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::UnresolvedTypeReference);
        assert!(
            error
                .to_string()
                .contains("neither a selected sort nor a registered builtin sort")
        );
    }

    #[test]
    fn protocol_v7_cell_items_use_the_configuration_declaration_lane() {
        assert_eq!(descriptor_label(ItemKind::Cell), "cell");
        assert_eq!(
            primary_key(ItemKind::Cell).unwrap(),
            ProvenanceRole::ConfigurationDeclaration.key(0).unwrap()
        );
    }
}
