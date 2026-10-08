use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use krs_ir::measure::Timings;
use krs_ir::{
    Descriptor, DescriptorBundle, DescriptorDeclaration, HostBuiltinRegistry, HostDescriptor,
    HostItemId, HostProvenanceError, IntLiterals, ItemKind, PackageId, PackageSettings,
    RawKProfile, SchemaVersion, StableItemId,
};

use crate::facade::FacadeAliases;
use crate::{CollectionError, CollectionErrorKind};

use provenance::materialize_descriptor_provenance;
use resolve::{
    declared_cell_field_table, declared_type_table, resolve_head_rule_targets, resolve_payload,
};
pub use run::run_collector;
use source::canonicalize_path;
pub(crate) use source::{record_file, record_probe};

mod invocation;
mod provenance;
mod resolve;
mod run;
mod source;
mod trivia;

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
    int_literals: IntLiterals,
    allow_raw_k: bool,
    profile: RawKProfile,
}

impl PackageContext {
    /// Creates a caller-supplied package context without consulting Cargo.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid stable identity components, a non-absolute
    /// manifest path, or an invalid one-segment Rust crate-root name. Filesystem
    /// existence and symlink resolution are checked during collection.
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
            int_literals: IntLiterals::Signed,
            allow_raw_k: false,
            profile: RawKProfile::Standard,
        })
    }

    /// Sets the package's `allow-raw-k` and `profile` metadata, which decide
    /// whether its quoted hooks and `raw_k!` sentences are allowed.
    #[must_use]
    pub const fn with_raw_k(mut self, allow_raw_k: bool, profile: RawKProfile) -> Self {
        self.allow_raw_k = allow_raw_k;
        self.profile = profile;
        self
    }

    /// Sets the package's `int-literals` metadata, which selects the module
    /// supplying integer literals to its program-syntax module.
    #[must_use]
    pub const fn with_int_literals(mut self, int_literals: IntLiterals) -> Self {
        self.int_literals = int_literals;
        self
    }

    /// Returns the package's `allow-raw-k` and `profile` metadata.
    #[must_use]
    pub const fn raw_k(&self) -> (bool, RawKProfile) {
        (self.allow_raw_k, self.profile)
    }

    /// Returns the package's `int-literals` metadata.
    #[must_use]
    pub const fn int_literals(&self) -> IntLiterals {
        self.int_literals
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
    int_literals: IntLiterals,
    allow_raw_k: bool,
    profile: RawKProfile,
    crate_root: String,
    package_dir: PathBuf,
    facade: FacadeAliases,
}

#[derive(Debug)]
struct PendingDescriptor {
    host: HostDescriptor,
    id: StableItemId,
    context_index: usize,
}

/// Resolves unordered current-protocol host descriptor factory results into one stable bundle.
///
/// Collection validates build-local `TypeId` producers and host paths, reparses authored nodes with `krs-syntax`, resolves references, and returns deterministically ordered, path-free data.
///
/// # Errors
///
/// Returns a typed error for invalid package selection, protocol/identity disagreement, unresolved or wrongly-kinded Rust references, or source provenance that cannot be reproduced exactly.
/// Factory failures must be reported in their total error order, independently of registration order.
pub fn collect_host_descriptors(
    contexts: impl IntoIterator<Item = PackageContext>,
    descriptors: impl IntoIterator<Item = Result<HostDescriptor, HostProvenanceError>>,
) -> Result<DescriptorBundle, CollectionError> {
    collect_host_descriptors_impl(contexts, descriptors, None, &mut Timings::disabled())
}

/// Resolves host descriptor factory results with the complete compiler-provided builtin catalog.
///
/// Unlike [`collect_host_descriptors`], this entry point admits typed-grammar references to builtin sort and operation marker types.
/// The registry must be validated for exact completeness before any descriptor is inspected.
///
/// # Errors
///
/// Returns a typed collection error for an invalid builtin registry or any of
/// the descriptor, identity, reference, source, and provenance failures
/// documented by [`collect_host_descriptors`].
pub fn collect_host_descriptors_with_builtins(
    contexts: impl IntoIterator<Item = PackageContext>,
    descriptors: impl IntoIterator<Item = Result<HostDescriptor, HostProvenanceError>>,
    builtins: &HostBuiltinRegistry,
) -> Result<DescriptorBundle, CollectionError> {
    collect_host_descriptors_with_builtins_timed(
        contexts,
        descriptors,
        builtins,
        &mut Timings::disabled(),
    )
}

/// [`collect_host_descriptors_with_builtins`] recording its phases in
/// `timings` (`collector.resolve.*` ids; see [`krs_ir::measure`]).
///
/// # Errors
///
/// Fails exactly when [`collect_host_descriptors_with_builtins`] fails.
pub fn collect_host_descriptors_with_builtins_timed(
    contexts: impl IntoIterator<Item = PackageContext>,
    descriptors: impl IntoIterator<Item = Result<HostDescriptor, HostProvenanceError>>,
    builtins: &HostBuiltinRegistry,
    timings: &mut Timings,
) -> Result<DescriptorBundle, CollectionError> {
    timings.try_span("collector.resolve.builtins", |_| {
        builtins.validate().map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::InvalidBuiltinRegistry,
                format!("invalid builtin registry: {error}"),
            )
        })
    })?;
    collect_host_descriptors_impl(contexts, descriptors, Some(builtins), timings)
}

fn collect_host_descriptors_impl(
    contexts: impl IntoIterator<Item = PackageContext>,
    descriptors: impl IntoIterator<Item = Result<HostDescriptor, HostProvenanceError>>,
    builtins: Option<&HostBuiltinRegistry>,
    timings: &mut Timings,
) -> Result<DescriptorBundle, CollectionError> {
    let (contexts, pending) = timings.try_span("collector.resolve.intake", |_| {
        let results = descriptors.into_iter().collect::<Vec<_>>();
        if let Some(error) = results
            .iter()
            .filter_map(|result| result.as_ref().err())
            .min()
        {
            return Err(CollectionError::new(
                CollectionErrorKind::SourceOutsidePackage,
                error.to_string(),
            ));
        }
        let mut descriptors = results.into_iter().flatten().collect::<Vec<_>>();
        descriptors.sort_by(|left, right| left.id.cmp(&right.id));
        let mut contexts = contexts.into_iter().collect::<Vec<_>>();
        select_framework_context(&mut contexts, &descriptors)?;
        let (contexts, context_lookup) = prepare_contexts(contexts)?;
        let pending = collect_pending_descriptors(descriptors, &contexts, &context_lookup)?;
        Ok((contexts, pending))
    })?;
    resolve_pending_descriptors(pending, &contexts, builtins, timings)
}

fn select_framework_context(
    contexts: &mut Vec<PackageContext>,
    descriptors: &[HostDescriptor],
) -> Result<(), CollectionError> {
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
    Ok(())
}

fn collect_pending_descriptors(
    descriptors: Vec<HostDescriptor>,
    contexts: &[PreparedContext],
    context_lookup: &ContextLookup,
) -> Result<Vec<PendingDescriptor>, CollectionError> {
    let mut pending = Vec::new();
    let mut ids = BTreeSet::new();

    for host in descriptors {
        if host.protocol_version != SchemaVersion::CURRENT {
            return Err(CollectionError::new(
                CollectionErrorKind::UnsupportedSchemaVersion,
                format!(
                    "descriptor schema {} is unsupported; expected {}",
                    host.protocol_version.0,
                    SchemaVersion::CURRENT.0
                ),
            ));
        }
        validate_payload_item_kind(&host)?;
        host.validate_state_ownership().map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                format!("invalid host configuration descriptor: {error}"),
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
                format!("duplicate final item identity `{id}`"),
            ));
        }
        pending.push(PendingDescriptor {
            host,
            id,
            context_index,
        });
    }
    Ok(pending)
}

fn resolve_pending_descriptors(
    mut pending: Vec<PendingDescriptor>,
    contexts: &[PreparedContext],
    builtins: Option<&HostBuiltinRegistry>,
    timings: &mut Timings,
) -> Result<DescriptorBundle, CollectionError> {
    let (context_aliases, declarations, cell_fields, head_targets) =
        timings.try_span("collector.resolve.tables", |_| {
            // Final identities sort by K namespace; host identities sort by Cargo package.
            pending.sort_by(|left, right| left.id.cmp(&right.id));
            let context_aliases = pending
                .iter()
                .filter(|pending| pending.id.item_kind() == ItemKind::ContextAlias)
                .map(|pending| (pending.host.id.clone(), pending.id.clone()))
                .collect::<HashMap<_, _>>();
            let declarations = declared_type_table(&pending, builtins)?;
            let cell_fields = declared_cell_field_table(&pending)?;
            let head_targets = resolve_head_rule_targets(&pending, &cell_fields)?;
            Ok::<_, CollectionError>((context_aliases, declarations, cell_fields, head_targets))
        })?;
    let mut source_cache = BTreeMap::new();
    let mut resolved = Vec::with_capacity(pending.len());
    let mut declaration_metadata = Vec::with_capacity(pending.len());
    // Provenance reparse and payload resolution interleave per descriptor, so
    // each is accumulated over the loop and recorded as one span.
    let mut provenance_seconds = 0.0;
    let mut payload_seconds = 0.0;
    let mut loop_failure = None;
    for pending in pending {
        let started = timings.now();
        let provenance = materialize_descriptor_provenance(
            &pending.host,
            &pending.host.payload,
            &pending.id,
            pending.context_index,
            contexts,
            &mut source_cache,
        );
        provenance_seconds += Timings::since(started);
        let (provenance, visibility, explicit_symbol) = match provenance {
            Ok(value) => value,
            Err(error) => {
                loop_failure = Some(("collector.resolve.provenance", error));
                break;
            }
        };
        let started = timings.now();
        let payload = resolve_payload(
            &pending.host.payload,
            &declarations,
            &cell_fields,
            &context_aliases,
            builtins,
            &head_targets,
        );
        payload_seconds += Timings::since(started);
        let payload = match payload {
            Ok(value) => value,
            Err(error) => {
                let error = error.with_provenance(&provenance);
                loop_failure = Some(("collector.resolve.payload", error));
                break;
            }
        };
        declaration_metadata.push(DescriptorDeclaration::new(
            pending.id.clone(),
            visibility,
            explicit_symbol,
        ));
        resolved.push((pending.id, pending.host.cfg, provenance, payload));
    }
    timings.record("collector.resolve.provenance", provenance_seconds, 0);
    timings.record("collector.resolve.payload", payload_seconds, 0);
    if let Some((span, error)) = loop_failure {
        timings.mark_failed(span);
        return Err(error);
    }
    timings.try_span("collector.resolve.bundle", |_| {
        resolved.sort();
        let resolved = resolved
            .into_iter()
            .map(|(id, cfg, provenance, payload)| {
                Descriptor::new(id, cfg, provenance, payload).map_err(descriptor_contract_error)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let settings = contexts.iter().map(|context| PackageSettings {
            package: context.package.clone(),
            int_literals: context.int_literals,
            allow_raw_k: context.allow_raw_k,
            profile: context.profile,
        });
        let bundle = DescriptorBundle::with_declarations(resolved, declaration_metadata)
            .and_then(|bundle| bundle.with_package_settings(settings))
            .map_err(|error| {
                CollectionError::new(
                    CollectionErrorKind::InvalidStableIdentity,
                    format!("invalid declaration metadata coverage: {error}"),
                )
            })?;
        Ok(bundle)
    })
}

fn descriptor_contract_error(error: krs_ir::DescriptorError) -> CollectionError {
    let (kind, message) = match error {
        krs_ir::DescriptorError::Grammar(error) => (
            CollectionErrorKind::ProvenanceMismatch,
            format!("invalid stable grammar descriptor: {error}"),
        ),
        krs_ir::DescriptorError::State(error) => (
            CollectionErrorKind::ProvenanceMismatch,
            format!("invalid stable configuration descriptor: {error}"),
        ),
        error @ krs_ir::DescriptorError::WrongKind { .. } => (
            CollectionErrorKind::InvalidStableIdentity,
            error.to_string(),
        ),
    };
    CollectionError::new(kind, message)
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
        record_probe(&context.manifest_path);
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
            int_literals: context.int_literals,
            allow_raw_k: context.allow_raw_k,
            profile: context.profile,
            crate_root: context.crate_root,
            package_dir: package_dir.to_owned(),
            facade: FacadeAliases::from_manifest(&manifest)?,
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
    let expected = host.payload.item_kind();
    if host.id.item_kind() != expected {
        return Err(CollectionError::new(
            CollectionErrorKind::ItemKindMismatch,
            format!(
                "host item `{}` declares kind {} but its payload requires {expected}",
                host.id.item_name(),
                host.id.item_kind()
            ),
        ));
    }
    Ok(())
}

fn is_rust_identifier(value: &str) -> bool {
    let mut characters = value.chars();
    characters
        .next()
        .is_some_and(|first| first == '_' || first.is_alphabetic())
        && characters.all(|character| character == '_' || character.is_alphanumeric())
}
