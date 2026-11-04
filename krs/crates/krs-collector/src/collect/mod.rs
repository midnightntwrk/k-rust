use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use krs_ir::measure::Timings;
use krs_ir::{
    Descriptor, DescriptorBundle, DescriptorDeclaration, HostApplicationIdentity,
    HostBuiltinRegistry, HostDescriptor, HostItemId, HostProvenanceError, IntLiterals, ItemKind,
    PackageId, PackageSettings, RawKProfile, SchemaVersion, StableItemId,
};

use crate::facade::FacadeAliases;
use crate::{CollectionError, CollectionErrorKind};

use provenance::materialize_descriptor_provenance;
use resolve::{
    HostCellDeclarations, HostCellKinds, check_cell_kinds, declared_cell_field_table,
    declared_type_table, host_cell_kinds, resolve_head_rule_targets, resolve_payload_reading,
};
pub use run::run_collector;
use source::canonicalize_path;
pub(crate) use source::{record_file, record_probe};

mod cell_entries;
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

/// A collected bundle, and the warnings its collection reports: the lints of admitted entries
/// (a `cells!` entry with no effect, `krs::analysis::no-effect-entry`), which leave the bundle as
/// it is.
#[derive(Clone, Debug)]
pub(crate) struct Collected {
    pub(crate) bundle: DescriptorBundle,
    pub(crate) warnings: Vec<krs_diagnostic::Diagnostic>,
}

/// Resolves unordered current-protocol host descriptor factory results into one stable bundle.
///
/// Collection validates build-local `TypeId` producers and host paths, reparses authored nodes with `krs-syntax`, resolves references, and returns deterministically ordered, path-free data.
/// The bundle is all this returns: the warnings the collection reports are written by the
/// generated collector ([`run_collector`]), beside its bundle, for `krs` to report.
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
        .map(|collected| collected.bundle)
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
    collect_reported(contexts, descriptors, builtins, timings).map(|collected| collected.bundle)
}

/// [`collect_host_descriptors_with_builtins_timed`], with the warnings the collection reports.
pub(crate) fn collect_reported(
    contexts: impl IntoIterator<Item = PackageContext>,
    descriptors: impl IntoIterator<Item = Result<HostDescriptor, HostProvenanceError>>,
    builtins: &HostBuiltinRegistry,
    timings: &mut Timings,
) -> Result<Collected, CollectionError> {
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
) -> Result<Collected, CollectionError> {
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
        // The ownership check follows the lookup of the descriptor's package context, which
        // locating its error needs; a descriptor of a package outside the selection is no part
        // of the definition, so that error comes first whatever the descriptor's shape.
        // A payload that disagrees with its anchors is the expander's failure, not the
        // author's: both come from one expansion.
        let failure = host
            .validate_state_ownership()
            .map_err(|error| {
                (
                    CollectionErrorKind::InvalidConfiguration,
                    format!("invalid host configuration descriptor: {error}"),
                    error.at().cloned(),
                )
            })
            .and_then(|()| {
                host.validate_complete_provenance().map_err(|error| {
                    (
                        CollectionErrorKind::ProvenanceMismatch,
                        format!("host descriptor provenance disagrees with its payload: {error}"),
                        error.at().cloned(),
                    )
                })
            });
        if let Err((kind, message, at)) = failure {
            let error = CollectionError::new(kind, message);
            let error = match at {
                Some(key) => error.with_reference_key(key),
                None => error,
            };
            return Err(locate_at_host(error, &host, &id, context_index, contexts));
        }
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

/// `error`, about the host descriptor `host`, located at its item: the descriptor's provenance is
/// materialized for this one failure, so success costs nothing.
fn locate_at_host(
    error: CollectionError,
    host: &HostDescriptor,
    id: &StableItemId,
    context_index: usize,
    contexts: &[PreparedContext],
) -> CollectionError {
    match materialize_descriptor_provenance(
        host,
        &host.payload,
        id,
        context_index,
        contexts,
        &mut BTreeMap::new(),
    ) {
        Ok((provenance, ..)) => error.with_provenance(&provenance).with_item(id),
        Err(_) => error,
    }
}

/// Locates each configuration's main-cell refusal at that configuration's initializer, whose
/// descriptor holds the provenance: a rule that reports it is about another item.
fn locate_main_cell_refusals(
    targets: &mut [resolve::HeadRuleTarget],
    pending: &[PendingDescriptor],
    contexts: &[PreparedContext],
) {
    for target in targets {
        let Some(owner) = pending
            .iter()
            .find(|pending| &pending.id == target.configuration())
        else {
            continue;
        };
        target.locate_main_refusal(|error| {
            locate_at_host(error, &owner.host, &owner.id, owner.context_index, contexts)
        });
    }
}

/// The tables every descriptor's payload is resolved against.
struct ResolutionTables {
    context_aliases: HashMap<HostItemId, StableItemId>,
    declarations: HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: HashMap<resolve::HostCellKey, krs_ir::DescriptorCellIdentity>,
    head_targets: Vec<resolve::HeadRuleTarget>,
    /// Every declared cell's kind as the host declaration gives it, checked against the
    /// collected declaration once the bundle is resolved.
    cell_kinds: HostCellKinds,
    /// The provenance keys each configuration's neutral-leaf decision drops.
    dropped: resolve::DroppedKeys,
}

/// Sorts `pending` by final identity (K namespace order; host identities sort by Cargo package)
/// and builds the tables its payloads are resolved against.
fn resolution_tables(
    pending: &mut [PendingDescriptor],
    contexts: &[PreparedContext],
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<ResolutionTables, CollectionError> {
    pending.sort_by(|left, right| left.id.cmp(&right.id));
    let dropped =
        resolve::decide_neutral_leaves(pending, builtins).map_err(|(index, key, error)| {
            let owner = &pending[index];
            locate_at_host(
                error.with_reference_key(key),
                &owner.host,
                &owner.id,
                owner.context_index,
                contexts,
            )
        })?;
    let context_aliases = pending
        .iter()
        .filter(|pending| pending.id.item_kind() == ItemKind::ContextAlias)
        .map(|pending| (pending.host.id.clone(), pending.id.clone()))
        .collect::<HashMap<_, _>>();
    let declarations = declared_type_table(pending, builtins)?;
    let cell_fields = declared_cell_field_table(pending)?;
    let views = HostCellDeclarations::new(pending, builtins);
    let mut head_targets = resolve_head_rule_targets(pending, &cell_fields, &views)?;
    let cell_kinds = host_cell_kinds(pending, &views);
    locate_main_cell_refusals(&mut head_targets, pending, contexts);
    Ok(ResolutionTables {
        context_aliases,
        declarations,
        cell_fields,
        head_targets,
        cell_kinds,
        dropped,
    })
}

#[expect(
    clippy::too_many_lines,
    reason = "Each descriptor's provenance and payload are resolved in one ordered pass, and the bundle is judged once whole."
)]
fn resolve_pending_descriptors(
    mut pending: Vec<PendingDescriptor>,
    contexts: &[PreparedContext],
    builtins: Option<&HostBuiltinRegistry>,
    timings: &mut Timings,
) -> Result<Collected, CollectionError> {
    let ResolutionTables {
        context_aliases,
        declarations,
        cell_fields,
        head_targets,
        cell_kinds,
        dropped,
    } = timings.try_span("collector.resolve.tables", |_| {
        resolution_tables(&mut pending, contexts, builtins)
    })?;
    let mut source_cache = BTreeMap::new();
    let mut resolved = Vec::with_capacity(pending.len());
    let mut declaration_metadata = Vec::with_capacity(pending.len());
    let mut authored_cells = BTreeMap::new();
    // Provenance reparse and payload resolution interleave per descriptor, so
    // each is accumulated over the loop and recorded as one span.
    let mut provenance_seconds = 0.0;
    let mut payload_seconds = 0.0;
    let mut loop_failure = None;
    let mut readable_warnings = Vec::new();
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
        let (provenance, visibility, explicit_symbol, cells) = match provenance {
            Ok(value) => value,
            Err(error) => {
                loop_failure = Some(("collector.resolve.provenance", error));
                break;
            }
        };
        // A readable record clause's entries are judged before its payload is resolved; an
        // admitted clause's lints are its warnings.
        if let (Some(authored), krs_ir::HostDescriptorPayload::HeadRule(rule)) =
            (&cells, &pending.host.payload)
            && let Ok(target) = resolve::select_head_rule_target(rule, &head_targets, &declarations)
        {
            match cell_entries::judge_readable(&pending.id, target, authored) {
                Ok(lints) => readable_warnings.extend(lints),
                Err(error) => {
                    loop_failure = Some(("collector.resolve.payload", error));
                    break;
                }
            }
        }
        let started = timings.now();
        let payload = resolve_payload_reading(
            &pending.host.payload,
            &declarations,
            &cell_fields,
            &context_aliases,
            builtins,
            &head_targets,
        );
        payload_seconds += Timings::since(started);
        let (payload, provenance, misreads) = match payload.and_then(|mut resolved| {
            if let Some(keys) = dropped.get(&pending.id) {
                resolved.discarded.extend(keys.iter().cloned());
            }
            Ok((
                resolved.payload,
                kept_provenance(&provenance, &resolved.discarded)?,
                resolved.misreads_set_element,
            ))
        }) {
            Ok(value) => value,
            Err(error) => {
                // An error about another item (a configuration's refusal that a rule needing
                // its main cell reports) is located at that item already.
                let error = if error.source_range().is_some() {
                    error
                } else {
                    error.with_provenance(&provenance).with_item(&pending.id)
                };
                loop_failure = Some(("collector.resolve.payload", error));
                break;
            }
        };
        declaration_metadata.push(DescriptorDeclaration::new(
            pending.id.clone(),
            visibility,
            explicit_symbol,
        ));
        authored_cells.extend(cells.map(|cells| (pending.id.clone(), cells)));
        resolved.push((pending.id, pending.host.cfg, provenance, payload, misreads));
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
            .map(|(id, cfg, provenance, payload, misreads)| {
                Descriptor::new_located(id, cfg, provenance, payload)
                    .map_err(|failure| descriptor_contract_error(*failure, misreads))
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
        check_cell_kinds(&bundle, &cell_kinds)?;
        let mut warnings = readable_warnings;
        warnings.extend(cell_entries::judge(&bundle, &authored_cells)?);
        Ok(Collected { bundle, warnings })
    })
}

/// The provenance of a resolved descriptor: the anchors of a reading the
/// collector did not keep name no node of it.
fn kept_provenance(
    provenance: &krs_ir::DescriptorProvenance,
    discarded: &std::collections::BTreeSet<krs_ir::ProvenanceKey>,
) -> Result<krs_ir::DescriptorProvenance, CollectionError> {
    provenance.without(discarded).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::ProvenanceMismatch,
            format!(
                "the readings the collector discarded hold the descriptor's primary node: {error}"
            ),
        )
    })
}

/// The collection error of a descriptor that fails its contract, located at the innermost node
/// a term walk failed in, and at the descriptor's item otherwise.
///
/// The host stage reads an application whose path ends in `set::item` as a set's singleton, whose
/// element is computed and may hold a `let` block, a test or a record update; the descriptor stage
/// reads it by what it resolves to. Where the descriptor `misreads` such a path (it resolves to a
/// constructor) and its contract then refuses one of those constructs, the construct stands in a
/// constructor's field, which the pattern matches as it stands: that is the author's mistake, the
/// class the position table gives a construct at a matched position.
fn descriptor_contract_error(
    failure: krs_ir::DescriptorFailure,
    misreads: bool,
) -> CollectionError {
    let krs_ir::DescriptorFailure {
        error,
        at,
        provenance,
        id,
    } = failure;
    // A state contract that names its node locates the error there when no term walk did.
    let at = at.or_else(|| match &error {
        krs_ir::DescriptorError::State(error) => error.at().cloned(),
        _ => None,
    });
    let misread = misreads.then(|| misread_set_element(&error)).flatten();
    let (kind, message) = match error {
        _ if let Some(misread) = misread => misread,
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
    let error = CollectionError::new(kind, message);
    match at {
        Some(key) => error.with_reference_key(key),
        None => error,
    }
    .with_provenance(&provenance)
    .with_item(&id)
}

/// The author error of a construct the host stage admitted in a set's element whose path resolves
/// to a constructor ([`descriptor_contract_error`]), if `error` is its refusal.
fn misread_set_element(error: &krs_ir::DescriptorError) -> Option<(CollectionErrorKind, String)> {
    use krs_ir::transport::detail::{GrammarTermReason, StateTermReason};
    use krs_syntax::positions::Class;
    #[derive(Clone, Copy)]
    enum Refused {
        Let,
        Matches,
        RecordUpdate,
    }
    let refused = match error {
        krs_ir::DescriptorError::Grammar(krs_ir::GrammarTransportError::InvalidTerm(reason)) => {
            match reason {
                GrammarTermReason::LetInPattern => Refused::Let,
                GrammarTermReason::MatchesInPattern => Refused::Matches,
                GrammarTermReason::RecordUpdateBase => Refused::RecordUpdate,
                _ => return None,
            }
        }
        krs_ir::DescriptorError::State(krs_ir::StateTransportError::InvalidTerm(reason)) => {
            match reason {
                StateTermReason::LetInPattern => Refused::Let,
                StateTermReason::MatchesInPattern => Refused::Matches,
                StateTermReason::RecordUpdateBase => Refused::RecordUpdate,
                _ => return None,
            }
        }
        _ => return None,
    };
    let (kind, class) = match refused {
        Refused::Let => (
            CollectionErrorKind::LetInMatchedField,
            Class::LetOutsideTerm,
        ),
        Refused::Matches => (
            CollectionErrorKind::MatchesInMatchedField,
            Class::MatchesOutsideCondition,
        ),
        Refused::RecordUpdate => (
            CollectionErrorKind::RecordUpdateInMatchedField,
            Class::RecordUpdateInPattern,
        ),
    };
    Some((
        kind,
        format!(
            "{}; here it stands in a field of an application whose path ends in `set::item`, which the syntax reads as a set's singleton before names are resolved, and which resolves to a constructor of the program, whose field the pattern matches as it stands: spell the builtin singleton `k::builtin::set::item`, or give the constructor a path that does not end in `set::item`",
            class.summary()
        ),
    ))
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
