use crate::metadata::{CargoMetadata, MetadataNode, MetadataPackage, MetadataTarget};
use krs_collector::PackageContext;
use krs_diagnostic::{Diagnostic, Location, ToDiagnostic, codes};
use krs_syntax::keyword;
use serde::Serialize;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};

/// An exact Cargo package selector or a convenient, ambiguity-checked name.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub enum PackageSelector {
    /// Cargo's exact package ID from the same metadata snapshot.
    Id(String),
    /// A package name, accepted only when it identifies exactly one package.
    Name(String),
}

/// An explicitly selected definition facet in a Cargo package.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct FacetSelector {
    /// Package containing the facet.
    pub package: PackageSelector,
    /// Key below `package.metadata.krs.definitions`.
    pub definition: String,
}

/// One rustc cfg passed to the selected semantics graph.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct KrsCfg {
    /// Rust cfg predicate name.
    pub key: String,
    /// Optional string value, such as `llvm` in `k_backend = "llvm"`.
    pub value: Option<String>,
}

/// The generated program's single collector function.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollectorEntrypoint {
    /// Cargo package exporting the collector function.
    pub package: PackageSelector,
    /// Rust path below that package's generated dependency alias.
    ///
    /// For example, `vec!["collector".into(), "collect".into()]` generates
    /// `runtime_alias::collector::collect(...)`.
    pub function: Vec<String>,
}

/// Complete, explicit input to collector planning.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollectorRequest {
    /// Root definition facet.
    pub root: FacetSelector,
    /// Dependency-only facets composed into the definition.
    pub dependencies: Vec<FacetSelector>,
    /// Runtime package and function called exactly once by generated `main`.
    pub entrypoint: CollectorEntrypoint,
    /// Host target triple used even when the eventual K target differs.
    pub host_target: String,
    /// KRS-owned rustc cfg predicates, applied to the entire Cargo graph.
    pub cfg: Vec<KrsCfg>,
}

/// Complete input to production collector planning.
///
/// Unlike [`CollectorRequest`], this request has no author-supplied runtime
/// entry point. The generated package owns collection and invokes the KRS host
/// and compiler APIs directly.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionRequest {
    /// Root definition facet.
    pub root: FacetSelector,
    /// Dependency-only facets composed into the definition.
    pub dependencies: Vec<FacetSelector>,
    /// Host target triple used to execute the collector.
    pub host_target: String,
    /// KRS-owned rustc cfg predicates applied to the selected graph.
    pub cfg: Vec<KrsCfg>,
}

/// Manifests for the collector's KRS runtime dependencies.
///
/// These paths are build-only inputs and are never included in the stable
/// descriptor protocol or canonical selection document.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollectorRuntime {
    /// Manifest of the author-facing `krs` host crate.
    pub host_manifest: PathBuf,
    /// Manifest of the `krs-collector` crate.
    pub collector_manifest: PathBuf,
}

/// How the generated production collector enumerates host descriptors.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum RegistrationMode {
    /// Linker-section registration through the `krs` `inventory` feature.
    #[default]
    Inventory,
    /// Generated crate-root `__KRS_REGISTRATIONS` tables, one per semantics
    /// package, with the `krs` `inventory` feature disabled.
    Explicit,
}

/// A selected and validated KRS definition facet.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedFacet {
    /// Whether this is the selected root facet rather than a composed dependency facet.
    pub is_root: bool,
    /// Immutable semantic namespace from `package.metadata.krs.k-namespace`.
    pub k_namespace: String,
    /// Cargo package name.
    pub package_name: String,
    /// Cargo package version.
    pub package_version: String,
    /// Path-free logical Cargo source identity.
    pub cargo_source: String,
    /// Definition facet name.
    pub definition: String,
    /// Rust module subtree selected by this facet.
    pub root: String,
    /// Effective program-syntax module subtree, defaulting to the whole crate.
    pub syntax_root: String,
    /// Generated Cargo dependency alias.
    pub dependency_alias: String,
    /// Cargo's actual selected library target and `module_path!()` crate root.
    pub crate_root: String,
    pub(crate) cargo_package_id: String,
    pub(crate) manifest_path: PathBuf,
}

/// One package in the root package's resolved Cargo closure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedPackage {
    /// Cargo package name.
    pub name: String,
    /// Cargo package version.
    pub version: String,
    /// Path-free logical Cargo source identity.
    pub cargo_source: String,
    /// Activated Cargo feature names.
    pub features: BTreeSet<String>,
    /// Whether this package contributes an explicitly selected semantics facet.
    pub semantics: bool,
    pub(crate) cargo_package_id: String,
    pub(crate) manifest_path: PathBuf,
    pub(crate) dependency_ids: BTreeSet<String>,
}

/// A deterministic, validated collector build plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollectorPlan {
    /// Root facet followed by dependency facets in canonical order.
    facets: Vec<ResolvedFacet>,
    /// Root package dependency closure in deterministic dependency order.
    package_closure: Vec<ResolvedPackage>,
    /// Host target triple.
    host_target: String,
    /// KRS cfg inputs.
    cfg: BTreeSet<KrsCfg>,
    pub(crate) dependencies: Vec<GeneratedDependency>,
    pub(crate) kind: CollectorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CollectorKind {
    EntryPoint {
        alias: EntryAlias,
        function: Vec<String>,
    },
    Production {
        runtime: CollectorRuntime,
        registration: RegistrationMode,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EntryAlias(String);

impl EntryAlias {
    fn new(alias: String) -> Result<Self, PlanningError> {
        if !valid_identifier_segment(&alias) {
            return Err(PlanningError::new(
                PlanningErrorKind::InvalidEntrypoint,
                "collector entry package has an invalid generated alias",
            ));
        }
        Ok(Self(alias))
    }

    pub(crate) fn as_str(&self) -> &str {
        &self.0
    }
}

struct ResolvedSelection {
    facets: Vec<ResolvedFacet>,
    package_closure: Vec<ResolvedPackage>,
    host_target: String,
    cfg: BTreeSet<KrsCfg>,
    dependencies: Vec<GeneratedDependency>,
    extra_alias: Option<String>,
}

impl ResolvedSelection {
    fn into_plan(self, kind: CollectorKind) -> CollectorPlan {
        CollectorPlan {
            facets: self.facets,
            package_closure: self.package_closure,
            host_target: self.host_target,
            cfg: self.cfg,
            dependencies: self.dependencies,
            kind,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct GeneratedDependency {
    pub alias: String,
    pub package_name: String,
    pub manifest_path: PathBuf,
    pub features: BTreeSet<String>,
    pub semantics: bool,
}

impl CollectorPlan {
    /// Validate and resolve a request against one Cargo metadata snapshot.
    ///
    /// # Errors
    ///
    /// Returns a typed [`PlanningError`] for incomplete or inconsistent Cargo
    /// metadata, missing or ambiguous selections, invalid facet metadata,
    /// unreachable dependency selections, or unsafe host/cfg/function inputs.
    pub fn resolve(
        metadata: &CargoMetadata,
        request: &CollectorRequest,
    ) -> Result<Self, PlanningError> {
        validate_rust_path(&request.entrypoint.function)?;
        let selection = Self::resolve_selection(
            metadata,
            &request.root,
            &request.dependencies,
            &request.host_target,
            &request.cfg,
            Some(&request.entrypoint.package),
        )?;
        let alias = selection.extra_alias.clone().ok_or_else(|| {
            PlanningError::new(
                PlanningErrorKind::InvalidEntrypoint,
                "collector entry package has no generated alias",
            )
        })?;
        let alias = EntryAlias::new(alias)?;
        let plan = selection.into_plan(CollectorKind::EntryPoint {
            alias,
            function: request.entrypoint.function.clone(),
        });
        plan.package_contexts()?;
        Ok(plan)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Selection resolution validates and joins the complete Cargo package and facet graph."
    )]
    fn resolve_selection(
        metadata: &CargoMetadata,
        root: &FacetSelector,
        dependencies: &[FacetSelector],
        host_target: &str,
        cfg: &[KrsCfg],
        extra_direct_package: Option<&PackageSelector>,
    ) -> Result<ResolvedSelection, PlanningError> {
        validate_host_target(host_target)?;
        validate_cfg(cfg)?;

        let packages = package_map(metadata)?;
        let nodes = node_map(metadata, &packages)?;
        let workspace_members = metadata
            .workspace_members
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let root_package = select_package(metadata, &root.package)?;
        let reachable = reachable_packages(&root_package.id, &nodes)?;

        let mut selections = Vec::with_capacity(1 + dependencies.len());
        selections.push((root, true));
        selections.extend(dependencies.iter().map(|selection| (selection, false)));

        let mut facet_records = Vec::new();
        for (selection, is_root) in selections {
            let package = select_package(metadata, &selection.package)?;
            if !reachable.contains(&package.id) {
                return Err(PlanningError::new(
                    PlanningErrorKind::UnreachableSelection,
                    format!(
                        "selected package `{}` is not in root package `{}`'s resolved dependency closure",
                        package.name, root_package.name
                    ),
                ));
            }
            facet_records.push(resolve_facet(package, &selection.definition, is_root)?);
        }

        facet_records.sort_by(|left, right| left.sort_key().cmp(&right.sort_key()));
        facet_records.dedup_by(|left, right| {
            left.package.id == right.package.id && left.definition == right.definition
        });
        ensure_unique_namespaces(&facet_records)?;

        let extra_package = extra_direct_package
            .map(|selector| select_package(metadata, selector))
            .transpose()?;
        if let Some(package) = extra_package
            && !reachable.contains(&package.id)
        {
            return Err(PlanningError::new(
                PlanningErrorKind::UnreachableEntrypoint,
                format!(
                    "collector entry package `{}` is not in root package `{}`'s resolved dependency closure",
                    package.name, root_package.name
                ),
            ));
        }

        let semantic_ids: BTreeSet<_> = facet_records
            .iter()
            .map(|facet| facet.package.id.as_str())
            .collect();
        let direct_ids: BTreeSet<_> = semantic_ids
            .iter()
            .copied()
            .chain(extra_package.map(|package| package.id.as_str()))
            .collect();
        let aliases = allocate_aliases(
            direct_ids
                .iter()
                .map(|id| packages[*id])
                .collect::<Vec<_>>(),
        );

        let mut facets = Vec::with_capacity(facet_records.len());
        for facet in &facet_records {
            let library_target = selected_library_target(facet.package)?;
            facets.push(ResolvedFacet {
                is_root: facet.is_root,
                k_namespace: facet.k_namespace.clone(),
                package_name: facet.package.name.clone(),
                package_version: facet.package.version.clone(),
                cargo_source: logical_cargo_source(facet.package, &workspace_members),
                definition: facet.definition.clone(),
                root: facet.root.clone(),
                syntax_root: facet.syntax_root.clone(),
                dependency_alias: aliases[&facet.package.id].clone(),
                crate_root: library_target.name.clone(),
                cargo_package_id: facet.package.id.clone(),
                manifest_path: PathBuf::from(&facet.package.manifest_path),
            });
        }
        facets.sort_by(|left, right| facet_key(left).cmp(&facet_key(right)));

        let closure_ids = dependency_order(&root_package.id, &nodes, &packages)?;
        let package_closure = closure_ids
            .iter()
            .map(|id| {
                let package = packages[id.as_str()];
                let node = nodes[id.as_str()];
                ResolvedPackage {
                    name: package.name.clone(),
                    version: package.version.clone(),
                    cargo_source: logical_cargo_source(package, &workspace_members),
                    features: node.features.iter().cloned().collect(),
                    semantics: semantic_ids.contains(id.as_str()),
                    cargo_package_id: id.clone(),
                    manifest_path: PathBuf::from(&package.manifest_path),
                    dependency_ids: node.dependencies.iter().cloned().collect(),
                }
            })
            .collect::<Vec<_>>();

        let mut dependencies = direct_ids
            .iter()
            .map(|id| {
                let package = packages[*id];
                let node = nodes[*id];
                GeneratedDependency {
                    alias: aliases[*id].clone(),
                    package_name: package.name.clone(),
                    manifest_path: PathBuf::from(&package.manifest_path),
                    features: node.features.iter().cloned().collect(),
                    semantics: semantic_ids.contains(*id),
                }
            })
            .collect::<Vec<_>>();
        dependencies.sort_by(|left, right| left.alias.cmp(&right.alias));

        Ok(ResolvedSelection {
            facets,
            package_closure,
            host_target: host_target.to_owned(),
            cfg: cfg.iter().cloned().collect(),
            dependencies,
            extra_alias: extra_package.map(|package| aliases[&package.id].clone()),
        })
    }

    /// Resolve a production collector request.
    ///
    /// The runtime manifests identify infrastructure owned by the installed
    /// KRS tool, not functions or packages supplied by the authored language.
    /// Generated collection calls the KRS host and compiler APIs directly.
    ///
    /// # Errors
    ///
    /// Returns the same selection errors as [`Self::resolve`], or
    /// [`PlanningErrorKind::InvalidCollectorRuntime`] when a runtime manifest
    /// is not a `Cargo.toml` path with a parent directory.
    pub fn resolve_definition(
        metadata: &CargoMetadata,
        request: &DefinitionRequest,
        runtime: CollectorRuntime,
    ) -> Result<Self, PlanningError> {
        validate_runtime_manifest(&runtime.host_manifest, "krs")?;
        validate_runtime_manifest(&runtime.collector_manifest, "krs-collector")?;
        let selection = Self::resolve_selection(
            metadata,
            &request.root,
            &request.dependencies,
            &request.host_target,
            &request.cfg,
            None,
        )?;
        let plan = selection.into_plan(CollectorKind::Production {
            runtime,
            registration: RegistrationMode::Inventory,
        });
        plan.package_contexts()?;
        Ok(plan)
    }

    /// Switch a production plan to explicit registration tables.
    ///
    /// The generated collector then disables the `krs` `inventory` feature
    /// and reads each semantics package's crate-root `__KRS_REGISTRATIONS`
    /// table. This is build tooling for targets without linker-section
    /// registration and for the native parity gate, not an author-facing
    /// mode.
    ///
    /// # Errors
    ///
    /// Returns [`PlanningErrorKind::InvalidRegistrationMode`] for a
    /// non-production plan, [`PlanningErrorKind::InventoryFeatureActive`] when
    /// the resolved `krs` package has `inventory` enabled (Cargo feature
    /// unification cannot disable it from the collector), and
    /// [`PlanningErrorKind::UnregisteredKrsDependent`] when a package that
    /// depends on `krs` is not a selected semantics package, because its
    /// descriptors would silently disappear rather than fail collection.
    pub fn with_explicit_registration(mut self) -> Result<Self, PlanningError> {
        if !self.is_production() {
            return Err(PlanningError::new(
                PlanningErrorKind::InvalidRegistrationMode,
                "explicit registration requires a production collector plan",
            ));
        }
        let facade_ids = self
            .package_closure
            .iter()
            .filter(|package| package.name == "krs")
            .map(|package| package.cargo_package_id.as_str())
            .collect::<BTreeSet<_>>();
        if let Some(facade) = self.package_closure.iter().find(|package| {
            facade_ids.contains(package.cargo_package_id.as_str())
                && package
                    .features
                    .iter()
                    .any(|feature| feature == "inventory")
        }) {
            return Err(PlanningError::new(
                PlanningErrorKind::InventoryFeatureActive,
                format!(
                    "explicit registration requires the `inventory` feature of `krs {}` to be disabled; depend on it with `default-features = false`",
                    facade.version
                ),
            ));
        }
        if let Some(dependent) = self.package_closure.iter().find(|package| {
            !package.semantics
                && !facade_ids.contains(package.cargo_package_id.as_str())
                && package
                    .dependency_ids
                    .iter()
                    .any(|dependency| facade_ids.contains(dependency.as_str()))
        }) {
            return Err(PlanningError::new(
                PlanningErrorKind::UnregisteredKrsDependent,
                format!(
                    "package `{} {}` depends on `krs` but is not a selected semantics package; explicit registration would omit its descriptors",
                    dependent.name, dependent.version
                ),
            ));
        }
        if let CollectorKind::Production { registration, .. } = &mut self.kind {
            *registration = RegistrationMode::Explicit;
        }
        Ok(self)
    }

    /// The descriptor registration mechanism of the generated collector.
    /// Entry-point collectors do not use registration and report inventory mode.
    #[must_use]
    pub const fn registration(&self) -> RegistrationMode {
        match &self.kind {
            CollectorKind::EntryPoint { .. } => RegistrationMode::Inventory,
            CollectorKind::Production { registration, .. } => *registration,
        }
    }

    /// Whether this plan uses KRS-owned production collection.
    #[must_use]
    pub const fn is_production(&self) -> bool {
        matches!(self.kind, CollectorKind::Production { .. })
    }

    /// Selected definition facets in canonical order.
    #[must_use]
    pub fn facets(&self) -> &[ResolvedFacet] {
        &self.facets
    }

    /// Root package dependency closure in deterministic dependency order.
    #[must_use]
    pub fn package_closure(&self) -> &[ResolvedPackage] {
        &self.package_closure
    }

    /// Host target triple used to execute the collector.
    #[must_use]
    pub fn host_target(&self) -> &str {
        &self.host_target
    }

    /// KRS cfg inputs in canonical order.
    #[must_use]
    pub fn cfg(&self) -> &BTreeSet<KrsCfg> {
        &self.cfg
    }

    pub(crate) fn context_facets(&self) -> impl Iterator<Item = &ResolvedFacet> {
        let mut seen = BTreeSet::new();
        self.facets
            .iter()
            .filter(move |facet| seen.insert((&facet.cargo_package_id, &facet.k_namespace)))
    }

    /// Canonical, path-free JSON selection data.
    ///
    /// This is suitable for hashing, diagnostics, and protocol-adjacent tests.
    /// Absolute manifest paths remain confined to generated Cargo build files.
    /// Schema 2 adds the semantic `crate-root` selected from Cargo target
    /// metadata; readers must not interpret schema 1 bytes as carrying that
    /// identity component.
    ///
    /// # Errors
    ///
    /// Returns the underlying JSON error if serialization fails.
    #[must_use = "canonical selection bytes must be consumed or persisted"]
    pub fn canonical_selection_json(&self) -> Result<Vec<u8>, serde_json::Error> {
        let document = CanonicalSelection {
            schema: 2,
            facets: self
                .facets
                .iter()
                .map(|facet| CanonicalFacet {
                    role: if facet.is_root { "root" } else { "dependency" },
                    k_namespace: &facet.k_namespace,
                    package: &facet.package_name,
                    version: &facet.package_version,
                    cargo_source: &facet.cargo_source,
                    crate_root: &facet.crate_root,
                    definition: &facet.definition,
                    root: &facet.root,
                    syntax_root: &facet.syntax_root,
                    features: self.features_for(&facet.cargo_package_id),
                })
                .collect(),
            cfg: &self.cfg,
        };
        let mut bytes = serde_json::to_vec_pretty(&document)?;
        bytes.push(b'\n');
        Ok(bytes)
    }

    /// Constructs compiler collection contexts in canonical facet order.
    ///
    /// Multiple facets selected from one Cargo package and immutable K
    /// namespace share one context. The first facet in canonical order emits
    /// it, preventing duplicate compiler contexts while retaining every facet
    /// in [`Self::facets`] and canonical selection data.
    ///
    /// # Errors
    ///
    /// Returns [`PlanningError`] if stored Cargo identity, target, or manifest
    /// data does not satisfy [`PackageContext`] validation. A plan returned by
    /// [`Self::resolve`] or [`Self::resolve_definition`] has already passed
    /// this validation.
    pub fn package_contexts(&self) -> Result<Vec<PackageContext>, PlanningError> {
        let mut contexts = Vec::new();
        for facet in self.context_facets() {
            let context = PackageContext::new(
                &facet.k_namespace,
                &facet.package_name,
                &facet.package_version,
                &facet.cargo_source,
                &facet.crate_root,
                &facet.manifest_path,
            )
            .map_err(|error| {
                PlanningError::new(
                    PlanningErrorKind::InvalidPackageContext,
                    format!(
                        "selected semantics package `{}` has invalid compiler context: {error}",
                        facet.package_name
                    ),
                )
            })?;
            contexts.push(context);
        }
        Ok(contexts)
    }

    fn features_for(&self, package_id: &str) -> BTreeSet<&String> {
        self.package_closure
            .iter()
            .find(|package| package.cargo_package_id == package_id)
            .map_or_else(BTreeSet::new, |package| package.features.iter().collect())
    }
}

#[derive(Serialize)]
struct CanonicalSelection<'a> {
    schema: u32,
    facets: Vec<CanonicalFacet<'a>>,
    cfg: &'a BTreeSet<KrsCfg>,
}

#[derive(Serialize)]
struct CanonicalFacet<'a> {
    role: &'static str,
    #[serde(rename = "k-namespace")]
    k_namespace: &'a str,
    package: &'a str,
    version: &'a str,
    #[serde(rename = "cargo-source")]
    cargo_source: &'a str,
    #[serde(rename = "crate-root")]
    crate_root: &'a str,
    definition: &'a str,
    root: &'a str,
    #[serde(rename = "syntax-root")]
    syntax_root: &'a str,
    features: BTreeSet<&'a String>,
}

struct FacetRecord<'a> {
    package: &'a MetadataPackage,
    k_namespace: String,
    definition: String,
    root: String,
    syntax_root: String,
    is_root: bool,
}

impl FacetRecord<'_> {
    fn sort_key(&self) -> (&str, bool, &str, &str, &str) {
        (
            &self.k_namespace,
            !self.is_root,
            &self.package.name,
            &self.package.version,
            &self.definition,
        )
    }
}

fn facet_key(facet: &ResolvedFacet) -> (bool, &str, &str, &str, &str) {
    (
        !facet.is_root,
        &facet.k_namespace,
        &facet.package_name,
        &facet.package_version,
        &facet.definition,
    )
}

fn package_map(
    metadata: &CargoMetadata,
) -> Result<BTreeMap<&str, &MetadataPackage>, PlanningError> {
    let mut packages = BTreeMap::new();
    for package in &metadata.packages {
        if packages.insert(package.id.as_str(), package).is_some() {
            return Err(PlanningError::new(
                PlanningErrorKind::InvalidMetadata,
                format!("Cargo metadata repeats package ID `{}`", package.id),
            ));
        }
    }
    Ok(packages)
}

fn node_map<'a>(
    metadata: &'a CargoMetadata,
    packages: &BTreeMap<&str, &MetadataPackage>,
) -> Result<BTreeMap<&'a str, &'a MetadataNode>, PlanningError> {
    let resolve = metadata.resolve.as_ref().ok_or_else(|| {
        PlanningError::new(
            PlanningErrorKind::MissingResolveGraph,
            "Cargo metadata did not include a resolve graph; do not use `--no-deps`",
        )
    })?;
    let mut nodes = BTreeMap::new();
    for node in &resolve.nodes {
        if !packages.contains_key(node.id.as_str()) {
            return Err(PlanningError::new(
                PlanningErrorKind::InvalidMetadata,
                format!("resolve node `{}` has no corresponding package", node.id),
            ));
        }
        if nodes.insert(node.id.as_str(), node).is_some() {
            return Err(PlanningError::new(
                PlanningErrorKind::InvalidMetadata,
                format!("Cargo metadata repeats resolve node `{}`", node.id),
            ));
        }
    }
    for package_id in packages.keys() {
        if !nodes.contains_key(package_id) {
            return Err(PlanningError::new(
                PlanningErrorKind::InvalidMetadata,
                format!("package `{package_id}` has no resolve node"),
            ));
        }
    }
    Ok(nodes)
}

fn select_package<'a>(
    metadata: &'a CargoMetadata,
    selector: &PackageSelector,
) -> Result<&'a MetadataPackage, PlanningError> {
    match selector {
        PackageSelector::Id(id) => metadata
            .packages
            .iter()
            .find(|package| package.id == *id)
            .ok_or_else(|| {
                PlanningError::new(
                    PlanningErrorKind::MissingPackage,
                    format!("Cargo metadata contains no package with ID `{id}`"),
                )
            }),
        PackageSelector::Name(name) => {
            let matches = metadata
                .packages
                .iter()
                .filter(|package| package.name == *name)
                .collect::<Vec<_>>();
            match matches.as_slice() {
                [] => Err(PlanningError::new(
                    PlanningErrorKind::MissingPackage,
                    format!("Cargo metadata contains no package named `{name}`"),
                )),
                [package] => Ok(*package),
                _ => Err(PlanningError::new(
                    PlanningErrorKind::AmbiguousPackage,
                    format!(
                        "package name `{name}` matches {} resolved packages; select an exact Cargo package ID",
                        matches.len()
                    ),
                )),
            }
        }
    }
}

fn resolve_facet<'a>(
    package: &'a MetadataPackage,
    definition: &str,
    is_root: bool,
) -> Result<FacetRecord<'a>, PlanningError> {
    let krs = package
        .metadata
        .get("krs")
        .and_then(Value::as_object)
        .ok_or_else(|| {
            PlanningError::new(
                PlanningErrorKind::MissingKrsMetadata,
                format!(
                    "package `{}` has no `package.metadata.krs` table",
                    package.name
                ),
            )
        })?;
    let namespace = krs
        .get("k-namespace")
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| {
            PlanningError::new(
                PlanningErrorKind::MissingNamespace,
                format!(
                    "package `{}` has no non-empty KRS `k-namespace`",
                    package.name
                ),
            )
        })?;
    let definitions = krs
        .get("definitions")
        .and_then(Value::as_object)
        .ok_or_else(|| {
            PlanningError::new(
                PlanningErrorKind::MissingDefinition,
                format!("package `{}` declares no KRS definitions", package.name),
            )
        })?;
    let facet = definitions
        .get(definition)
        .and_then(Value::as_object)
        .ok_or_else(|| {
            PlanningError::new(
                PlanningErrorKind::MissingDefinition,
                format!(
                    "package `{}` declares no KRS definition facet `{definition}`",
                    package.name
                ),
            )
        })?;
    let root = optional_string(facet.get("root"), "root", package, definition)?
        .unwrap_or_else(|| "crate".to_owned());
    let syntax_root =
        optional_string(facet.get("syntax-root"), "syntax-root", package, definition)?
            .unwrap_or_else(|| "crate".to_owned());

    Ok(FacetRecord {
        package,
        k_namespace: namespace.to_owned(),
        definition: definition.to_owned(),
        root,
        syntax_root,
        is_root,
    })
}

fn selected_library_target(package: &MetadataPackage) -> Result<&MetadataTarget, PlanningError> {
    let eligible = package
        .targets
        .iter()
        .filter(|target| is_linkable_library_target(target))
        .collect::<Vec<_>>();
    match eligible.as_slice() {
        [] => Err(PlanningError::new(
            PlanningErrorKind::MissingLibraryTarget,
            format!(
                "selected semantics package `{}` has no linkable Rust library target",
                package.name
            ),
        )),
        [target] => Ok(*target),
        targets => Err(PlanningError::new(
            PlanningErrorKind::AmbiguousLibraryTarget,
            format!(
                "selected semantics package `{}` has {} linkable Rust library targets: {}",
                package.name,
                targets.len(),
                targets
                    .iter()
                    .map(|target| target.name.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        )),
    }
}

fn is_linkable_library_target(target: &MetadataTarget) -> bool {
    let library_kind = target
        .kind
        .iter()
        .any(|kind| matches!(kind.as_str(), "lib" | "rlib" | "dylib"));
    let rust_linkable_crate_type = target
        .crate_types
        .iter()
        .any(|crate_type| matches!(crate_type.as_str(), "lib" | "rlib" | "dylib"));
    library_kind && rust_linkable_crate_type
}

fn optional_string(
    value: Option<&Value>,
    field: &str,
    package: &MetadataPackage,
    definition: &str,
) -> Result<Option<String>, PlanningError> {
    match value {
        None => Ok(None),
        Some(value) => value
            .as_str()
            .map(|text| Some(text.to_owned()))
            .ok_or_else(|| {
                PlanningError::new(
                    PlanningErrorKind::InvalidDefinition,
                    format!(
                        "KRS definition `{}` in package `{}` has a non-string `{field}`",
                        definition, package.name
                    ),
                )
            }),
    }
}

fn reachable_packages(
    root: &str,
    nodes: &BTreeMap<&str, &MetadataNode>,
) -> Result<BTreeSet<String>, PlanningError> {
    let mut reachable = BTreeSet::new();
    let mut pending = vec![root.to_owned()];
    while let Some(id) = pending.pop() {
        if !reachable.insert(id.clone()) {
            continue;
        }
        let node = nodes.get(id.as_str()).ok_or_else(|| {
            PlanningError::new(
                PlanningErrorKind::InvalidMetadata,
                format!("selected package `{id}` has no resolve node"),
            )
        })?;
        for dependency in &node.dependencies {
            if !nodes.contains_key(dependency.as_str()) {
                return Err(PlanningError::new(
                    PlanningErrorKind::InvalidMetadata,
                    format!("resolve node `{id}` references missing dependency `{dependency}`"),
                ));
            }
            pending.push(dependency.clone());
        }
    }
    Ok(reachable)
}

fn dependency_order(
    root: &str,
    nodes: &BTreeMap<&str, &MetadataNode>,
    packages: &BTreeMap<&str, &MetadataPackage>,
) -> Result<Vec<String>, PlanningError> {
    fn visit(
        id: &str,
        nodes: &BTreeMap<&str, &MetadataNode>,
        packages: &BTreeMap<&str, &MetadataPackage>,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
        output: &mut Vec<String>,
    ) -> Result<(), PlanningError> {
        if visited.contains(id) {
            return Ok(());
        }
        if !visiting.insert(id.to_owned()) {
            return Err(PlanningError::new(
                PlanningErrorKind::DependencyCycle,
                format!("Cargo resolve graph contains a cycle at package `{id}`"),
            ));
        }
        let node = nodes[id];
        let dependencies = node
            .dependencies
            .iter()
            .map(|dependency| (package_sort_key(packages[dependency.as_str()]), dependency))
            .collect::<BTreeSet<_>>();
        for (_, dependency) in dependencies {
            visit(dependency, nodes, packages, visiting, visited, output)?;
        }
        visiting.remove(id);
        visited.insert(id.to_owned());
        output.push(id.to_owned());
        Ok(())
    }

    let mut output = Vec::new();
    visit(
        root,
        nodes,
        packages,
        &mut BTreeSet::new(),
        &mut BTreeSet::new(),
        &mut output,
    )?;
    Ok(output)
}

fn package_sort_key(package: &MetadataPackage) -> (&str, &str, Option<&str>, &str) {
    (
        &package.name,
        &package.version,
        package.source.as_deref(),
        &package.id,
    )
}

fn ensure_unique_namespaces(facets: &[FacetRecord<'_>]) -> Result<(), PlanningError> {
    let mut owners = BTreeMap::<&str, &str>::new();
    for facet in facets {
        if let Some(owner) = owners.insert(&facet.k_namespace, &facet.package.id)
            && owner != facet.package.id
        {
            return Err(PlanningError::new(
                PlanningErrorKind::DuplicateNamespace,
                format!(
                    "KRS namespace `{}` is declared by more than one selected package",
                    facet.k_namespace
                ),
            ));
        }
    }
    Ok(())
}

fn allocate_aliases(packages: Vec<&MetadataPackage>) -> BTreeMap<String, String> {
    let mut packages = packages;
    packages.sort_by(|left, right| package_sort_key(left).cmp(&package_sort_key(right)));
    let mut grouped = BTreeMap::<String, Vec<&MetadataPackage>>::new();
    for package in packages {
        grouped
            .entry(rust_identifier(&package.name))
            .or_default()
            .push(package);
    }
    let mut aliases = BTreeMap::new();
    for (base, mut group) in grouped {
        group.sort_by(|left, right| package_sort_key(left).cmp(&package_sort_key(right)));
        if group.len() == 1 {
            aliases.insert(group[0].id.clone(), base);
        } else {
            for (index, package) in group.into_iter().enumerate() {
                aliases.insert(package.id.clone(), format!("{base}__{}", index + 1));
            }
        }
    }
    aliases
}

fn rust_identifier(name: &str) -> String {
    let mut identifier = String::new();
    let mut previous_underscore = false;
    for character in name.chars() {
        let mapped = if character.is_ascii_alphanumeric() || character == '_' {
            character.to_ascii_lowercase()
        } else {
            '_'
        };
        if mapped == '_' && previous_underscore {
            continue;
        }
        previous_underscore = mapped == '_';
        identifier.push(mapped);
    }
    identifier = identifier.trim_matches('_').to_owned();
    if identifier.is_empty()
        || identifier.starts_with(|character: char| character.is_ascii_digit())
        || keyword::is_keyword(&identifier)
    {
        identifier.insert_str(0, "pkg_");
    }
    identifier
}

fn validate_host_target(target: &str) -> Result<(), PlanningError> {
    if target.is_empty()
        || !target
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
    {
        return Err(PlanningError::new(
            PlanningErrorKind::InvalidHostTarget,
            format!("invalid host target triple `{target}`"),
        ));
    }
    Ok(())
}

fn validate_cfg(cfg: &[KrsCfg]) -> Result<(), PlanningError> {
    for predicate in cfg {
        if !valid_identifier_segment(&predicate.key) {
            return Err(PlanningError::new(
                PlanningErrorKind::InvalidCfg,
                format!("invalid cfg predicate name `{}`", predicate.key),
            ));
        }
        if predicate
            .value
            .as_ref()
            .is_some_and(|value| value.contains(['\n', '\r', '\0']))
        {
            return Err(PlanningError::new(
                PlanningErrorKind::InvalidCfg,
                format!("cfg predicate `{}` has an invalid value", predicate.key),
            ));
        }
    }
    Ok(())
}

fn validate_rust_path(path: &[String]) -> Result<(), PlanningError> {
    if path.is_empty()
        || path
            .iter()
            .any(|segment| !valid_identifier_segment(segment))
    {
        return Err(PlanningError::new(
            PlanningErrorKind::InvalidEntrypoint,
            "collector entrypoint must contain only non-empty Rust identifier segments",
        ));
    }
    Ok(())
}

fn validate_runtime_manifest(path: &Path, package: &str) -> Result<(), PlanningError> {
    if path.file_name().and_then(|name| name.to_str()) != Some("Cargo.toml")
        || path.parent().is_none()
    {
        return Err(PlanningError::new(
            PlanningErrorKind::InvalidCollectorRuntime,
            format!(
                "collector runtime package `{package}` has invalid manifest path `{}`",
                path.display()
            ),
        ));
    }
    Ok(())
}

/// Return whether a segment is a Rust identifier accepted by KRS planning.
#[must_use]
pub fn valid_identifier_segment(segment: &str) -> bool {
    let mut bytes = segment.bytes();
    matches!(bytes.next(), Some(first) if first.is_ascii_alphabetic() || first == b'_')
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        && !keyword::is_keyword(segment)
}

fn logical_cargo_source(package: &MetadataPackage, workspace_members: &BTreeSet<&str>) -> String {
    if let Some(source) = &package.source {
        source.clone()
    } else if workspace_members.contains(package.id.as_str()) {
        "workspace".to_owned()
    } else {
        "path".to_owned()
    }
}

/// Stable category for a planning failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum PlanningErrorKind {
    /// Metadata has inconsistent package or resolve records.
    InvalidMetadata,
    /// Full dependency metadata was not supplied.
    MissingResolveGraph,
    /// A package selector matched nothing.
    MissingPackage,
    /// A name selector matched multiple package IDs.
    AmbiguousPackage,
    /// A selected package has no KRS metadata table.
    MissingKrsMetadata,
    /// A selected package has no immutable semantic namespace.
    MissingNamespace,
    /// A selected facet does not exist.
    MissingDefinition,
    /// A selected facet has an invalid metadata shape.
    InvalidDefinition,
    /// A selected semantics package has no linkable Rust library target.
    MissingLibraryTarget,
    /// A selected semantics package has multiple linkable Rust library targets.
    AmbiguousLibraryTarget,
    /// Selected package identity, target, or manifest data is compiler-invalid.
    InvalidPackageContext,
    /// Two selected packages declare the same semantic namespace.
    DuplicateNamespace,
    /// A dependency facet is not in the root Cargo package closure.
    UnreachableSelection,
    /// The configured collector package is not in the root Cargo package closure.
    UnreachableEntrypoint,
    /// Cargo metadata unexpectedly contains a dependency cycle.
    DependencyCycle,
    /// The requested host target is not a target-triple-shaped value.
    InvalidHostTarget,
    /// A KRS cfg input is not safe Rust cfg syntax.
    InvalidCfg,
    /// The collector function path is invalid.
    InvalidEntrypoint,
    /// A KRS-owned collector runtime manifest path is malformed.
    InvalidCollectorRuntime,
    /// The requested registration mode does not apply to this plan.
    InvalidRegistrationMode,
    /// Explicit registration was requested while `krs` enables `inventory`.
    InventoryFeatureActive,
    /// Explicit registration would omit a non-semantics `krs` dependent.
    UnregisteredKrsDependent,
}

/// A typed collector planning failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlanningError {
    kind: PlanningErrorKind,
    message: String,
}

impl PlanningError {
    fn new(kind: PlanningErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
        }
    }

    /// Machine-readable failure category.
    #[must_use]
    pub const fn kind(&self) -> PlanningErrorKind {
        self.kind
    }
}

impl ToDiagnostic for PlanningError {
    fn to_diagnostic(&self) -> Diagnostic {
        let code = match self.kind {
            PlanningErrorKind::InvalidMetadata => codes::plan::INVALID_METADATA,
            PlanningErrorKind::MissingResolveGraph => codes::plan::MISSING_RESOLVE_GRAPH,
            PlanningErrorKind::MissingPackage => codes::plan::MISSING_PACKAGE,
            PlanningErrorKind::AmbiguousPackage => codes::plan::AMBIGUOUS_PACKAGE,
            PlanningErrorKind::MissingKrsMetadata => codes::plan::MISSING_KRS_METADATA,
            PlanningErrorKind::MissingNamespace => codes::plan::MISSING_NAMESPACE,
            PlanningErrorKind::MissingDefinition => codes::plan::MISSING_DEFINITION,
            PlanningErrorKind::InvalidDefinition => codes::plan::INVALID_DEFINITION,
            PlanningErrorKind::MissingLibraryTarget => codes::plan::MISSING_LIBRARY_TARGET,
            PlanningErrorKind::AmbiguousLibraryTarget => codes::plan::AMBIGUOUS_LIBRARY_TARGET,
            PlanningErrorKind::InvalidPackageContext => codes::plan::INVALID_PACKAGE_CONTEXT,
            PlanningErrorKind::DuplicateNamespace => codes::plan::DUPLICATE_NAMESPACE,
            PlanningErrorKind::UnreachableSelection => codes::plan::UNREACHABLE_SELECTION,
            PlanningErrorKind::UnreachableEntrypoint => codes::plan::UNREACHABLE_ENTRYPOINT,
            PlanningErrorKind::DependencyCycle => codes::plan::DEPENDENCY_CYCLE,
            PlanningErrorKind::InvalidHostTarget => codes::plan::INVALID_HOST_TARGET,
            PlanningErrorKind::InvalidCfg => codes::plan::INVALID_CFG,
            PlanningErrorKind::InvalidEntrypoint => codes::plan::INVALID_ENTRYPOINT,
            PlanningErrorKind::InvalidCollectorRuntime => codes::plan::INVALID_COLLECTOR_RUNTIME,
            PlanningErrorKind::InvalidRegistrationMode => codes::plan::INVALID_REGISTRATION_MODE,
            PlanningErrorKind::InventoryFeatureActive => codes::plan::INVENTORY_FEATURE_ACTIVE,
            PlanningErrorKind::UnregisteredKrsDependent => codes::plan::UNREGISTERED_KRS_DEPENDENT,
        };
        Diagnostic::error(code, self.to_string(), Location::None)
    }
}

impl fmt::Display for PlanningError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl Error for PlanningError {}

pub(crate) fn manifest_directory(path: &Path) -> Result<&Path, PlanningError> {
    path.parent().ok_or_else(|| {
        PlanningError::new(
            PlanningErrorKind::InvalidMetadata,
            format!("manifest path `{}` has no parent directory", path.display()),
        )
    })
}
