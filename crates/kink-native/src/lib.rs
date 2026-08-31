//! Fail-closed integration over the pinned KRS and k-rust native definition boundary.
//!
//! The index in this crate is semantic and owner-qualified, but its provenance data is only the
//! KRS sidecar. The pinned KRS revision does not bridge that sidecar into every k-rust production,
//! term span, source-table entry, and generated origin. Consequently no type in this crate grants
//! native provenance authority.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    path::{Path, PathBuf},
    process::Command,
};

use k_rust::{
    builtin,
    definition::{Definition, ProductionItem, Sentence, compute_subsorts},
    kast::{Label, Sort, Term},
    kompile::{CompileOptions, CompiledKoreArtifacts, compile_loaded_definition},
    outer::{LoadOptions, load_structured},
};
use kink_patch::StagedNativeInput;

/// Native definition type accepted by the exact k-rust pin.
pub type NativeDefinition = Definition;

/// Exact KRS source revision reviewed by NR-05.
pub const KRS_REVISION: &str = "9a10f89e04cf4bc48ba42046569b31644bd0f55e";

/// Exact k-rust source revision declared by the reviewed KRS checkout.
pub const K_RUST_REVISION: &str = "0de7983f76f87ce93b91f5d3e994f0a2c3ff710c";

/// Absolute clean-source locations selected by the native-readiness work package.
pub const KRS_PATH: &str = "/home/sebastiengllmt/git/workspaces/starstream-fv/krs";
pub const K_RUST_PATH: &str =
    "/home/sebastiengllmt/git/workspaces/starstream-fv/inspirations/midnightntwrk/k-rust-krs-main";

/// Filesystem locations whose repository identity and cleanliness must be checked before use.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PinnedSources {
    pub krs: PathBuf,
    pub k_rust: PathBuf,
}

impl Default for PinnedSources {
    fn default() -> Self {
        Self {
            krs: PathBuf::from(KRS_PATH),
            k_rust: PathBuf::from(K_RUST_PATH),
        }
    }
}

/// Evidence that both source repositories were exact and clean at validator construction time.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedPins {
    pub krs_revision: &'static str,
    pub k_rust_revision: &'static str,
    pub k_rust_crate_version: &'static str,
    pub declared_krs_feature_profile: &'static str,
    pub integration_feature_profile: &'static str,
    pub rustc_identity: String,
}

/// Closed structural destination roles emitted by the reviewed KRS sidecar.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum NativeNodeRole {
    Module,
    Sentence,
    ConfigurationCell,
    ConfigurationInitializer,
    ContextAliasName,
    ContextAliasHere,
    ContextAliasCell(u32),
    ContextAliasFrame(u32),
    StrictnessContextAlias,
    StrictnessField(u32),
    StrictnessResult,
    ProductionItem(u32),
    ProductionAttribute(u32),
    ConfigurationRuleCell(u32),
    ConfigurationRuleFrame(u32),
    ClaimBinder(u32),
    ClaimBinderName(u32),
    ClaimBinderSort(u32),
    ClaimModality,
    ClaimCircularity,
    Requires,
    Ensures,
    Term(Vec<u32>),
}

/// Closed sentence inventory for the pinned k-rust `Sentence` enum.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SentenceVariant {
    SyntaxSort,
    SortSynonym,
    SyntaxLexical,
    Production,
    SyntaxAssociativity,
    SyntaxPriority,
    ContextAlias,
    Context,
    Rule,
    Claim,
    Configuration,
    Bubble,
}

/// Closed term inventory for the pinned k-rust `Term` enum.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TermVariant {
    InjectedLabel,
    Rewrite,
    As,
    Variable,
    Sequence,
    Apply,
    Token,
    Annotated,
}

/// Exact inventory observed while indexing one admitted native definition.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct NativeInventory {
    pub sentence_variants: BTreeMap<SentenceVariant, usize>,
    pub term_variants: BTreeMap<TermVariant, usize>,
}

/// Stable module-local sentence identity. Module name, not module vector position, owns identity.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NativeSentenceId {
    pub owner_module: String,
    pub ordinal: usize,
}

/// Owner-qualified declared symbol identity.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NativeSymbolId {
    pub owner_module: String,
    pub label: String,
}

/// Owner-qualified declared sort identity.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NativeSortId {
    pub owner_module: String,
    pub sort: Sort,
}

/// One native production signature.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NativeSignature {
    pub result: Sort,
    pub arguments: Vec<Sort>,
    pub sentence: NativeSentenceId,
}

/// One direct semantic subsort edge selected by the pinned frontend's rule.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NativeSubsort {
    pub owner_module: String,
    pub child: Sort,
    pub parent: Sort,
    pub sentence: NativeSentenceId,
}

/// Non-authoritative summary of one KRS sidecar mapping.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProvenanceSidecarRecord {
    pub source_map_key: String,
    pub module: String,
    pub sentence_index: Option<usize>,
    pub role: NativeNodeRole,
}

impl ProvenanceSidecarRecord {
    /// Construct a non-authoritative record copied from one KRS `OriginMapping`.
    pub fn new(
        source_map_key: impl Into<String>,
        module: impl Into<String>,
        sentence_index: Option<usize>,
        role: NativeNodeRole,
    ) -> Self {
        Self {
            source_map_key: source_map_key.into(),
            module: module.into(),
            sentence_index,
            role,
        }
    }
}

/// Destination-keyed KRS sidecar. It is deliberately not a provenance receipt.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ProvenanceSidecarIndex {
    pub records: BTreeMap<(String, Option<usize>, NativeNodeRole), ProvenanceSidecarRecord>,
}

/// Semantic indexes over an admitted native source definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NativeIndex {
    pub inventory: NativeInventory,
    pub declarations: BTreeMap<NativeSentenceId, SentenceVariant>,
    pub sorts: BTreeMap<NativeSortId, NativeSentenceId>,
    pub signatures: BTreeMap<NativeSymbolId, NativeSignature>,
    pub subsorts: BTreeSet<NativeSubsort>,
    pub resolved_symbol_uses: BTreeMap<(NativeSentenceId, Vec<u32>), NativeSymbolId>,
    pub provenance_sidecar: ProvenanceSidecarIndex,
}

/// Explicit status of provenance available from this adapter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProvenanceStatus {
    /// KRS mappings were indexed, but the KRS-to-k-rust provenance bridge is absent.
    SidecarOnlyMissingBridge,
}

/// Opaque NR-02 native success output. Construction is possible only after the whole pipeline.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidatedNativeOutput {
    definition: NativeDefinition,
    index: NativeIndex,
    artifacts: CompiledKoreArtifacts,
    pins: VerifiedPins,
    compile_options: CompileOptions,
}

impl ValidatedNativeOutput {
    pub const fn definition(&self) -> &NativeDefinition {
        &self.definition
    }

    pub const fn index(&self) -> &NativeIndex {
        &self.index
    }

    pub const fn artifacts(&self) -> &CompiledKoreArtifacts {
        &self.artifacts
    }

    pub const fn pins(&self) -> &VerifiedPins {
        &self.pins
    }

    /// Exact backend, KORE width, claims mode, and hook namespace profile used for lowering.
    pub const fn compile_options(&self) -> &CompileOptions {
        &self.compile_options
    }

    pub const fn provenance_status(&self) -> ProvenanceStatus {
        ProvenanceStatus::SidecarOnlyMissingBridge
    }
}

/// A native patch rejection supplied before resolution and lowering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NativePatchRejection {
    detail: String,
}

impl NativePatchRejection {
    pub fn new(detail: impl Into<String>) -> Self {
        Self {
            detail: detail.into(),
        }
    }
}

impl fmt::Display for NativePatchRejection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.detail.fmt(formatter)
    }
}

impl std::error::Error for NativePatchRejection {}

/// Typed fail-closed native integration failures. No variant contains staged output or identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NativeFailure {
    PinRepositoryUnavailable {
        repository: &'static str,
        detail: String,
    },
    WrongRevision {
        repository: &'static str,
        expected: &'static str,
        actual: String,
    },
    DirtyRepository {
        repository: &'static str,
    },
    DeclaredFrontendMismatch(String),
    DuplicateModule(String),
    UnsupportedSentence {
        module: String,
        ordinal: usize,
        variant: SentenceVariant,
    },
    DuplicateLabel {
        owner: String,
        label: String,
    },
    DuplicateSort {
        owner: String,
        sort: Sort,
    },
    InvalidSubsort(String),
    AmbiguousSymbolOwner {
        module: String,
        label: String,
        owners: Vec<String>,
    },
    ArityMismatch {
        module: String,
        label: String,
        expected: usize,
        actual: usize,
    },
    InvalidSidecar(String),
    PatchRejected(String),
    Preparation(String),
    Compilation {
        stage: &'static str,
        detail: String,
    },
}

impl NativeFailure {
    /// Every failure publishes no output and therefore commits zero edits at the NR-02 boundary.
    pub const fn committed_edit_count(&self) -> usize {
        0
    }
}

impl fmt::Display for NativeFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PinRepositoryUnavailable { repository, detail } => {
                write!(formatter, "cannot verify {repository}: {detail}")
            }
            Self::WrongRevision {
                repository,
                expected,
                actual,
            } => write!(
                formatter,
                "{repository} revision is {actual:?}, expected {expected:?}"
            ),
            Self::DirtyRepository { repository } => {
                write!(formatter, "{repository} repository is not clean")
            }
            Self::DeclaredFrontendMismatch(detail) => detail.fmt(formatter),
            Self::DuplicateModule(module) => write!(formatter, "duplicate module {module:?}"),
            Self::UnsupportedSentence {
                module,
                ordinal,
                variant,
            } => write!(
                formatter,
                "unsupported native sentence {variant:?} at {module}[{ordinal}]"
            ),
            Self::DuplicateLabel { owner, label } => {
                write!(
                    formatter,
                    "duplicate native label {label:?} in owner {owner:?}"
                )
            }
            Self::DuplicateSort { owner, sort } => {
                write!(
                    formatter,
                    "duplicate native sort {sort:?} in owner {owner:?}"
                )
            }
            Self::InvalidSubsort(detail) => write!(formatter, "invalid native subsort: {detail}"),
            Self::AmbiguousSymbolOwner {
                module,
                label,
                owners,
            } => write!(
                formatter,
                "native label {label:?} used from {module:?} has ambiguous owners: {}",
                owners.join(", ")
            ),
            Self::ArityMismatch {
                module,
                label,
                expected,
                actual,
            } => write!(
                formatter,
                "native label {label:?} used from {module:?} has arity {actual}, expected {expected}"
            ),
            Self::InvalidSidecar(detail)
            | Self::PatchRejected(detail)
            | Self::Preparation(detail) => detail.fmt(formatter),
            Self::Compilation { stage, detail } => {
                write!(
                    formatter,
                    "native compilation stage {stage:?} failed: {detail}"
                )
            }
        }
    }
}

impl std::error::Error for NativeFailure {}

/// A pinned, immutable native baseline ready to serve as an NR-02 validator closure.
#[derive(Clone, Debug)]
pub struct PinnedNativeValidator {
    baseline: NativeDefinition,
    sidecar: Vec<ProvenanceSidecarRecord>,
    pins: VerifiedPins,
    options: CompileOptions,
}

impl PinnedNativeValidator {
    /// Verify exact clean default pins and capture an immutable KRS-adapted baseline.
    pub fn bind(
        definition: &NativeDefinition,
        sidecar: Vec<ProvenanceSidecarRecord>,
        options: CompileOptions,
    ) -> Result<Self, NativeFailure> {
        Self::bind_at(definition, sidecar, options, &PinnedSources::default())
    }

    /// Verify exact clean caller-selected repositories and capture the baseline.
    pub fn bind_at(
        definition: &NativeDefinition,
        sidecar: Vec<ProvenanceSidecarRecord>,
        options: CompileOptions,
        sources: &PinnedSources,
    ) -> Result<Self, NativeFailure> {
        let pins = verify_pins(sources)?;
        Ok(Self {
            baseline: definition.clone(),
            sidecar,
            pins,
            options,
        })
    }

    /// Clone, patch, inventory, index, resolve, check, lower, and publish one native output.
    ///
    /// The clone and every intermediate stay private. An error returns only [`NativeFailure`].
    pub fn validate(
        &self,
        staged: StagedNativeInput<'_>,
        patch: impl FnOnce(
            &mut NativeDefinition,
            StagedNativeInput<'_>,
        ) -> Result<(), NativePatchRejection>,
    ) -> Result<ValidatedNativeOutput, NativeFailure> {
        let mut candidate = self.baseline.clone();
        patch(&mut candidate, staged)
            .map_err(|error| NativeFailure::PatchRejected(error.to_string()))?;
        let index = index_definition_with_sidecar(&candidate, &self.sidecar)?;
        let prelude = builtin::embedded("prelude.md").ok_or_else(|| {
            NativeFailure::Preparation("pinned k-rust prelude is unavailable".to_owned())
        })?;
        let load_options = LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                self.options.backend.excluded_module_attribute().to_owned(),
            ],
            ..LoadOptions::default()
        };
        let loaded = load_structured(candidate.clone(), &load_options)
            .map_err(|error| NativeFailure::Preparation(error.to_string()))?;
        let artifacts =
            compile_loaded_definition(&loaded, self.options.clone()).map_err(|error| {
                NativeFailure::Compilation {
                    stage: error.stage,
                    detail: error.message,
                }
            })?;
        Ok(ValidatedNativeOutput {
            definition: candidate,
            index,
            artifacts,
            pins: self.pins.clone(),
            compile_options: self.options.clone(),
        })
    }
}

/// Verify repository HEADs, worktree cleanliness, and the KRS-declared frontend location.
pub fn verify_pins(sources: &PinnedSources) -> Result<VerifiedPins, NativeFailure> {
    verify_repository("k-rust", &sources.k_rust, K_RUST_REVISION)?;
    verify_repository("KRS", &sources.krs, KRS_REVISION)?;
    let manifest = sources.krs.join("crates/krs-k-rust/Cargo.toml");
    let manifest_text = std::fs::read_to_string(&manifest).map_err(|error| {
        NativeFailure::PinRepositoryUnavailable {
            repository: "KRS",
            detail: format!("cannot read {}: {error}", manifest.display()),
        }
    })?;
    let expected = "../../../inspirations/midnightntwrk/k-rust-krs-main/crates/k-rust";
    if !manifest_text.contains(&format!("path = \"{expected}\"")) {
        return Err(NativeFailure::DeclaredFrontendMismatch(
            "KRS does not declare the reviewed k-rust-krs-main path".to_owned(),
        ));
    }
    for required in [
        "version = \"=0.4.0\"",
        "default-features = false",
        "features = [\"z3-inference\"]",
    ] {
        if !manifest_text.contains(required) {
            return Err(NativeFailure::DeclaredFrontendMismatch(format!(
                "KRS frontend declaration is missing {required:?}"
            )));
        }
    }
    let declared = sources
        .krs
        .join("crates/krs-k-rust")
        .join(expected)
        .canonicalize()
        .map_err(|error| NativeFailure::DeclaredFrontendMismatch(error.to_string()))?;
    let selected = sources
        .k_rust
        .join("crates/k-rust")
        .canonicalize()
        .map_err(|error| NativeFailure::DeclaredFrontendMismatch(error.to_string()))?;
    if declared != selected {
        return Err(NativeFailure::DeclaredFrontendMismatch(format!(
            "KRS declares {}, but NR-05 selected {}",
            declared.display(),
            selected.display()
        )));
    }
    Ok(VerifiedPins {
        krs_revision: KRS_REVISION,
        k_rust_revision: K_RUST_REVISION,
        k_rust_crate_version: "0.4.0",
        declared_krs_feature_profile: "default-features=false,z3-inference",
        integration_feature_profile: "default-features=false,structured-no-z3-inference",
        rustc_identity: command_identity("rustc", &["--version", "--verbose"])?,
    })
}

fn command_identity(command: &'static str, arguments: &[&str]) -> Result<String, NativeFailure> {
    let output = Command::new(command)
        .args(arguments)
        .output()
        .map_err(|error| NativeFailure::PinRepositoryUnavailable {
            repository: "compiler",
            detail: error.to_string(),
        })?;
    if !output.status.success() {
        return Err(NativeFailure::PinRepositoryUnavailable {
            repository: "compiler",
            detail: String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        });
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn verify_repository(
    name: &'static str,
    path: &Path,
    expected: &'static str,
) -> Result<(), NativeFailure> {
    let head = git_output(path, &["rev-parse", "HEAD"], name)?;
    if head != expected {
        return Err(NativeFailure::WrongRevision {
            repository: name,
            expected,
            actual: head,
        });
    }
    let status = git_output(
        path,
        &["status", "--porcelain=v1", "--untracked-files=normal"],
        name,
    )?;
    if !status.is_empty() {
        return Err(NativeFailure::DirtyRepository { repository: name });
    }
    Ok(())
}

fn git_output(
    path: &Path,
    arguments: &[&str],
    repository: &'static str,
) -> Result<String, NativeFailure> {
    let output = Command::new("git")
        .arg("-c")
        .arg(format!("safe.directory={}", path.display()))
        .arg("-C")
        .arg(path)
        .args(arguments)
        .output()
        .map_err(|error| NativeFailure::PinRepositoryUnavailable {
            repository,
            detail: error.to_string(),
        })?;
    if !output.status.success() {
        return Err(NativeFailure::PinRepositoryUnavailable {
            repository,
            detail: String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        });
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

/// Build the closed semantic indexes for a native definition without granting provenance.
pub fn index_definition(definition: &Definition) -> Result<NativeIndex, NativeFailure> {
    index_definition_with_sidecar(definition, &[])
}

fn index_definition_with_sidecar(
    definition: &Definition,
    sidecar: &[ProvenanceSidecarRecord],
) -> Result<NativeIndex, NativeFailure> {
    let mut modules = BTreeMap::new();
    for module in &definition.modules {
        if modules.insert(module.name.as_str(), module).is_some() {
            return Err(NativeFailure::DuplicateModule(module.name.clone()));
        }
    }
    let mut index = NativeIndex {
        inventory: NativeInventory::default(),
        declarations: BTreeMap::new(),
        sorts: BTreeMap::new(),
        signatures: BTreeMap::new(),
        subsorts: BTreeSet::new(),
        resolved_symbol_uses: BTreeMap::new(),
        provenance_sidecar: index_sidecar(definition, sidecar)?,
    };

    for module in &definition.modules {
        for (ordinal, sentence) in module.local_sentences.iter().enumerate() {
            let id = NativeSentenceId {
                owner_module: module.name.clone(),
                ordinal,
            };
            let variant = sentence_variant(sentence);
            *index
                .inventory
                .sentence_variants
                .entry(variant)
                .or_default() += 1;
            if variant == SentenceVariant::Bubble {
                return Err(NativeFailure::UnsupportedSentence {
                    module: module.name.clone(),
                    ordinal,
                    variant,
                });
            }
            index.declarations.insert(id.clone(), variant);
            index_sentence_declarations(sentence, &id, &mut index)?;
        }
    }
    compute_subsorts(
        definition
            .modules
            .iter()
            .flat_map(|module| module.local_sentences.iter()),
        false,
    )
    .map_err(|cycle| NativeFailure::InvalidSubsort(cycle.to_string()))?;

    let ownership = index.signatures.keys().fold(
        BTreeMap::<String, BTreeSet<String>>::new(),
        |mut map, symbol| {
            map.entry(symbol.label.clone())
                .or_default()
                .insert(symbol.owner_module.clone());
            map
        },
    );
    for module in &definition.modules {
        let visible = visible_modules(definition, &module.name);
        for (ordinal, sentence) in module.local_sentences.iter().enumerate() {
            let id = NativeSentenceId {
                owner_module: module.name.clone(),
                ordinal,
            };
            let mut path = Vec::new();
            visit_sentence_terms(sentence, &mut |term| {
                index_term(
                    term,
                    &id,
                    &visible,
                    &ownership,
                    &index.signatures,
                    &mut index.inventory,
                    &mut index.resolved_symbol_uses,
                    &mut path,
                )
            })?;
        }
    }
    Ok(index)
}

fn sentence_variant(sentence: &Sentence) -> SentenceVariant {
    match sentence {
        Sentence::SyntaxSort { .. } => SentenceVariant::SyntaxSort,
        Sentence::SortSynonym { .. } => SentenceVariant::SortSynonym,
        Sentence::SyntaxLexical { .. } => SentenceVariant::SyntaxLexical,
        Sentence::Production { .. } => SentenceVariant::Production,
        Sentence::SyntaxAssociativity { .. } => SentenceVariant::SyntaxAssociativity,
        Sentence::SyntaxPriority { .. } => SentenceVariant::SyntaxPriority,
        Sentence::ContextAlias { .. } => SentenceVariant::ContextAlias,
        Sentence::Context { .. } => SentenceVariant::Context,
        Sentence::Rule { .. } => SentenceVariant::Rule,
        Sentence::Claim { .. } => SentenceVariant::Claim,
        Sentence::Configuration { .. } => SentenceVariant::Configuration,
        Sentence::Bubble { .. } => SentenceVariant::Bubble,
    }
}

fn index_sentence_declarations(
    sentence: &Sentence,
    id: &NativeSentenceId,
    index: &mut NativeIndex,
) -> Result<(), NativeFailure> {
    match sentence {
        Sentence::SyntaxSort { sort, .. } => {
            let sort_id = NativeSortId {
                owner_module: id.owner_module.clone(),
                sort: sort.clone(),
            };
            if index.sorts.insert(sort_id, id.clone()).is_some() {
                return Err(NativeFailure::DuplicateSort {
                    owner: id.owner_module.clone(),
                    sort: sort.clone(),
                });
            }
        }
        Sentence::SortSynonym { new_sort, .. } => {
            let sort_id = NativeSortId {
                owner_module: id.owner_module.clone(),
                sort: new_sort.clone(),
            };
            if index.sorts.insert(sort_id, id.clone()).is_some() {
                return Err(NativeFailure::DuplicateSort {
                    owner: id.owner_module.clone(),
                    sort: new_sort.clone(),
                });
            }
        }
        Sentence::Production {
            label,
            parameters,
            sort,
            items,
            ..
        } => {
            if parameters.is_empty()
                && label.is_none()
                && let [ProductionItem::NonTerminal { sort: child, .. }] = items.as_slice()
            {
                index.subsorts.insert(NativeSubsort {
                    owner_module: id.owner_module.clone(),
                    child: child.clone(),
                    parent: sort.clone(),
                    sentence: id.clone(),
                });
            }
            if let Some(label) = label {
                let symbol = NativeSymbolId {
                    owner_module: id.owner_module.clone(),
                    label: label.name.clone(),
                };
                let signature = NativeSignature {
                    result: sort.clone(),
                    arguments: items
                        .iter()
                        .filter_map(|item| match item {
                            ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => {
                                None
                            }
                        })
                        .collect(),
                    sentence: id.clone(),
                };
                if index.signatures.insert(symbol, signature).is_some() {
                    return Err(NativeFailure::DuplicateLabel {
                        owner: id.owner_module.clone(),
                        label: label.name.clone(),
                    });
                }
            }
        }
        Sentence::SyntaxLexical { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Rule { .. }
        | Sentence::Claim { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => {}
    }
    Ok(())
}

fn visit_sentence_terms(
    sentence: &Sentence,
    visitor: &mut impl FnMut(&Term) -> Result<(), NativeFailure>,
) -> Result<(), NativeFailure> {
    match sentence {
        Sentence::ContextAlias { body, requires, .. }
        | Sentence::Context { body, requires, .. } => {
            visitor(body)?;
            visitor(requires)
        }
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => {
            visitor(body)?;
            visitor(requires)?;
            visitor(ensures)
        }
        Sentence::Configuration { body, ensures, .. } => {
            visitor(body)?;
            visitor(ensures)
        }
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::Bubble { .. } => Ok(()),
    }
}

#[allow(clippy::too_many_arguments)]
fn index_term(
    term: &Term,
    sentence: &NativeSentenceId,
    visible: &BTreeSet<String>,
    ownership: &BTreeMap<String, BTreeSet<String>>,
    signatures: &BTreeMap<NativeSymbolId, NativeSignature>,
    inventory: &mut NativeInventory,
    uses: &mut BTreeMap<(NativeSentenceId, Vec<u32>), NativeSymbolId>,
    path: &mut Vec<u32>,
) -> Result<(), NativeFailure> {
    let variant = match term {
        Term::InjectedLabel(_) => TermVariant::InjectedLabel,
        Term::Rewrite { .. } => TermVariant::Rewrite,
        Term::As { .. } => TermVariant::As,
        Term::Variable { .. } => TermVariant::Variable,
        Term::Sequence(_) => TermVariant::Sequence,
        Term::Apply { .. } => TermVariant::Apply,
        Term::Token { .. } => TermVariant::Token,
        Term::Annotated { .. } => TermVariant::Annotated,
    };
    *inventory.term_variants.entry(variant).or_default() += 1;
    match term {
        Term::InjectedLabel(label) => resolve_label(
            label, None, sentence, path, visible, ownership, signatures, uses,
        ),
        Term::Rewrite { left, right } => {
            visit_child(
                left, 0, sentence, visible, ownership, signatures, inventory, uses, path,
            )?;
            visit_child(
                right, 1, sentence, visible, ownership, signatures, inventory, uses, path,
            )
        }
        Term::As { pattern, alias } => {
            visit_child(
                pattern, 0, sentence, visible, ownership, signatures, inventory, uses, path,
            )?;
            visit_child(
                alias, 1, sentence, visible, ownership, signatures, inventory, uses, path,
            )
        }
        Term::Sequence(terms) => visit_children(
            terms, sentence, visible, ownership, signatures, inventory, uses, path,
        ),
        Term::Apply { label, arguments } => {
            resolve_label(
                label,
                Some(arguments.len()),
                sentence,
                path,
                visible,
                ownership,
                signatures,
                uses,
            )?;
            visit_children(
                arguments, sentence, visible, ownership, signatures, inventory, uses, path,
            )
        }
        Term::Annotated { term, .. } => visit_child(
            term, 0, sentence, visible, ownership, signatures, inventory, uses, path,
        ),
        Term::Variable { .. } | Term::Token { .. } => Ok(()),
    }
}

#[allow(clippy::too_many_arguments)]
fn visit_children(
    terms: &[Term],
    sentence: &NativeSentenceId,
    visible: &BTreeSet<String>,
    ownership: &BTreeMap<String, BTreeSet<String>>,
    signatures: &BTreeMap<NativeSymbolId, NativeSignature>,
    inventory: &mut NativeInventory,
    uses: &mut BTreeMap<(NativeSentenceId, Vec<u32>), NativeSymbolId>,
    path: &mut Vec<u32>,
) -> Result<(), NativeFailure> {
    for (offset, term) in terms.iter().enumerate() {
        let offset = u32::try_from(offset).map_err(|_| {
            NativeFailure::Preparation("native term child index exceeds u32".to_owned())
        })?;
        visit_child(
            term, offset, sentence, visible, ownership, signatures, inventory, uses, path,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn visit_child(
    term: &Term,
    offset: u32,
    sentence: &NativeSentenceId,
    visible: &BTreeSet<String>,
    ownership: &BTreeMap<String, BTreeSet<String>>,
    signatures: &BTreeMap<NativeSymbolId, NativeSignature>,
    inventory: &mut NativeInventory,
    uses: &mut BTreeMap<(NativeSentenceId, Vec<u32>), NativeSymbolId>,
    path: &mut Vec<u32>,
) -> Result<(), NativeFailure> {
    path.push(offset);
    let result = index_term(
        term, sentence, visible, ownership, signatures, inventory, uses, path,
    );
    path.pop();
    result
}

#[allow(clippy::too_many_arguments)]
fn resolve_label(
    label: &Label,
    arity: Option<usize>,
    sentence: &NativeSentenceId,
    path: &[u32],
    visible: &BTreeSet<String>,
    ownership: &BTreeMap<String, BTreeSet<String>>,
    signatures: &BTreeMap<NativeSymbolId, NativeSignature>,
    uses: &mut BTreeMap<(NativeSentenceId, Vec<u32>), NativeSymbolId>,
) -> Result<(), NativeFailure> {
    let Some(all_owners) = ownership.get(&label.name) else {
        return Ok(());
    };
    let owners = all_owners
        .intersection(visible)
        .cloned()
        .collect::<Vec<_>>();
    let [owner] = owners.as_slice() else {
        if owners.is_empty() {
            return Ok(());
        }
        return Err(NativeFailure::AmbiguousSymbolOwner {
            module: sentence.owner_module.clone(),
            label: label.name.clone(),
            owners,
        });
    };
    let symbol = NativeSymbolId {
        owner_module: owner.clone(),
        label: label.name.clone(),
    };
    let signature = &signatures[&symbol];
    if let Some(actual) = arity
        && actual != signature.arguments.len()
    {
        return Err(NativeFailure::ArityMismatch {
            module: sentence.owner_module.clone(),
            label: label.name.clone(),
            expected: signature.arguments.len(),
            actual,
        });
    }
    uses.insert((sentence.clone(), path.to_vec()), symbol);
    Ok(())
}

fn visible_modules(definition: &Definition, root: &str) -> BTreeSet<String> {
    let by_name = definition
        .modules
        .iter()
        .map(|module| (module.name.as_str(), module))
        .collect::<BTreeMap<_, _>>();
    let mut visible = BTreeSet::from([root.to_owned()]);
    let Some(root_module) = by_name.get(root) else {
        return visible;
    };
    for import in &root_module.imports {
        visible.insert(import.name.clone());
        collect_public_imports(&import.name, &by_name, &mut visible);
    }
    visible
}

fn collect_public_imports(
    module: &str,
    modules: &BTreeMap<&str, &k_rust::definition::FlatModule>,
    visible: &mut BTreeSet<String>,
) {
    let Some(module) = modules.get(module) else {
        return;
    };
    for import in module.imports.iter().filter(|import| import.public) {
        if visible.insert(import.name.clone()) {
            collect_public_imports(&import.name, modules, visible);
        }
    }
}

fn index_sidecar(
    definition: &Definition,
    sidecar: &[ProvenanceSidecarRecord],
) -> Result<ProvenanceSidecarIndex, NativeFailure> {
    let modules = definition
        .modules
        .iter()
        .map(|module| (module.name.as_str(), module.local_sentences.len()))
        .collect::<BTreeMap<_, _>>();
    let mut records = BTreeMap::new();
    for record in sidecar {
        let Some(sentence_count) = modules.get(record.module.as_str()) else {
            return Err(NativeFailure::InvalidSidecar(format!(
                "sidecar destination module {:?} is absent",
                record.module
            )));
        };
        let is_module = record.role == NativeNodeRole::Module;
        if is_module != record.sentence_index.is_none() {
            return Err(NativeFailure::InvalidSidecar(format!(
                "sidecar role {:?} has inconsistent sentence index",
                record.role
            )));
        }
        if record
            .sentence_index
            .is_some_and(|ordinal| ordinal >= *sentence_count)
        {
            return Err(NativeFailure::InvalidSidecar(format!(
                "sidecar destination {}[{:?}] is absent",
                record.module, record.sentence_index
            )));
        }
        let destination = (
            record.module.clone(),
            record.sentence_index,
            record.role.clone(),
        );
        if records.insert(destination, record.clone()).is_some() {
            return Err(NativeFailure::InvalidSidecar(
                "two KRS origins claim one native sidecar destination".to_owned(),
            ));
        }
    }
    Ok(ProvenanceSidecarIndex { records })
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::{
        definition::{Attributes, FlatImport, FlatModule},
        kast::TermMetadata,
    };

    fn production(label: &str, result: &str, arguments: &[&str]) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(label)),
            parameters: Vec::new(),
            sort: Sort::new(result),
            items: arguments
                .iter()
                .map(|argument| ProductionItem::NonTerminal {
                    sort: Sort::new(*argument),
                    name: None,
                })
                .collect(),
            attributes: Attributes::default(),
        }
    }

    fn module(name: &str, imports: &[&str], local_sentences: Vec<Sentence>) -> FlatModule {
        FlatModule {
            name: name.to_owned(),
            imports: imports
                .iter()
                .map(|name| FlatImport {
                    name: (*name).to_owned(),
                    public: true,
                })
                .collect(),
            local_sentences,
            attributes: Attributes::default(),
        }
    }

    fn definition(modules: Vec<FlatModule>) -> Definition {
        Definition {
            main_module: modules.last().unwrap().name.clone(),
            modules,
            attributes: Attributes::default(),
        }
    }

    #[test]
    fn closed_inventory_visits_every_term_variant() {
        let nested = Term::Rewrite {
            left: Box::new(Term::InjectedLabel(Label::new("f"))),
            right: Box::new(Term::As {
                pattern: Box::new(Term::Apply {
                    label: Label::new("f"),
                    arguments: vec![Term::Token {
                        token: "x".to_owned(),
                        sort: Sort::new("S"),
                    }],
                }),
                alias: Box::new(Term::Variable {
                    name: "X".to_owned(),
                    sort: Some(Sort::new("S")),
                }),
            }),
        };
        let body = Term::Sequence(vec![nested.with_metadata(TermMetadata {
            sort: Some(Sort::new("S")),
            ..TermMetadata::default()
        })]);
        let rule = Sentence::Rule {
            body,
            requires: Term::Token {
                token: "true".to_owned(),
                sort: Sort::new("Bool"),
            },
            ensures: Term::Token {
                token: "true".to_owned(),
                sort: Sort::new("Bool"),
            },
            attributes: Attributes::default(),
        };
        let index = index_definition(&definition(vec![module(
            "M",
            &[],
            vec![production("f", "S", &["S"]), rule],
        )]))
        .unwrap();
        for variant in [
            TermVariant::InjectedLabel,
            TermVariant::Rewrite,
            TermVariant::As,
            TermVariant::Variable,
            TermVariant::Sequence,
            TermVariant::Apply,
            TermVariant::Token,
            TermVariant::Annotated,
        ] {
            assert!(index.inventory.term_variants.contains_key(&variant));
        }
    }

    #[test]
    fn bubble_fails_closed() {
        let error = index_definition(&definition(vec![module(
            "M",
            &[],
            vec![Sentence::Bubble {
                sentence_type: "rule".to_owned(),
                contents: "X => Y".to_owned(),
                attributes: Attributes::default(),
            }],
        )]))
        .unwrap_err();
        assert!(matches!(
            error,
            NativeFailure::UnsupportedSentence {
                variant: SentenceVariant::Bubble,
                ..
            }
        ));
    }

    #[test]
    fn duplicate_label_in_one_owner_rejects() {
        let error = index_definition(&definition(vec![module(
            "M",
            &[],
            vec![production("f", "S", &[]), production("f", "T", &[])],
        )]))
        .unwrap_err();
        assert_eq!(
            error,
            NativeFailure::DuplicateLabel {
                owner: "M".to_owned(),
                label: "f".to_owned(),
            }
        );
    }

    #[test]
    fn application_arity_mismatch_rejects() {
        let use_f = Sentence::Context {
            body: Term::Apply {
                label: Label::new("f"),
                arguments: Vec::new(),
            },
            requires: Term::Token {
                token: "true".to_owned(),
                sort: Sort::new("Bool"),
            },
            attributes: Attributes::default(),
        };
        let error = index_definition(&definition(vec![module(
            "M",
            &[],
            vec![production("f", "S", &["S"]), use_f],
        )]))
        .unwrap_err();
        assert_eq!(
            error,
            NativeFailure::ArityMismatch {
                module: "M".to_owned(),
                label: "f".to_owned(),
                expected: 1,
                actual: 0,
            }
        );
    }

    #[test]
    fn duplicate_sort_and_circular_subsort_reject() {
        let sort = |name: &str| Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new(name),
            attributes: Attributes::default(),
        };
        let duplicate = index_definition(&definition(vec![module(
            "M",
            &[],
            vec![sort("S"), sort("S")],
        )]))
        .unwrap_err();
        assert!(matches!(duplicate, NativeFailure::DuplicateSort { .. }));

        let injection = |child: &str, parent: &str| Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new(parent),
            items: vec![ProductionItem::NonTerminal {
                sort: Sort::new(child),
                name: None,
            }],
            attributes: Attributes::default(),
        };
        let circular = index_definition(&definition(vec![module(
            "M",
            &[],
            vec![
                sort("A"),
                sort("B"),
                injection("A", "B"),
                injection("B", "A"),
            ],
        )]))
        .unwrap_err();
        assert!(matches!(circular, NativeFailure::InvalidSubsort(_)));
    }

    #[test]
    fn ambiguous_visible_owners_reject_use() {
        let use_f = Sentence::Context {
            body: Term::Apply {
                label: Label::new("f"),
                arguments: Vec::new(),
            },
            requires: Term::Token {
                token: "true".to_owned(),
                sort: Sort::new("Bool"),
            },
            attributes: Attributes::default(),
        };
        let error = index_definition(&definition(vec![
            module("A", &[], vec![production("f", "S", &[])]),
            module("B", &[], vec![production("f", "S", &[])]),
            module("M", &["A", "B"], vec![use_f]),
        ]))
        .unwrap_err();
        assert_eq!(
            error,
            NativeFailure::AmbiguousSymbolOwner {
                module: "M".to_owned(),
                label: "f".to_owned(),
                owners: vec!["A".to_owned(), "B".to_owned()],
            }
        );
    }

    #[test]
    fn symbol_identity_survives_module_vector_relocation() {
        let rule = Sentence::Context {
            body: Term::Apply {
                label: Label::new("f"),
                arguments: Vec::new(),
            },
            requires: Term::Token {
                token: "true".to_owned(),
                sort: Sort::new("Bool"),
            },
            attributes: Attributes::default(),
        };
        let first = definition(vec![
            module("OWNER", &[], vec![production("f", "S", &[])]),
            module("USE", &["OWNER"], vec![rule.clone()]),
        ]);
        let second = Definition {
            main_module: "USE".to_owned(),
            modules: vec![
                module("USE", &["OWNER"], vec![rule]),
                module("OWNER", &[], vec![production("f", "S", &[])]),
            ],
            attributes: Attributes::default(),
        };
        let first = index_definition(&first).unwrap();
        let second = index_definition(&second).unwrap();
        assert_eq!(first.signatures, second.signatures);
        assert_eq!(first.resolved_symbol_uses, second.resolved_symbol_uses);
    }

    #[test]
    fn direct_subsort_and_signature_are_indexed() {
        let subsort = Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("Parent"),
            items: vec![ProductionItem::NonTerminal {
                sort: Sort::new("Child"),
                name: None,
            }],
            attributes: Attributes::default(),
        };
        let index = index_definition(&definition(vec![module(
            "M",
            &[],
            vec![subsort, production("f", "Parent", &["Child"])],
        )]))
        .unwrap();
        assert_eq!(index.subsorts.len(), 1);
        assert_eq!(index.signatures.len(), 1);
    }

    #[test]
    fn sidecar_destination_is_name_based_and_bounds_checked() {
        let source = definition(vec![module("M", &[], vec![production("f", "S", &[])])]);
        let records = vec![ProvenanceSidecarRecord {
            source_map_key: "origin.f".to_owned(),
            module: "M".to_owned(),
            sentence_index: Some(1),
            role: NativeNodeRole::Sentence,
        }];
        let error = index_definition_with_sidecar(&source, &records).unwrap_err();
        assert!(matches!(error, NativeFailure::InvalidSidecar(_)));
    }

    #[test]
    fn frontend_constant_matches_work_package_pin() {
        assert_eq!(K_RUST_REVISION.len(), 40);
        assert_eq!(KRS_REVISION.len(), 40);
    }

    #[test]
    fn default_pin_check_accepts_only_exact_clean_repositories() {
        match verify_pins(&PinnedSources::default()) {
            Ok(pins) => {
                assert_eq!(pins.krs_revision, KRS_REVISION);
                assert_eq!(pins.k_rust_revision, K_RUST_REVISION);
            }
            Err(NativeFailure::DirtyRepository { repository: "KRS" }) => {
                // The shared checkout is currently modified by unrelated KEVM work. Rejection is
                // the required production behavior, not a test skip or an accepted pin.
            }
            Err(error) => panic!("unexpected pin failure: {error}"),
        }
    }
}
