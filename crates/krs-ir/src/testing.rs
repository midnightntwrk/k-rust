//! Shared identity and provenance fixtures for IR tests.

#[cfg(feature = "test-support")]
use std::fmt::Debug;

#[cfg(feature = "test-support")]
use serde::de::DeserializeOwned;

#[cfg(feature = "test-support")]
use crate::{DefinitionIr, DescriptorBundle, SemanticTheory};
use crate::{
    ItemKind, NodeOrigin, OriginStack, PackageId, Sha256Digest, SourceFileId, SourceMapKey,
    SourceRange, StableItemId,
};

/// An IR root whose canonical JSON must be independent of set input order.
#[cfg(feature = "test-support")]
pub trait CanonicalContract: Debug + Eq + DeserializeOwned {
    /// Rebuilds every set-like collection through its validating constructor.
    #[must_use]
    fn permute_sets(&self, seed: u64) -> Self;

    /// Returns the root's canonical JSON encoding.
    ///
    /// # Errors
    ///
    /// Returns an error if JSON encoding fails.
    fn to_canonical_json(&self) -> serde_json::Result<String>;
}

#[cfg(feature = "test-support")]
impl CanonicalContract for DescriptorBundle {
    fn permute_sets(&self, seed: u64) -> Self {
        Self::permute_sets(self, seed)
    }

    fn to_canonical_json(&self) -> serde_json::Result<String> {
        Self::to_canonical_json(self)
    }
}

#[cfg(feature = "test-support")]
impl CanonicalContract for SemanticTheory {
    fn permute_sets(&self, seed: u64) -> Self {
        Self::permute_sets(self, seed)
    }

    fn to_canonical_json(&self) -> serde_json::Result<String> {
        Self::to_canonical_json(self)
    }
}

#[cfg(feature = "test-support")]
impl CanonicalContract for DefinitionIr {
    fn permute_sets(&self, seed: u64) -> Self {
        Self::permute_sets(self, seed)
    }

    fn to_canonical_json(&self) -> serde_json::Result<String> {
        Self::to_canonical_json(self)
    }
}

/// Asserts order independence and validating JSON round trips for an IR root.
///
/// # Panics
///
/// Panics when permutation changes canonical JSON, deserialization fails, or
/// decoding changes the canonical value.
#[cfg(feature = "test-support")]
pub fn assert_canonical_contract<T: CanonicalContract>(value: &T) {
    let name = std::any::type_name::<T>();
    let canonical = value
        .to_canonical_json()
        .unwrap_or_else(|error| panic!("{name} seed 0: canonical encoding failed: {error}"));
    for seed in 0..8 {
        let permuted = value.permute_sets(seed);
        let permuted_json = permuted.to_canonical_json().unwrap_or_else(|error| {
            panic!("{name} seed {seed}: permuted encoding failed: {error}")
        });
        assert_eq!(
            permuted_json, canonical,
            "{name} seed {seed}: set permutation changed canonical JSON"
        );
        let decoded = serde_json::from_str::<T>(&canonical).unwrap_or_else(|error| {
            panic!("{name} seed {seed}: canonical decoding failed: {error}")
        });
        let decoded_json = decoded
            .to_canonical_json()
            .unwrap_or_else(|error| panic!("{name} seed {seed}: decoded encoding failed: {error}"));
        assert_eq!(
            decoded_json, canonical,
            "{name} seed {seed}: decoded canonical JSON changed"
        );
        assert_eq!(decoded, *value, "{name} seed {seed}: decoded value changed");
    }
}

/// Permutes a set input deterministically; seed zero reverses it.
#[cfg(feature = "test-support")]
pub(crate) fn permute<T>(values: &mut [T], seed: u64) {
    if seed == 0 {
        values.reverse();
        return;
    }
    let mut state = seed;
    for index in (1..values.len()).rev() {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let bound = u64::try_from(index + 1).expect("set input length fits in u64");
        let swap_index = usize::try_from(state % bound).expect("index fits in usize");
        values.swap(index, swap_index);
    }
}

/// Returns the package used by the smoke IR fixtures.
#[must_use]
pub fn smoke_package() -> PackageId {
    package("ORG-EXAMPLE-SMOKE", "smoke-semantics")
}

/// Returns a workspace package with the fixture version `0.1.0`.
#[must_use]
pub fn package(namespace: &str, name: &str) -> PackageId {
    package_with(namespace, name, "0.1.0", "workspace")
}

/// Returns a package with explicit identity components.
///
/// # Panics
///
/// Panics if the package components are invalid.
#[must_use]
pub fn package_with(namespace: &str, name: &str, version: &str, source: &str) -> PackageId {
    PackageId::new(namespace, name, version, source).expect("valid fixture package")
}

/// Returns a stable item in the smoke package.
#[must_use]
pub fn item(module: &str, name: &str, kind: ItemKind) -> StableItemId {
    item_in(smoke_package(), module, name, kind)
}

/// Returns a stable item in the specified package and module.
///
/// # Panics
///
/// Panics if the item components are invalid.
#[must_use]
pub fn item_in(package: PackageId, module: &str, name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(package, [module], name, kind, "").expect("valid fixture item")
}

/// Returns the fixed digest used by the smoke IR fixtures.
#[must_use]
pub fn digest() -> Sha256Digest {
    digest_with("0123456789abcdef".repeat(4))
}

/// Returns a digest from an explicit hexadecimal fixture value.
///
/// # Panics
///
/// Panics if the value is not a SHA-256 digest.
#[must_use]
pub fn digest_with(hex: impl Into<String>) -> Sha256Digest {
    Sha256Digest::new(hex.into()).expect("valid fixture digest")
}

/// Returns a smoke-source authored origin stack for the given byte range.
#[must_use]
pub fn authored(start: u32, end: u32) -> OriginStack {
    authored_in(smoke_package(), "src/lib.rs", digest(), start, end)
}

/// Returns an authored origin stack for an explicit source identity and byte range.
///
/// # Panics
///
/// Panics if the source path or byte range is invalid.
#[must_use]
pub fn authored_in(
    package: PackageId,
    path: &str,
    digest: Sha256Digest,
    start: u32,
    end: u32,
) -> OriginStack {
    let file = SourceFileId::new(package, path, digest).expect("valid fixture source file");
    OriginStack::authored(SourceRange::new(file, start, end).expect("valid fixture source range"))
}

/// Returns a node origin in the smoke source at bytes 0 through 3.
///
/// # Panics
///
/// Panics if the source-map key is invalid.
#[must_use]
pub fn origin(key: &str) -> NodeOrigin {
    NodeOrigin::new(
        SourceMapKey::new(key).expect("valid fixture key"),
        authored(0, 3),
    )
}

/// Returns a node origin with explicit source identity and byte range.
///
/// # Panics
///
/// Panics if the source-map key, source path, or byte range is invalid.
#[must_use]
pub fn origin_in(
    key: &str,
    package: PackageId,
    path: &str,
    digest: Sha256Digest,
    start: u32,
    end: u32,
) -> NodeOrigin {
    NodeOrigin::new(
        SourceMapKey::new(key).expect("valid fixture key"),
        authored_in(package, path, digest, start, end),
    )
}

/// Creates a descriptor fixture through its validating constructor.
///
/// # Panics
///
/// Panics if the fixture violates a descriptor contract.
#[must_use]
pub fn descriptor(
    id: StableItemId,
    cfg: std::collections::BTreeMap<String, Option<String>>,
    provenance: crate::DescriptorProvenance,
    payload: crate::DescriptorPayload,
) -> crate::Descriptor {
    crate::Descriptor::new(id, cfg, provenance, payload).expect("valid descriptor fixture")
}

/// Editable constructor inputs for descriptor boundary tests.
#[derive(Clone, Debug, serde::Serialize)]
pub struct DescriptorInputs {
    /// Stable identity to validate.
    pub id: StableItemId,
    /// Enabled configuration keys.
    pub cfg: std::collections::BTreeMap<String, Option<String>>,
    /// Parser-keyed provenance to validate.
    pub provenance: crate::DescriptorProvenance,
    /// Declaration payload to validate.
    #[serde(flatten)]
    pub payload: crate::DescriptorPayload,
}

impl DescriptorInputs {
    /// Collects inputs without creating a descriptor.
    #[must_use]
    pub const fn new(
        id: StableItemId,
        cfg: std::collections::BTreeMap<String, Option<String>>,
        provenance: crate::DescriptorProvenance,
        payload: crate::DescriptorPayload,
    ) -> Self {
        Self {
            id,
            cfg,
            provenance,
            payload,
        }
    }

    /// Validates these inputs through the descriptor constructor.
    ///
    /// # Errors
    ///
    /// Returns the violated descriptor contract.
    pub fn build(&self) -> Result<crate::Descriptor, crate::DescriptorError> {
        crate::Descriptor::new(
            self.id.clone(),
            self.cfg.clone(),
            self.provenance.clone(),
            self.payload.clone(),
        )
    }
}

impl From<crate::Descriptor> for DescriptorInputs {
    fn from(descriptor: crate::Descriptor) -> Self {
        Self::new(
            descriptor.id().clone(),
            descriptor.cfg().clone(),
            descriptor.provenance().clone(),
            descriptor.payload().clone(),
        )
    }
}

/// Builds descriptor inputs and their inherited declaration metadata.
///
/// # Errors
///
/// Rejects invalid descriptor or bundle contracts.
pub fn descriptor_bundle(
    inputs: Vec<DescriptorInputs>,
) -> serde_json::Result<crate::DescriptorBundle> {
    let descriptors = inputs
        .into_iter()
        .map(|input| crate::Descriptor::new(input.id, input.cfg, input.provenance, input.payload))
        .collect::<Result<Vec<_>, _>>()
        .map_err(serde::de::Error::custom)?;
    crate::DescriptorBundle::new(descriptors).map_err(serde::de::Error::custom)
}

/// Editable bundle inputs for constructor and compiler boundary tests.
#[derive(Clone, Debug)]
pub struct DescriptorBundleInputs {
    /// Descriptor constructor inputs in test order.
    pub descriptors: Vec<DescriptorInputs>,
    /// Exact metadata overrides for descriptor identities.
    pub declarations: Vec<crate::DescriptorDeclaration>,
}

impl DescriptorBundleInputs {
    /// Collects descriptor inputs with inherited declaration metadata.
    #[must_use]
    pub const fn new(descriptors: Vec<DescriptorInputs>) -> Self {
        Self {
            descriptors,
            declarations: Vec::new(),
        }
    }

    /// Builds the descriptors and validates bundle-wide contracts.
    ///
    /// # Errors
    ///
    /// Rejects invalid descriptor or bundle contracts.
    pub fn build(&self) -> serde_json::Result<crate::DescriptorBundle> {
        let descriptors = self
            .descriptors
            .iter()
            .map(DescriptorInputs::build)
            .collect::<Result<Vec<_>, _>>()
            .map_err(serde::de::Error::custom)?;
        let mut declarations = descriptors
            .iter()
            .map(|descriptor| {
                (
                    descriptor.id().clone(),
                    crate::DescriptorDeclaration::new(
                        descriptor.id().clone(),
                        crate::RustVisibility::Inherited,
                        None,
                    ),
                )
            })
            .collect::<std::collections::BTreeMap<_, _>>();
        for declaration in &self.declarations {
            declarations.insert(declaration.id().clone(), declaration.clone());
        }
        crate::DescriptorBundle::with_declarations(
            descriptors,
            declarations.into_values().collect(),
        )
        .map_err(serde::de::Error::custom)
    }
}
