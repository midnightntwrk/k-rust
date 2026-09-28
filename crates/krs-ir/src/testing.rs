//! Shared identity and provenance fixtures for IR tests.

use crate::{
    ItemKind, NodeOrigin, OriginStack, PackageId, Sha256Digest, SourceFileId, SourceMapKey,
    SourceRange, StableItemId,
};

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
