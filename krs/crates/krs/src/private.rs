//! Implementation details used by generated registration expansions.
//!
//! No item in this module is a stable author-facing API. It is public only
//! because a macro expanded in a downstream crate must be able to name it.

use super::{HostDescriptor, HostProvenanceError};

#[cfg(feature = "inventory")]
#[doc(hidden)]
pub use inventory;

/// One semantics crate's explicit registration table.
///
/// A whole-crate step emits this as the crate-root
/// `__KRS_REGISTRATIONS` static. `register` pushes every factory under
/// the `#[cfg]` attributes of the item that defines it.
#[doc(hidden)]
pub struct RegistrationTable {
    /// Whether any `sorts!` in the crate names `KItem` or `KResult`.
    pub requests_framework: bool,
    /// Pushes each descriptor factory of the crate.
    pub register: fn(&mut Registrar),
}

/// Accumulates descriptor factories from explicit registration tables.
#[doc(hidden)]
#[derive(Default)]
pub struct Registrar {
    factories: Vec<fn() -> Result<HostDescriptor, HostProvenanceError>>,
}

impl Registrar {
    /// Records one descriptor factory.
    #[doc(hidden)]
    pub fn factory(&mut self, factory: fn() -> Result<HostDescriptor, HostProvenanceError>) {
        self.factories.push(factory);
    }

    pub(crate) fn into_factories(self) -> Vec<fn() -> Result<HostDescriptor, HostProvenanceError>> {
        self.factories
    }
}

/// One process-local registration entry.
#[cfg(feature = "inventory")]
#[doc(hidden)]
pub struct HostRegistration {
    factory: fn() -> Result<HostDescriptor, HostProvenanceError>,
    path: &'static str,
    manifest_dir: &'static str,
}

#[cfg(feature = "inventory")]
impl HostRegistration {
    /// Creates an entry around a descriptor factory, its
    /// `module_path!()`-qualified path, and its crate's manifest
    /// directory.
    #[doc(hidden)]
    #[must_use]
    pub const fn new(
        factory: fn() -> Result<HostDescriptor, HostProvenanceError>,
        path: &'static str,
        manifest_dir: &'static str,
    ) -> Self {
        Self {
            factory,
            path,
            manifest_dir,
        }
    }

    pub(crate) fn make(&self) -> Result<HostDescriptor, HostProvenanceError> {
        (self.factory)()
    }
}

/// One downstream request for the framework sort descriptor pair.
#[cfg(feature = "inventory")]
#[doc(hidden)]
pub struct FrameworkSortRequest {
    manifest_dir: &'static str,
}

#[cfg(feature = "inventory")]
impl FrameworkSortRequest {
    /// Captures the requesting definition's manifest directory.
    #[doc(hidden)]
    #[must_use]
    pub const fn new(manifest_dir: &'static str) -> Self {
        Self { manifest_dir }
    }

    pub(crate) const fn manifest_dir(&self) -> &'static str {
        self.manifest_dir
    }
}

/// One linked factory as recorded by the inventory registration.
#[cfg(feature = "inventory")]
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CensusRegistration {
    /// `module_path!()`-qualified factory path.
    pub path: &'static str,
    /// `CARGO_MANIFEST_DIR` of the registering crate.
    pub manifest_dir: &'static str,
}

/// Every inventory registration linked into this process.
///
/// This is test support for generating and checking explicit
/// registration tables; it never enters a descriptor bundle.
#[cfg(feature = "inventory")]
#[doc(hidden)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegistrationCensus {
    /// Registered factories, sorted.
    pub registrations: Vec<CensusRegistration>,
    /// Manifest directories that requested the framework sorts, sorted
    /// and deduplicated.
    pub framework_requests: Vec<&'static str>,
}

/// Lists every linked registration and framework-sort request.
#[cfg(feature = "inventory")]
#[doc(hidden)]
#[must_use]
pub fn registration_census() -> RegistrationCensus {
    let mut registrations = inventory::iter::<HostRegistration>
        .into_iter()
        .map(|registration| CensusRegistration {
            path: registration.path,
            manifest_dir: registration.manifest_dir,
        })
        .collect::<Vec<_>>();
    registrations.sort_unstable();
    let mut framework_requests = inventory::iter::<FrameworkSortRequest>
        .into_iter()
        .map(FrameworkSortRequest::manifest_dir)
        .collect::<Vec<_>>();
    framework_requests.sort_unstable();
    framework_requests.dedup();
    RegistrationCensus {
        registrations,
        framework_requests,
    }
}

#[cfg(feature = "inventory")]
inventory::collect!(HostRegistration);
#[cfg(feature = "inventory")]
inventory::collect!(FrameworkSortRequest);
