//! Decodes literal source coordinates emitted by KRS macros.

use crate::{HostProvenance, HostProvenanceError};

#[doc(hidden)]
pub use krs_ir::{HostRawAnchor as __KrsRawAnchor, HostRawProvenance as __KrsRawProvenance};

/// Builds the validated provenance for one generated descriptor factory.
///
/// The factory constructs `provenance` in a `const` block, which checks every
/// fact that does not depend on the build machine at compile time.
///
/// # Errors
///
/// Returns [`HostProvenanceError`] when an absolute display filename cannot be validated relative to the Cargo manifest directory.
#[doc(hidden)]
#[inline(never)]
pub fn __krs_host_provenance(
    manifest_dir: &str,
    provenance: &__KrsRawProvenance,
) -> Result<HostProvenance, HostProvenanceError> {
    provenance.decode(manifest_dir)
}
