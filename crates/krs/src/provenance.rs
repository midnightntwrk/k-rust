//! Decodes literal source coordinates emitted by KRS macros.

use crate::{
    AnchorPrecision, HostAuthoredAnchor, HostProvenance, HostProvenanceError, HostSourceAnchor,
    HostSourcePosition, ProvenanceKey, ProvenanceRole,
};
use krs_ir::DisplayPath;

/// Literal source coordinates emitted by KRS macros.
#[doc(hidden)]
#[derive(Clone, Copy)]
pub struct __KrsRawAnchor {
    pub file: usize,
    pub absolute: bool,
    pub start: (u32, u32),
    pub end: (u32, u32),
    pub exact: bool,
}

/// Builds the validated provenance for one generated descriptor factory.
///
/// # Errors
///
/// Returns [`HostProvenanceError::SourceOutsidePackage`] when a display filename cannot be validated relative to the Cargo manifest directory.
#[doc(hidden)]
#[inline(never)]
#[track_caller]
pub fn __krs_host_provenance(
    manifest_dir: &str,
    files: &[&str],
    invocation: __KrsRawAnchor,
    authored: &[(ProvenanceRole, u32, __KrsRawAnchor)],
) -> Result<HostProvenance, HostProvenanceError> {
    let invocation_file = files[invocation.file];
    let invocation_start = HostSourcePosition::new(invocation.start.0, invocation.start.1)
        .expect("stable proc-macro positions are one-based");
    let mut resolved: Vec<Option<String>> = vec![None; files.len()];
    macro_rules! source_anchor {
        ($raw:expr) => {{
            let raw: __KrsRawAnchor = $raw;
            let outside_package = |path_error| HostProvenanceError::SourceOutsidePackage {
                invocation_file: invocation_file.to_owned(),
                invocation_start,
                display_file: files[raw.file].to_owned(),
                manifest_dir: manifest_dir.to_owned(),
                path_error,
            };
            let file = if raw.absolute {
                match &resolved[raw.file] {
                    Some(file) => file.clone(),
                    None => {
                        let source = std::path::Path::new(files[raw.file]);
                        let manifest = std::path::Path::new(manifest_dir);
                        let relative = source
                            .strip_prefix(manifest)
                            .map_err(|_| outside_package(None))?
                            .to_string_lossy();
                        let file = DisplayPath::new(relative.as_ref())
                            .map_err(|error| outside_package(Some(Box::new(error))))?
                            .as_str()
                            .to_owned();
                        resolved[raw.file] = Some(file.clone());
                        file
                    }
                }
            } else {
                files[raw.file].to_owned()
            };
            HostSourceAnchor::new(
                file,
                HostSourcePosition::new(raw.start.0, raw.start.1)
                    .expect("stable proc-macro positions are one-based"),
                HostSourcePosition::new(raw.end.0, raw.end.1)
                    .expect("stable proc-macro positions are one-based"),
                if raw.exact {
                    AnchorPrecision::Exact
                } else {
                    AnchorPrecision::InvocationFallback
                },
            )
            .expect("KRS emits ordered, non-absolute display anchors")
        }};
    }
    let invocation = source_anchor!(invocation);
    let mut decoded_authored = Vec::with_capacity(authored.len());
    for &(role, ordinal, raw) in authored {
        decoded_authored.push(HostAuthoredAnchor::new(
            ProvenanceKey::new(role, ordinal),
            source_anchor!(raw),
        ));
    }
    Ok(HostProvenance::new(invocation, decoded_authored)
        .expect("KRS shared parsers emit nonempty, uniquely keyed provenance"))
}
