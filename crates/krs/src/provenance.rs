//! Decodes literal source coordinates emitted by KRS macros.

use crate::{
    AnchorPrecision, HostAuthoredAnchor, HostProvenance, HostSourceAnchor, HostSourcePosition,
    ProvenanceKey, ProvenanceRole,
};

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
#[doc(hidden)]
#[inline(never)]
#[track_caller]
#[must_use]
pub fn __krs_host_provenance(
    manifest_dir: &str,
    files: &[&str],
    invocation: __KrsRawAnchor,
    authored: &[(ProvenanceRole, u32, __KrsRawAnchor)],
) -> HostProvenance {
    let mut resolved: Vec<Option<String>> = vec![None; files.len()];
    macro_rules! source_anchor {
        ($raw:expr) => {{
            let raw: __KrsRawAnchor = $raw;
            let file = if raw.absolute {
                match &resolved[raw.file] {
                    Some(file) => file.clone(),
                    None => {
                        let source = std::path::Path::new(files[raw.file]);
                        let manifest = std::path::Path::new(manifest_dir);
                        let file = source
                            .strip_prefix(manifest)
                            .expect("rustc's absolute display path must remain inside the Cargo package")
                            .to_string_lossy()
                            .replace('\\', "/");
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
    HostProvenance::new(invocation, decoded_authored)
        .expect("KRS shared parsers emit nonempty, uniquely keyed provenance")
}
