//! The specification and program digests that key the result cache (flow README 5.3).
//!
//! Both are `payload_digest(domain, canonical JSON)` (kink-patch), so they depend on values,
//! never on how `FLOW.toml` is formatted, and a program's id enters neither: renaming a
//! program keeps its cached result.

use crate::manifest::{FlowManifest, Program};
use kink_corpus::SourceFile;
use kink_native::{K_RUST_REVISION, execution::SolverProfile};
use kink_patch::{Sha256Digest, canonical_json, payload_digest, sha256};
use serde_json::{Value, json};

/// Domain of the specification digest.
pub const SPEC_DOMAIN: &str = "kink-flow/spec/v1";
/// Domain of the program digest.
pub const PROGRAM_DOMAIN: &str = "kink-flow/program/v1";

/// The payload of the specification digest: the k-rust revision and solver profile of this
/// build, how the specification is loaded, and every non-builtin source file the load read
/// (`files`, kink-corpus `load_source`), as `{name, sha256}` sorted by name. Builtin sources
/// are fixed by the k-rust revision.
pub fn spec_payload(manifest: &FlowManifest, files: &[SourceFile]) -> Value {
    let spec = &manifest.spec;
    let mut files = files
        .iter()
        .map(|file| (file.name.clone(), file.sha256.to_string()))
        .collect::<Vec<_>>();
    files.sort();
    json!({
        "k_rust_revision": K_RUST_REVISION,
        "profile": SolverProfile::BUILD.name(),
        "entry": spec.entry,
        "main_module": spec.main_module,
        "syntax_module": spec.syntax_module,
        "md_selector": spec.md_selector,
        "include_dirs": spec.include_dirs,
        "files": files
            .into_iter()
            .map(|(name, sha256)| json!({"name": name, "sha256": sha256}))
            .collect::<Vec<_>>(),
    })
}

/// The specification digest of README 5.3.
pub fn spec_digest(manifest: &FlowManifest, files: &[SourceFile]) -> Sha256Digest {
    payload_digest(
        SPEC_DOMAIN,
        canonical_json(&spec_payload(manifest, files)).as_bytes(),
    )
}

/// The payload of a program digest: the sha256 of the program's bytes (its file's bytes, or
/// its inline text), its start sort and its configuration variables sorted by name.
pub fn program_payload(program: &Program, text: &str) -> Value {
    let mut variables = program.variables.clone();
    variables.sort();
    json!({
        "program_sha256": sha256(text.as_bytes()).to_string(),
        "start_sort": program.start_sort,
        "variables": variables
            .into_iter()
            .map(|(name, text)| json!({"name": name, "text": text}))
            .collect::<Vec<_>>(),
    })
}

/// The program digest of README 5.3; `text` is the program's text as read for admission.
pub fn program_digest(program: &Program, text: &str) -> Sha256Digest {
    payload_digest(
        PROGRAM_DOMAIN,
        canonical_json(&program_payload(program, text)).as_bytes(),
    )
}
