//! Versioned syntactic policy for editable KRS lesson source.
//!
//! A browser lesson compiles learner-edited Rust with a compiler that cannot
//! load arbitrary procedural macros. This crate runs before expansion and
//! before rustc and rejects any editable source that leaves the lesson
//! surface: a procedural macro other than a KRS facade macro, an
//! `extern crate`, a reach outside the lesson's editable files, and the other
//! constructs listed in [`v1`].
//!
//! The rule set is selected by the lesson manifest's `[policy] version`
//! field and compiled into this crate; a manifest never carries rules. Each
//! version is frozen once published: changing an allowlist or a rule creates
//! a new version.
//!
//! [`check`] checks one authored file and [`check_request`] checks a whole
//! compile request. Every source diagnostic carries the exact UTF-8 byte
//! range in the authored file. The crate also builds as a
//! `wasm32-unknown-unknown` module whose JSON protocol is described in
//! [`protocol`].

use std::collections::BTreeMap;
use std::ops::Range;

use serde::{Deserialize, Serialize, Serializer};

#[cfg(feature = "abi")]
mod abi;
pub mod protocol;
pub mod v1;

/// The `[policy]` table of a lesson manifest.
///
/// ```toml
/// [policy]
/// version = 1
/// editable_files = ["src/lib.rs"]
/// facade_alias = "k"
/// ```
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LessonPolicy {
    /// Rule-set version compiled into this crate.
    pub version: u32,
    /// Package-relative paths (`/`-separated) that a compile request may
    /// contain and that an out-of-line `mod` may resolve to.
    pub editable_files: Vec<String>,
    /// The dependency name under which the lesson's `Cargo.toml` imports the
    /// `krs` facade, `k` for every current lesson.
    pub facade_alias: String,
}

impl LessonPolicy {
    /// The policy of a single-file lesson whose crate root is `src/lib.rs`
    /// and whose facade alias is `k`, as tour-minimal uses.
    #[must_use]
    pub fn single_file_v1() -> Self {
        Self {
            version: 1,
            editable_files: vec!["src/lib.rs".to_owned()],
            facade_alias: "k".to_owned(),
        }
    }
}

/// One policy rejection.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct PolicyDiagnostic {
    /// Stable diagnostic code, one of the `v1` codes such as
    /// `krs::policy::non-krs-proc-macro`.
    pub code: &'static str,
    /// Human-readable explanation.
    pub message: String,
    /// The package-relative file the diagnostic concerns.
    pub file: String,
    /// UTF-8 byte range in the authored file; `None` only for request-level
    /// rejections, which have no source location.
    #[serde(serialize_with = "serialize_range")]
    pub authored: Option<Range<usize>>,
    /// `exact-authored` whenever `authored` is `Some`, `unmappable` otherwise.
    pub class: &'static str,
}

impl PolicyDiagnostic {
    pub(crate) fn authored(
        code: &'static str,
        message: String,
        file: &str,
        range: Range<usize>,
    ) -> Self {
        Self {
            code,
            message,
            file: file.to_owned(),
            authored: Some(range),
            class: CLASS_EXACT_AUTHORED,
        }
    }

    pub(crate) fn request_level(code: &'static str, message: String, file: &str) -> Self {
        Self {
            code,
            message,
            file: file.to_owned(),
            authored: None,
            class: CLASS_UNMAPPABLE,
        }
    }
}

/// Diagnostic class of a diagnostic with an exact authored range.
pub const CLASS_EXACT_AUTHORED: &str = "exact-authored";
/// Diagnostic class of a request-level diagnostic.
pub const CLASS_UNMAPPABLE: &str = "unmappable";

/// A request selected a policy version this crate does not implement.
pub const UNKNOWN_VERSION: &str = "krs::policy::unknown-version";

/// Every policy version this crate implements.
pub const SUPPORTED_VERSIONS: &[u32] = &[1];

// `serialize_with` passes the field by reference.
#[allow(clippy::ref_option)]
fn serialize_range<S: Serializer>(
    range: &Option<Range<usize>>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    range
        .as_ref()
        .map(|range| [range.start, range.end])
        .serialize(serializer)
}

/// Checks one authored file against `policy`.
///
/// `display_file` is the package-relative path of `source` (for example
/// `src/lib.rs`); it is recorded in each diagnostic and resolves out-of-line
/// modules. The result is sorted by authored start offset and is empty when
/// the file is accepted.
///
/// Parsing uses `proc_macro2`'s fallback spans, which accumulate in a
/// thread-local source map. This function does not clear that map, so it is
/// safe to call while the caller holds spans of its own; a long-lived caller
/// should call `proc_macro2::extra::invalidate_current_thread_spans` when it
/// holds none.
#[must_use]
pub fn check(source: &str, display_file: &str, policy: &LessonPolicy) -> Vec<PolicyDiagnostic> {
    match policy.version {
        1 => v1::check(source, display_file, policy),
        other => vec![unknown_version(other, display_file)],
    }
}

/// Checks a compile request: every file key must be in
/// `policy.editable_files`, and every file is checked with [`check`].
///
/// `files` maps package-relative paths to UTF-8 source, as the browser
/// worker's `CompileRequest.files` does. A file outside the allowlist yields
/// one request-level `krs::policy::editable-file` diagnostic and is not
/// parsed.
#[must_use]
pub fn check_request(
    files: &BTreeMap<String, String>,
    policy: &LessonPolicy,
) -> Vec<PolicyDiagnostic> {
    if !SUPPORTED_VERSIONS.contains(&policy.version) {
        return vec![unknown_version(policy.version, "")];
    }
    let mut diagnostics = Vec::new();
    for (path, source) in files {
        if policy.editable_files.iter().any(|allowed| allowed == path) {
            diagnostics.extend(check(source, path, policy));
        } else {
            diagnostics.push(PolicyDiagnostic::request_level(
                v1::EDITABLE_FILE,
                format!(
                    "`{path}` is not an editable file of this lesson; editable files are {:?}",
                    policy.editable_files
                ),
                path,
            ));
        }
    }
    diagnostics
}

fn unknown_version(version: u32, file: &str) -> PolicyDiagnostic {
    PolicyDiagnostic::request_level(
        UNKNOWN_VERSION,
        format!(
            "lesson policy version {version} is not implemented; supported versions are {SUPPORTED_VERSIONS:?}"
        ),
        file,
    )
}
