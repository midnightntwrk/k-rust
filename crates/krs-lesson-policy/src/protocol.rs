//! JSON protocol of the Wasm module.
//!
//! The browser worker sends one UTF-8 JSON request per call:
//!
//! ```json
//! {
//!   "schema": 1,
//!   "policy": { "version": 1, "editable_files": ["src/lib.rs"], "facade_alias": "k" },
//!   "files": { "src/lib.rs": "<complete UTF-8 source>" }
//! }
//! ```
//!
//! `policy` is the lesson manifest's `[policy]` table and `files` is the
//! compile request's file map. The response is:
//!
//! ```json
//! {
//!   "schema": 1,
//!   "ok": false,
//!   "policy_version": 1,
//!   "diagnostics": [
//!     { "code": "krs::policy::non-krs-proc-macro", "message": "…", "file": "src/lib.rs",
//!       "authored": [9, 25], "class": "exact-authored" }
//!   ]
//! }
//! ```
//!
//! `ok` is true exactly when `diagnostics` is empty. `authored` is a UTF-8
//! byte range `[start, end)` or `null` for a request-level rejection. A
//! request that is not valid JSON of this shape yields `ok = false` with one
//! `krs::policy::protocol` diagnostic and `policy_version = null`.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::{LessonPolicy, PolicyDiagnostic, check_request};

/// Protocol schema this module reads and writes.
pub const SCHEMA: u32 = 1;

/// The request was not a valid schema-1 request.
pub const PROTOCOL_ERROR: &str = "krs::policy::protocol";

/// One policy request.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Request {
    /// Must equal [`SCHEMA`].
    pub schema: u32,
    /// The lesson manifest's `[policy]` table.
    pub policy: LessonPolicy,
    /// Package-relative path to UTF-8 source.
    pub files: BTreeMap<String, String>,
}

/// One policy response.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Response {
    /// Always [`SCHEMA`].
    pub schema: u32,
    /// True exactly when `diagnostics` is empty.
    pub ok: bool,
    /// The version that was applied, or `None` for a protocol error.
    pub policy_version: Option<u32>,
    /// Every rejection, file by file in path order, each sorted by offset.
    pub diagnostics: Vec<PolicyDiagnostic>,
}

/// Runs one request given as JSON bytes and returns the JSON response bytes.
///
/// # Panics
///
/// Never in practice: a [`Response`] always serializes.
#[must_use]
pub fn run_json(request: &[u8]) -> Vec<u8> {
    let response = match serde_json::from_slice::<Request>(request) {
        Ok(request) if request.schema == SCHEMA => {
            let diagnostics = check_request(&request.files, &request.policy);
            Response {
                schema: SCHEMA,
                ok: diagnostics.is_empty(),
                policy_version: Some(request.policy.version),
                diagnostics,
            }
        }
        Ok(request) => protocol_error(format!(
            "request schema {} is not supported; expected {SCHEMA}",
            request.schema
        )),
        Err(error) => protocol_error(format!("malformed policy request: {error}")),
    };
    serde_json::to_vec(&response).expect("policy responses always serialize")
}

pub(crate) fn protocol_error(message: String) -> Response {
    Response {
        schema: SCHEMA,
        ok: false,
        policy_version: None,
        diagnostics: vec![PolicyDiagnostic::request_level(PROTOCOL_ERROR, message, "")],
    }
}
