//! The answers of the facade's request routes for implication and models, as their JSON text
//! forms write them (`Backend::implies_json`, `Backend::get_model_json`) and read back as JSON:
//! the form the RPC server, the bindings and the CLI hand out, for tests that state what that
//! answer says (its `status`, `satisfiable`, `condition` or `substitution`).
//! A test that needs the pattern itself uses the pattern forms (`Backend::implies_kore`,
//! `Backend::model_for`, `Backend::simplify_kore`).
//!
//! Test binaries include this file with `#[path = "support/wire_answers.rs"] mod wire_answers;`
//! and bring [`WireAnswers`] into scope.

use k_rust::backend::{Backend, BackendError, ImplicationRequest, PatternRequest};
use serde_json::Value;

/// The JSON text an answer route wrote, read back as JSON.
fn read(text: Result<String, BackendError>) -> Result<Value, BackendError> {
    text.map(|text| serde_json::from_str(&text).expect("the facade writes JSON text"))
}

/// The implication and model routes' answers as JSON.
pub trait WireAnswers {
    /// The `implies` answer to `request` (an `ImplicationResult` as JSON).
    #[allow(dead_code)]
    fn implies_answer(&mut self, request: ImplicationRequest) -> Result<Value, BackendError>;

    /// The `get-model` answer to `request` (a `ModelResultOutput` as JSON).
    #[allow(dead_code)]
    fn model_answer(&mut self, request: PatternRequest) -> Result<Value, BackendError>;
}

impl WireAnswers for Backend {
    fn implies_answer(&mut self, request: ImplicationRequest) -> Result<Value, BackendError> {
        read(self.implies_json(request))
    }

    fn model_answer(&mut self, request: PatternRequest) -> Result<Value, BackendError> {
        read(self.get_model_json(request))
    }
}
