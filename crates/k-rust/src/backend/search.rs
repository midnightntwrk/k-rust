//! Search-target compilation, generated-variable mapping, and hidden-binding filtering (S12 and S27).

use k_rust_backend::{
    rewrite::Pattern,
    search::{PatternMatch, match_disjunction},
};

use super::{Backend, BackendError};

impl Backend {
    pub fn match_disjunction(
        &mut self,
        module: Option<&str>,
        target: &Pattern,
        alternatives: &[Pattern],
    ) -> Result<Vec<PatternMatch>, BackendError> {
        self.with_solver(module, |definition, _| {
            match_disjunction(definition, target, alternatives).map_err(|error| {
                BackendError(format!("KORE pattern match was indeterminate: {error:?}"))
            })
        })
    }
}
