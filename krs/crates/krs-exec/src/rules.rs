//! The compiled definition's rules and equations, by the backend's identity (`UNIQUE_ID`).
//!
//! k-rust names a rule or an equation by its `UNIQUE_ID` in run coverage and in traces. This
//! catalog is what krs-exec reads each identity's label and kind from, as the backend loaded
//! them (`Backend::rule_catalog`).

use std::collections::BTreeMap;

use k_rust::backend::{Backend, CompiledRuleKind};

use crate::{ExecError, report::RuleKind};

/// One identity of the catalog.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CatalogRule {
    /// The rule's label, as the backend names it (`MODULE.name`).
    pub(crate) label: Option<String>,
    /// What kind of sentence it is.
    pub(crate) kind: RuleKind,
}

/// The rules and equations of the definition a run executes, by `UNIQUE_ID`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Rules {
    by_id: BTreeMap<String, CatalogRule>,
}

impl Rules {
    /// The catalog of the definition `backend` runs.
    pub(crate) fn new(backend: &Backend) -> Result<Self, ExecError> {
        let mut by_id = BTreeMap::new();
        for rule in backend.rule_catalog(None)? {
            // Equal written axioms share one identity (`shared_identity`); they are one rule.
            by_id.entry(rule.id).or_insert(CatalogRule {
                label: rule.label,
                kind: match rule.kind {
                    CompiledRuleKind::Rewrite => RuleKind::Rule,
                    CompiledRuleKind::FunctionEquation => RuleKind::Equation,
                    CompiledRuleKind::Simplification => RuleKind::Simplification,
                    CompiledRuleKind::Definedness => RuleKind::Definedness,
                },
            });
        }
        Ok(Self { by_id })
    }

    /// The identity `id`, when the catalog holds it.
    pub(crate) fn get(&self, id: &str) -> Option<&CatalogRule> {
        self.by_id.get(id)
    }
}
