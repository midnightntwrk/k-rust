//! Whole-theory checks of SMT translations (KF-044).
//!
//! `smtlib = "sym"` makes Z3 see a function as the uninterpreted symbol
//! `sym`. Z3 has one namespace, so two K functions with one symbol would be
//! the same function to the solver.

use std::collections::BTreeMap;

use krs_ir::ProductionAttribute;
use krs_ir_levels::{SemanticModule, SemanticProduction};

use super::error::DescriptorLoweringError;
use crate::partition::production_display_name;

/// Rejects two functions that declare the same `smtlib` symbol.
pub(super) fn check_smtlib_symbols(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    let mut symbols = BTreeMap::<&str, &SemanticProduction>::new();
    for production in modules.iter().flat_map(SemanticModule::productions) {
        for attribute in production.attributes() {
            let ProductionAttribute::Smtlib { symbol, origin } = attribute else {
                continue;
            };
            if let Some(previous) = symbols.insert(symbol, production) {
                return Err(DescriptorLoweringError::DuplicateSmtlib {
                    reason: format!(
                        "`{}` and `{}` both declare `smtlib = \"{symbol}\"`: Z3 would identify `{symbol}` across two K functions; give each its own symbol",
                        production_display_name(previous.id()),
                        production_display_name(production.id()),
                    ),
                    range: origin.origin().exact_authored_range().map(Box::new),
                });
            }
        }
    }
    Ok(())
}
