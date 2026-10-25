//! Warnings for optional and collection cells (KF-023).
//!
//! K starts a `?` or `*` cell present exactly when the cell is `initial` or
//! its template reads a configuration variable. A template that reads one
//! without `initial` therefore starts present although the author did not ask
//! for it, which is legal K and so warns.

use std::collections::BTreeSet;

use krs_diagnostic::{Diagnostic, Location, Severity, codes};
use krs_ir::{FixedCellContent, FixedInitializerContent, SemanticId};
use krs_ir_levels::{DefinitionIr, DefinitionSentence, DefinitionTerm, DefinitionTermKind};

/// The `warning[krs::analysis::collection-config-var-without-initial]`
/// diagnostics of a definition, in configuration order.
#[must_use]
pub fn cell_collection_warnings(definition: &DefinitionIr) -> Vec<Diagnostic> {
    let mut warnings = Vec::new();
    for module in definition.modules() {
        for sentence in module.sentences() {
            if let DefinitionSentence::Configuration(configuration) = sentence {
                let variables = configuration
                    .variables()
                    .iter()
                    .map(|variable| variable.id().clone())
                    .collect::<BTreeSet<_>>();
                let mut cells = Vec::new();
                cells_of(configuration.cells(), &mut cells);
                for initializer in configuration.initializer() {
                    walk(initializer, &cells, &variables, &mut warnings);
                }
            }
        }
    }
    warnings
}

type Cell = krs_ir::FixedCell<krs_ir_levels::DefinitionSortRef, krs_ir_levels::SymbolId>;
type Initializer = krs_ir::FixedInitializerCell<krs_ir_levels::SymbolId, DefinitionTerm>;

fn cells_of<'a>(cells: &'a [Cell], out: &mut Vec<&'a Cell>) {
    for cell in cells {
        out.push(cell);
        if let FixedCellContent::Children { children } = cell.content() {
            cells_of(children, out);
        }
    }
}

fn walk(
    initializer: &Initializer,
    cells: &[&Cell],
    variables: &BTreeSet<SemanticId>,
    warnings: &mut Vec<Diagnostic>,
) {
    let cell = cells.iter().find(|cell| cell.id() == initializer.cell());
    if let Some(cell) = cell
        && let Some(multiplicity) = cell.multiplicity()
        && !cell.is_initial()
        && reads_variable(initializer, variables)
    {
        let mut warning = Diagnostic::error(
            codes::analysis::COLLECTION_CONFIG_VAR_WITHOUT_INITIAL,
            format!(
                "the `multiplicity = \"{}\"` cell `{}` reads a configuration variable, so K starts it present although it is not `initial`; add `initial` to say so",
                multiplicity.as_str(),
                cell.name(),
            ),
            cell.origin()
                .origin()
                .exact_authored_range()
                .map_or(Location::None, Location::Source),
        );
        warning.severity = Severity::Warning;
        warnings.push(warning);
        return;
    }
    if let FixedInitializerContent::Children { children } = initializer.content() {
        for child in children {
            walk(child, cells, variables, warnings);
        }
    }
}

fn reads_variable(initializer: &Initializer, variables: &BTreeSet<SemanticId>) -> bool {
    match initializer.content() {
        FixedInitializerContent::Term { term } => term_reads(term, variables),
        FixedInitializerContent::Children { children } => children
            .iter()
            .any(|child| reads_variable(child, variables)),
    }
}

fn term_reads(term: &DefinitionTerm, variables: &BTreeSet<SemanticId>) -> bool {
    if let DefinitionTermKind::Variable { variable } = term.kind()
        && variables.contains(variable)
    {
        return true;
    }
    term.children()
        .into_iter()
        .any(|child| term_reads(child, variables))
}
