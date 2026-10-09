//! Console stream cells in rules (KF-035).
//!
//! K generates the rules that move standard input into a `stream = "stdin"` cell only for a rule
//! that consumes the cell's front item, `<in> ListItem(V:Sort) => .List ... </in>`, and rejects
//! any other pattern on that cell (Java K's `ResolveIOStreams`, k-rust's `resolve_io.rs`). The
//! readable spelling of that read is `input: list::concat(list::item(v), rest) => rest`, with
//! `rest` used nowhere else in the rule. Semantic analysis rejects every other clause on a stdin
//! cell; Definition IR lowering then writes the read as the clause `ListItem(V) => .List` with an
//! unbound list remainder and drops `rest`.

use std::collections::BTreeSet;

use krs_ir::{CellAttribute, CellContentFrame, CellPost, CellStream, FixedCell, FixedCellClause};
use krs_ir::{FixedCellContent, SemanticId};
use krs_ir_levels::{IrTermKind, ListOperands, SemanticTerm, SemanticTheory};

/// One semantic fixed-cell clause.
pub(crate) type SemanticClause = FixedCellClause<SemanticId, SemanticTerm>;

/// A read of a stdin stream cell in the shape K unblocks.
pub(crate) struct StdinRead<'a> {
    /// `list::item(v)`, the consumed front item.
    pub(crate) item: &'a SemanticTerm,
    /// The remainder binding `rest`.
    pub(crate) rest: &'a SemanticId,
}

/// The read `list::concat(list::item(v), rest) => rest` in `clauses[index]`, with `v` a variable
/// and `rest` used by no other clause.
pub(crate) fn stdin_read(clauses: &[SemanticClause], index: usize) -> Option<StdinRead<'_>> {
    let clause = &clauses[index];
    let (CellPost::Replace { term: after }, CellContentFrame::Exact) =
        (clause.after(), clause.frame())
    else {
        return None;
    };
    let IrTermKind::List(before) = clause.before().kind() else {
        return None;
    };
    let ListOperands::Concat { left, right } = &**before else {
        return None;
    };
    let (IrTermKind::List(front), IrTermKind::Variable { variable: rest }) =
        (left.kind(), right.kind())
    else {
        return None;
    };
    let ListOperands::Item { element } = &**front else {
        return None;
    };
    let used_elsewhere = clauses
        .iter()
        .enumerate()
        .any(|(other, clause)| other != index && clause_mentions(clause, rest));
    (matches!(element.kind(), IrTermKind::Variable { .. })
        && matches!(after.kind(), IrTermKind::Variable { variable } if variable == rest)
        && !used_elsewhere)
        .then_some(StdinRead { item: left, rest })
}

/// The stdin stream cells of every configuration in `theory`.
pub(crate) fn stdin_cells(theory: &SemanticTheory) -> BTreeSet<SemanticId> {
    let mut cells = BTreeSet::new();
    for module in theory.modules() {
        if let Some(configuration) = module.configuration() {
            collect_stdin_cells(configuration.cells(), &mut cells);
        }
    }
    cells
}

fn collect_stdin_cells<S>(cells: &[FixedCell<S, SemanticId>], output: &mut BTreeSet<SemanticId>) {
    for cell in cells {
        if cell.attributes().iter().any(|attribute| {
            matches!(
                attribute,
                CellAttribute::Stream {
                    value: CellStream::Stdin,
                    ..
                }
            )
        }) {
            output.insert(cell.id().clone());
        }
        if let FixedCellContent::Children { children } = cell.content() {
            collect_stdin_cells(children, output);
        }
    }
}

fn clause_mentions(clause: &SemanticClause, variable: &SemanticId) -> bool {
    term_mentions(clause.before(), variable)
        || matches!(clause.after(), CellPost::Replace { term } if term_mentions(term, variable))
        || matches!(
            clause.frame(),
            CellContentFrame::KSequenceTail { binding: Some(binding), .. }
                | CellContentFrame::MapRemainder { binding: Some(binding), .. }
                if binding == variable
        )
}

fn term_mentions(term: &SemanticTerm, variable: &SemanticId) -> bool {
    match term.kind() {
        IrTermKind::Variable { variable: name } => name == variable,
        IrTermKind::Token { .. } => false,
        IrTermKind::Application { arguments, .. }
        | IrTermKind::KSequence {
            items: arguments, ..
        }
        | IrTermKind::Cell {
            children: arguments,
            ..
        } => arguments
            .iter()
            .any(|argument| term_mentions(argument, variable)),
        IrTermKind::Map(operands) => operands
            .operands()
            .any(|operand| term_mentions(operand, variable)),
        IrTermKind::List(operands) => operands
            .operands()
            .any(|operand| term_mentions(operand, variable)),
        IrTermKind::Set(operands) => operands
            .operands()
            .any(|operand| term_mentions(operand, variable)),
        IrTermKind::Rewrite { from, to } => {
            term_mentions(from, variable) || term_mentions(to, variable)
        }
        IrTermKind::As { alias, pattern } => alias == variable || term_mentions(pattern, variable),
        IrTermKind::Or { alternatives } => alternatives
            .iter()
            .any(|alternative| term_mentions(alternative, variable)),
        IrTermKind::Matches {
            subject, pattern, ..
        } => term_mentions(subject, variable) || term_mentions(pattern, variable),
    }
}
