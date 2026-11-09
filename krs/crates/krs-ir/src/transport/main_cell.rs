//! The main cell of a fixed configuration: the one computation cell a run's program starts in,
//! and the one every sentence that names no cell of its own rewrites.
//!
//! One rule decides it, [`select_main_cell`], for every consumer: the collector (a `for Stmt`
//! clause's computation cell), semantic lowering (a `#[k::rule]` fn stated over the computation
//! cell, and the configuration's own check), and both backends' marking of the cell
//! (`krs_ir_levels::k_surface::main_cell`, on the lowered configuration). Each reads the same
//! configuration in its own representation and hands the rule its computation cells, each with
//! whether its initial value reads the main configuration variable.

use super::configuration::{
    CellWrapper, FixedConfiguration, ProtocolInitializerCell, ProtocolInitializerCellContent,
    ProtocolInitializerStateTerm,
};
use super::grammar::{Arguments, Term};
use crate::stage::Stage;

/// Which computation cell (a `KSequence` cell) of a configuration is its main cell.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MainCell<T> {
    /// The main cell.
    Cell(T),
    /// The configuration has no computation cell: nothing computes in it.
    NoComputationCell,
    /// The configuration has several computation cells and does not say which holds the
    /// computation: none of them, or more than one, reads the program.
    Ambiguous {
        /// Every computation cell, in the order the reader that gave them lists them: the
        /// lowered configuration's in declaration order, the initializer's in the order it
        /// writes them. A refusal names them in declaration order.
        cells: Vec<T>,
        /// How many of them read the program.
        reading: usize,
    },
}

impl<T> MainCell<T> {
    /// The main cell, where there is exactly one.
    #[must_use]
    pub fn cell(self) -> Option<T> {
        match self {
            Self::Cell(cell) => Some(cell),
            Self::NoComputationCell | Self::Ambiguous { .. } => None,
        }
    }

    /// The same answer over other cells.
    #[must_use]
    pub fn map<U>(self, mut map: impl FnMut(T) -> U) -> MainCell<U> {
        match self {
            Self::Cell(cell) => MainCell::Cell(map(cell)),
            Self::NoComputationCell => MainCell::NoComputationCell,
            Self::Ambiguous { cells, reading } => MainCell::Ambiguous {
                cells: cells.into_iter().map(map).collect(),
                reading,
            },
        }
    }
}

/// The main cell among a configuration's computation cells (its `KSequence` cells, at any depth:
/// inside a group or a collection instance), each given with whether its initial value reads the
/// main configuration variable, the program.
///
/// The program starts in its cell, so that cell is the computation: the one cell that reads it,
/// and, where none reads it, the configuration's only computation cell. A configuration with
/// several, of which none or more than one reads the program, does not say which is the
/// computation ([`MainCell::Ambiguous`]). A cell of another sort that reads the program (a map
/// keyed by it) holds a value of its declared sort, not a computation, and is no candidate.
pub fn select_main_cell<T>(cells: impl IntoIterator<Item = (T, bool)>) -> MainCell<T> {
    let mut all = Vec::new();
    let mut reading = Vec::new();
    for (index, (cell, reads)) in cells.into_iter().enumerate() {
        if reads {
            reading.push(index);
        }
        all.push(cell);
    }
    match (reading.as_slice(), all.len()) {
        (_, 0) => MainCell::NoComputationCell,
        ([index], _) => MainCell::Cell(all.swap_remove(*index)),
        ([], 1) => MainCell::Cell(all.swap_remove(0)),
        _ => MainCell::Ambiguous {
            cells: all,
            reading: reading.len(),
        },
    }
}

/// The refusal of configuration `configuration`, whose computation cells are `names` (in
/// declaration order), of which `reading` read the program, for having no main cell: the one
/// error every consumer that needs the main cell reports, at the configuration's initializer.
#[must_use]
pub fn ambiguous_main_cell_refusal(configuration: &str, names: &[&str], reading: usize) -> String {
    let count = names.len();
    let names = names
        .iter()
        .map(|name| format!("`{name}`"))
        .collect::<Vec<_>>()
        .join(", ");
    let which = if reading == 0 {
        "none of them reads the program"
    } else {
        "more than one reads the program"
    };
    format!(
        "configuration `{configuration}` has {count} `KSequence` cells, {names}, and {which}: the \
         computation is the `KSequence` cell whose initial value reads the main configuration \
         variable, where the program starts and where every sentence that names no cell runs. \
         Place the program, the `main` configuration variable, in the one `KSequence` cell that \
         holds the computation"
    )
}

impl<S: Stage> FixedConfiguration<S> {
    /// The configuration's main cell ([`select_main_cell`]), as the initializer's reference to
    /// it: the `KCell` leaves of the initializer forest (a `KCell` holds a `KSequence`), each
    /// reading the program where its initial sequence mentions the `main` variable.
    #[must_use]
    pub fn main_cell(&self) -> MainCell<&S::Cell> {
        fn leaves<'a, S: Stage>(
            cells: &'a [super::configuration::StageInitializerCell<S>],
            main: Option<&str>,
            found: &mut Vec<(&'a S::Cell, bool)>,
        ) {
            for cell in cells {
                let ProtocolInitializerCell { field, content, .. } = cell;
                match content {
                    ProtocolInitializerCellContent::Leaf {
                        wrapper: CellWrapper::KCell,
                        value,
                        ..
                    } => found.push((field, main.is_some_and(|main| state_reads(value, main)))),
                    // An undecided neutral leaf is no computation cell: the collector
                    // decides each one on a computation cell before reading the main cell.
                    ProtocolInitializerCellContent::Leaf { .. }
                    | ProtocolInitializerCellContent::NeutralLeaf { .. } => {}
                    ProtocolInitializerCellContent::Nested { children, .. } => {
                        leaves::<S>(children, main, found);
                    }
                }
            }
        }
        let main = self
            .initializer
            .variables
            .iter()
            .find(|variable| variable.main_key.is_some())
            .map(|variable| variable.binding.as_str());
        let mut found = Vec::new();
        leaves::<S>(&self.initializer.cells, main, &mut found);
        select_main_cell(found)
    }
}

/// Whether the initializer state `state` reads the variable `name` ([`term_reads`]): the reading
/// [`FixedConfiguration::main_cell`] asks of each computation leaf, which the collector asks of
/// the computation it decides from a kind-neutral leaf.
#[must_use]
pub fn initializer_state_reads<S: Stage>(
    state: &ProtocolInitializerStateTerm<Term<S>>,
    name: &str,
) -> bool {
    state_reads(state, name)
}

fn state_reads<S: Stage>(state: &ProtocolInitializerStateTerm<Term<S>>, name: &str) -> bool {
    match state {
        ProtocolInitializerStateTerm::Term(term) => term_reads(&term.term, name),
        ProtocolInitializerStateTerm::KSequence(sequence) => sequence
            .items
            .iter()
            .any(|item| term_reads(&item.value.term, name)),
        ProtocolInitializerStateTerm::Map(map) => match &map.body {
            super::configuration::ProtocolMapBody::Empty { .. } => false,
            super::configuration::ProtocolMapBody::Items { items } => items
                .iter()
                .any(|item| term_reads(&item.key.term, name) || term_reads(&item.value.term, name)),
            super::configuration::ProtocolMapBody::Update {
                base, key, value, ..
            } => [base, key, value]
                .iter()
                .any(|term| term_reads(&term.term, name)),
        },
    }
}

/// Whether `term` reads the variable `name`: whether `name` occurs in it free, outside every
/// binder that names it.
///
/// A binder makes its name another variable: the pattern of a `let` and of a `k::matches!` binds
/// every name it holds, which the `let`'s body then reads in place of the outer one, and a
/// closure's binder does the same in its body. The lowered configuration's reader
/// (`krs_ir_levels::k_surface::main_cell`) reads by identity, and lowering gives each such
/// binder a fresh one, so the two readers answer alike; the configuration's lowering checks
/// that they name the same main cell.
fn term_reads<S: Stage>(term: &Term<S>, name: &str) -> bool {
    match term {
        Term::Variable { name: read, .. } => read == name,
        Term::Application {
            arguments, update, ..
        } => {
            arguments_read(arguments, name)
                || update.as_deref().is_some_and(|base| term_reads(base, name))
        }
        Term::Literal { .. }
        | Term::Wildcard { .. }
        | Term::KeptRest { .. }
        | Term::BuiltinToken { .. }
        | Term::Anonymous { .. }
        | Term::Lexeme { .. } => false,
        Term::OrBool { arguments, .. } => arguments.iter().any(|term| term_reads(term, name)),
        Term::Or { alternatives, .. } => alternatives.iter().any(|term| term_reads(term, name)),
        Term::Cell { fields, update, .. } => {
            fields.iter().any(|field| term_reads(&field.value, name))
                || update.as_deref().is_some_and(|base| term_reads(base, name))
        }
        Term::MapEntries { entries, rest, .. } => {
            entries
                .iter()
                .any(|entry| term_reads(&entry.key, name) || term_reads(&entry.value, name))
                || rest.as_deref().is_some_and(|rest| term_reads(rest, name))
        }
        Term::SortTest { operand, .. } => term_reads(operand, name),
        Term::As { pattern, .. } => term_reads(pattern, name),
        // The pattern binds its names, so only the tested term reads.
        Term::Matches { subject, .. } => term_reads(subject, name),
        Term::Let {
            pattern,
            value,
            body,
            ..
        } => {
            let mut bound = std::collections::BTreeSet::new();
            super::validation::let_pattern_names(pattern, &mut bound);
            term_reads(value, name) || (!bound.contains(name) && term_reads(body, name))
        }
        Term::Closure {
            name: binder, body, ..
        } => binder != name && term_reads(body, name),
        Term::Rewrite { from, to, .. } => {
            term_reads(from, name) || to.as_deref().is_some_and(|to| term_reads(to, name))
        }
    }
}

fn arguments_read<S: Stage>(arguments: &Arguments<S>, name: &str) -> bool {
    arguments.iter().any(|argument| {
        let value = match argument {
            super::grammar::TermArgumentRef::Positional { value }
            | super::grammar::TermArgumentRef::Named { value, .. } => value,
        };
        term_reads(value, name)
    })
}

#[cfg(test)]
mod tests {
    use super::{MainCell, select_main_cell};

    /// The rule on its own: the cell that reads the program, else the only cell, else none.
    #[test]
    fn the_main_cell_is_the_one_computation_cell_that_reads_the_program_or_the_only_one() {
        assert_eq!(
            select_main_cell(Vec::<(&str, bool)>::new()),
            MainCell::NoComputationCell
        );
        assert_eq!(select_main_cell([("k", false)]), MainCell::Cell("k"));
        assert_eq!(select_main_cell([("k", true)]), MainCell::Cell("k"));
        assert_eq!(
            select_main_cell([("prog", false), ("code", true)]),
            MainCell::Cell("code")
        );
        assert_eq!(
            select_main_cell([("prog", false), ("code", false)]),
            MainCell::Ambiguous {
                cells: vec!["prog", "code"],
                reading: 0
            }
        );
        assert_eq!(
            select_main_cell([("prog", true), ("code", true)]),
            MainCell::Ambiguous {
                cells: vec!["prog", "code"],
                reading: 2
            }
        );
    }
}
