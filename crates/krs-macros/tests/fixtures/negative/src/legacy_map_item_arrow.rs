use krs_macros::{cells, map, rule};
use renamed_krs::Term;
use renamed_krs::configuration::{Cell, KCell};

pub struct Machine;

#[rule]
pub fn legacy_map_item_arrow(
    key: Term<renamed_krs::builtin::Id>,
    value: Term<renamed_krs::builtin::Id>,
    cells! {
        k: KCell(key, tail @ ..),
        env: Cell(map![key => value, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: KCell(value, ..tail),
        ..state
    }
}

fn main() {}
