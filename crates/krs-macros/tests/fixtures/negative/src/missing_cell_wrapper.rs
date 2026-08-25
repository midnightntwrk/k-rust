#![deny(warnings)]

use krs_macros::{cells, rule};
use renamed_krs::Term;

pub struct Machine;

#[rule]
pub fn missing_wrapper(
    value: Term<renamed_krs::builtin::Id>,
    cells! {
        k: KCell(value, tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: KCell(value, ..tail),
        ..state
    }
}

fn main() {}
