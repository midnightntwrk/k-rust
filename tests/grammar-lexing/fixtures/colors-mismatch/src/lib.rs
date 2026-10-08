//! `colors` names one colour per printed terminal and per `%c`: `x = {value};`
//! prints three terminals and one `%c`, so two colours are too few.

use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((AssignX))]
pub enum StmtSyntax {
    #[k::syntax("x = {value};", colors = ["green", "red"])]
    #[k::format("%c// assign%r%nx = {value};")]
    AssignX { value: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm] }
    }
}
