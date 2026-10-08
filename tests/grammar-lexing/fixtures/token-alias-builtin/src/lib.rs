//! A token alias adds tokens to a user sort or to `Id`; `Int` has its own literals.

use k::KItem;
use k::builtin::{Int, KSequence};

k::sorts! {
    Stmt: KItem;
}

#[k::token(regex = r"0x[0-9a-f]+")]
pub type HexInt = Int;

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Push))]
pub enum StmtSyntax {
    #[k::syntax("push {value}")]
    Push { value: Int },
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
