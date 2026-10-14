//! A builtin token is a literal: `k::lexeme!(Int, "1")` is written `1`.

use k::KItem;
use k::builtin::{Int, KSequence};

k::sorts! {
    Stmt: KItem;
}

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Push, Halt))]
pub enum StmtSyntax {
    #[k::syntax("push {value}")]
    Push { value: Int },
    #[k::syntax("halt")]
    Halt(),
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

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    push_one: Push(k::lexeme!(Int, "1")) => Halt();
}
