//! `k::lexeme!` names a token sort; `Stmt` has constructors, not tokens.

use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Stmt: KItem;
}

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Wrap, Halt))]
pub enum StmtSyntax {
    #[k::syntax("wrap {body}")]
    Wrap { body: Stmt },
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

    unwrap: Wrap(k::lexeme!(Stmt, "halt")) => Halt();
}
