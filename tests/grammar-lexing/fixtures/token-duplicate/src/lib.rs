//! One sort declares each token once: the alias repeats the struct's terminal.

use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Stmt: KItem;
}

#[k::token(regex = r"[a-z]+")]
#[k::token(terminal = "main")]
pub struct Name(pub String);

#[k::token(terminal = "main")]
pub type MoreNames = Name;

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Call))]
pub enum StmtSyntax {
    #[k::syntax("call {target}")]
    Call { target: Name },
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
