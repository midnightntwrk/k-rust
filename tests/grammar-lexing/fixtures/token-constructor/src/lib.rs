//! A token sort is closed: a constructor family cannot target it.

use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Stmt: KItem;
}

#[k::token(regex = r"[a-z]+")]
pub struct Name(pub String);

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Call))]
pub enum StmtSyntax {
    #[k::syntax("call {target}")]
    Call { target: Name },
}

#[k::constructors(sort = Name, result = k::KResult)]
#[k::precedence((Anonymous))]
pub enum NameSyntax {
    #[k::syntax("anonymous")]
    Anonymous(),
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
