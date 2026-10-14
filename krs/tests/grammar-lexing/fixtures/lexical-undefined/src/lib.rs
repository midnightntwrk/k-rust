//! A token regex refers to `{Digit}`, which no `k::lexical!` declares.

use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Stmt: KItem;
}

k::lexical! {
    Alpha = r"[a-z]";
}

#[k::token(regex = r"{Alpha}{Digit}*")]
pub struct Name(pub String);

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
