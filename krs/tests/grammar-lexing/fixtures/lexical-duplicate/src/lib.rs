//! Two `k::lexical!` blocks declare `Alpha`; K names lexicals in one namespace.

use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Stmt: KItem;
}

k::lexical! {
    Alpha = r"[a-z]";
}

k::lexical! {
    Alpha = r"[A-Z]";
}

#[k::token(regex = r"{Alpha}+")]
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
