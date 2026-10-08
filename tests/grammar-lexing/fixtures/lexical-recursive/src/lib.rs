//! Two lexicals refer to each other, so K would expand them forever.

use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Stmt: KItem;
}

k::lexical! {
    Word = r"[a-z]{Tail}?";
    Tail = r"[0-9]{Word}";
}

#[k::token(regex = r"{Word}")]
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
