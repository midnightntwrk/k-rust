//! `Name`'s regex matches `k` at `prec(2)`, as strongly as K's own `#LowerId`,
//! so in the emitted `configuration <k> $PGM:Stmt </k>` the cell name `k`
//! lexes as a `Name` and Java K cannot parse the configuration.

use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Stmt: KItem;
    impl KItem for Name;
}

#[k::token(regex = r"[a-z][a-z0-9_]*", prec = 2)]
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
