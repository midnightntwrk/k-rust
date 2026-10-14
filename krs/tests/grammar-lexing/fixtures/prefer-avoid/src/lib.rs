//! A production is either preferred or avoided: K would let `prefer` win
//! silently, so KRS rejects the pair.

use k::KItem;
use k::builtin::{Bool, KSequence};

k::sorts! {
    Stmt: KItem;
}

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((IfThen, Skip))]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("if {condition} then {body}", avoid, prefer)]
    IfThen { condition: Bool, body: Stmt },
    #[k::syntax("skip")]
    Skip(),
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
