//! A `#[k::token]` type alias adds token productions to an existing sort,
//! here the builtin `Id`: `@`-prefixed labels are `Id` tokens beside K's own
//! identifiers, so `jump @top` and `jump top` both parse as `jump` of an `Id`.

use k::KItem;
use k::builtin::{Id, KSequence};

k::sorts! {
    Stmt: KItem;
}

/// `@`-prefixed labels are builtin `Id` tokens.
#[k::token(regex = r"@[a-z]+")]
pub type AtId = Id;

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Jump, Halt))]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("jump {label}")]
    Jump { label: Id },
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

    jump: Jump { label: _ } => Halt();
}
