//! `prefer` resolves the dangling else.
//!
//! `if true then if false then first else second` has two parses: the `else`
//! belongs either to the inner `if` or to the outer one. `prefer` on `IfThen`
//! keeps the parse whose top is `IfThen`, so the `else` binds to the inner
//! `if` and the program runs to `second`; the other parse would run to
//! `skip`. `prefer` and `avoid` are parse-forest filters: they act only where
//! a program is ambiguous, so `if true then first else second` still parses
//! as one `IfThenElse`.

use k::KItem;
use k::builtin::{Bool, KSequence};

k::sorts! {
    Stmt: KItem;
}

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((IfThen, IfThenElse, First, Second, Skip))]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("if {condition} then {body}", prefer)]
    IfThen { condition: Bool, body: Stmt },
    #[k::syntax("if {condition} then {then_branch} else {else_branch}")]
    IfThenElse { condition: Bool, then_branch: Stmt, else_branch: Stmt },
    #[k::syntax("first")]
    First(),
    #[k::syntax("second")]
    Second(),
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

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    if_then_true : IfThen { condition: true, body }                             => body;
    if_then_false: IfThen { condition: false, body: _ }                         => Skip();
    if_else_true : IfThenElse { condition: true, then_branch, else_branch: _ }  => then_branch;
    if_else_false: IfThenElse { condition: false, then_branch: _, else_branch } => else_branch;
}
