//! Colours belong to terminals: `color` paints every terminal of a
//! production, and a `colors` list advances once per printed terminal and once
//! per `%c`; `%r` resets. Emitted formats refer to terminals by position, so
//! `while ({condition}) {body}` prints with `format(%1 %2%3%4 %5)`.

use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    impl Exp for Int;
    Stmt;
}

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((While, Block, AssignX, Skip))]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("while ({condition}) {body}", color = "magenta")]
    While { condition: Exp, body: Stmt },
    #[k::syntax("{{{body}}}", colors = ["blue", "blue"])]
    #[k::format("{{%i%n{body}%d%n}}")]
    Block { body: Stmt },
    #[k::syntax("x = {value};", colors = ["green", "red", "red", "red"])]
    #[k::format("%c// assign%r%nx = {value};")]
    AssignX { value: Int },
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
