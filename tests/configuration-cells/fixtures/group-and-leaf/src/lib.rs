//! `peek` selects the nested cell `frame` and the cell `pc` inside it: the
//! whole-cell entry already names `pc`, so the rule selects it twice.

use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Peek))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("peek")] Peek(),
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub gas: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "PC")] pc: Int,
        #[k::config_var(name = "GAS")] gas: Int,
    ) -> Self {
        Self {
            k: k::k![pgm],
            frame: Frame { pc, gas },
        }
    }
}

k::rules! {
    for Machine;
    use Cmd::*;

    peek: {
        k: [Peek(), ..],
        frame: f,
        pc: p,
    } => {
        k: [..],
        frame: f,
        pc: int::add(p, 1),
    };
}
