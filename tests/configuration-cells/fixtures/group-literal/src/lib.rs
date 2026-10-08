//! `frame: 3` writes an integer where the whole nested cell `frame` belongs:
//! a nested cell entry is a binder, `_`, or `k::fragment!`.

use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Reset))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("reset")] Reset(),
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
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
    ) -> Self {
        Self {
            k: k::k![pgm],
            frame: Frame { pc },
        }
    }
}

#[k::rule(label = "reset")]
pub fn reset(
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Reset(), tail @ ..),
        frame: _,
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        frame: 3,
        ..state
    }
}
