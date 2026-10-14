//! `Frame` is the content of both `current` and `saved`, so the K cell sort
//! of a `Frame` value would name two different cells.

use k::builtin::{Int, KSequence};

k::sorts! {
    Stmt: k::KItem;
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
    pub current: Frame,
    #[k::cell(nested)]
    pub saved: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "PC")] pc: Int,
        #[k::config_var(name = "SAVED")] saved: Int,
    ) -> Self {
        Self {
            k: k::k![pgm],
            current: Frame { pc },
            saved: Frame { pc: saved },
        }
    }
}
