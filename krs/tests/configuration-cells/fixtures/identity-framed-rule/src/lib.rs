//! `idle` leaves the computation cell out and writes `fuel` back unchanged,
//! so applying it changes nothing.

use k::builtin::{Int, KSequence};

k::sorts! {
    Stmt: k::KItem;
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub fuel: Int,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "FUEL")] fuel: Int,
    ) -> Self {
        Self {
            k: k::k![pgm],
            fuel,
        }
    }
}

k::rules! {
    for Machine;

    idle: { fuel: f } => { fuel: f };
}
