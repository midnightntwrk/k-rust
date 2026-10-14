//! `burn` leaves the computation cell out, matches any `fuel`, and has no
//! guard, so it is enabled in every configuration and execution never ends.

use k::builtin::{Int, KSequence, int};

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

    burn: { fuel: f } => { fuel: int::sub(f, 1) };
}
