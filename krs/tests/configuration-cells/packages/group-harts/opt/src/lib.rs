//! One hart held in an optional cell.
//!
//! The hart starts present, running the program, and the library's rules
//! for `Hart` are local steps of the one hart present. This definition has
//! no rules of its own, so the hart's bus items stay open.

use hart::{Hart, Job, Jobs, Prog, Regs};
use k::builtin::{Int, Map, map};

#[k::configuration]
pub struct Uni {
    #[k::cell(multiplicity = "?", nested)]
    pub hart: Option<Hart>,
    #[k::cell]
    pub mem: Map<Int, Int>,
}

impl Uni {
    #[k::init]
    pub fn init(pgm: Prog) -> Self {
        Self {
            hart: Some(Hart {
                id: 0,
                k: k::k![pgm],
                pc: 0,
                regs: Regs { a: 1, b: 2 },
                reservation: k::absent!(0),
                jobs: Jobs {
                    job: Job { jid: 0, payload: 0 },
                },
            }),
            mem: map::empty(),
        }
    }
}
