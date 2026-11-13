//! A second definition that holds the group `Core`, which refuses some inputs before it runs.
//!
//! `Board { core, timer }` starts with one item in the core's computation, `boot ( rom , pgm )`:
//! the inputs, not yet loaded. The rule `accept` replaces it by the program when the ROM number
//! is not negative, and no rule applies otherwise. The end `refused_rom` declares the second
//! set of states, and only it: a `fn` over the item whose condition is the negation of
//! `accept`'s, with the item as its reason. `#[k::end(refused)]` on the constructor `Boot`
//! would declare every state whose computation starts with the item, which holds where
//! `accept` applies too. So an input the board does not accept ends `refused` after no step,
//! at the initial state, and no cell of the machine was written.
//!
//! The board has no memory, so no rule answers `busRead`: a `load` is stuck at it, at no
//! declared end. The group's ends (`end_core::halt`, `end_core::trap`, `end_core::drained`,
//! `end_core::overflow`) are this definition's too, under the names they have in `Small`.

use k::Term;
use k::builtin::{Int, int};

k::sorts! {
    Start;
}

/// The board's first item: the ROM and the program it was given, not yet accepted.
#[k::constructor(sort = Start, syntax = "boot ( {rom} , {pgm} )", internal)]
pub struct Boot {
    pub rom: Term<Int>,
    pub pgm: Term<end_core::Prog>,
}

#[k::configuration]
pub struct Board {
    #[k::cell(nested)]
    pub core: end_core::Core,
    #[k::cell]
    pub timer: Int,
}

impl Board {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: end_core::Prog,
        #[k::config_var(name = "ROM")] rom: Int,
    ) -> Self {
        Self {
            core: end_core::Core {
                k: k::k![Boot { rom, pgm }],
                pc: 0,
                acc: 0,
            },
            timer: 0,
        }
    }
}

/// A negative ROM number is refused, with the item: `accept` applies exactly where it is not.
#[k::end(refused)]
#[k::requires(int::lt(rom, 0))]
fn refused_rom(
    rom: Term<Int>,
    pgm: Term<end_core::Prog>,
    k::cells! {
        end_core::Core::k: k::configuration::KCell(Boot { rom, pgm }, ..),
        ..
    }: Board,
) -> Term<Start> {
    Boot { rom, pgm }
}

k::rules! {
    for Board;

    /// Accept a ROM whose number is not negative, and start the timer at it.
    #[k::requires(int::le(0, rom))]
    accept: {
        k: [Boot { rom, pgm }, ..],
        timer: _,
    } => {
        k: [pgm, ..],
        timer: rom,
    };
}
