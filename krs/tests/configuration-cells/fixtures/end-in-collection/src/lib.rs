//! `parked` reads the cell `mode` of one thread, an instance of a Map collection: an end is a
//! function of the whole configuration, which holds no one thread for it to read.

use k::builtin::{Int, KSequence};

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("park")] Park(),
}

/// The thread collection's parent.
#[k::cell]
pub struct Threads {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub thread: Thread,
}

/// One thread; its first child `id` is the Map key.
#[k::cell]
pub struct Thread {
    #[k::cell]
    pub id: Int,
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub mode: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell(nested)]
    pub threads: Threads,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            threads: Threads {
                thread: Thread {
                    id: 0,
                    k: k::k![pgm],
                    mode: 0,
                },
            },
        }
    }
}

/// A parked thread.
#[k::end(finished)]
pub fn parked(
    k::cells! {
        mode: k::configuration::Cell(1),
        ..
    }: Thread,
) {
}

k::rules! {
    for Thread;
    use Cmd::*;

    park: {
        k: [Park(), ..],
        mode: _,
    } => {
        k: [..],
        mode: 1,
    };
}
