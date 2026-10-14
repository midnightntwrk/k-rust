//! Direct console writes: `io::write` and `io::putc`.
//!
//! `hello` writes the string `hi` and a newline to file descriptor 1 with K's
//! `#write`, and `bye` writes the byte 65 (`A`) with `#putc`. Both evaluate to
//! the empty computation. `both` writes `hi` and a newline and continues with
//! `bye` in the same rule: the `K`-sorted `#write` item splices into the
//! sequence as K's `~>` does. Java K's LLVM backend performs the writes; KRS's
//! in-process k-rust backend has no console state, so `krs run` refuses the
//! definition before compiling it (`ConsoleWriteHook`). A `stream` cell is the
//! portable way to print.

use k::builtin::{KSequence, io};

k::sorts! {
    Stmt: k::KItem;
}

/// A statement that writes to standard output.
#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Hello, Bye, Both))]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("hello")]
    Hello(),
    #[k::syntax("bye")]
    Bye(),
    #[k::syntax("both")]
    Both(),
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
    for Machine;
    use StmtSyntax::*;

    /// `hello` writes a line with `#write`.
    hello: {
        k: [Hello(), ..]
    } => {
        k: [io::write(1, "hi\n"), ..]
    };

    /// `bye` writes one byte with `#putc`.
    bye: {
        k: [Bye(), ..]
    } => {
        k: [io::putc(1, 65), ..]
    };

    /// `both` writes a line and then continues with `bye`.
    both: {
        k: [Both(), ..]
    } => {
        k: [io::write(1, "hi\n"), Bye(), ..]
    };
}
