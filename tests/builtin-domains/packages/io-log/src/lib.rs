//! A log line: `io::log`.
//!
//! `trace` logs the line `traced` with K's `#log` (hook `IO.logString`) and
//! evaluates to the empty computation. Java K's LLVM backend writes the line
//! to standard error; `krs run` prints the log effects of the in-process k-rust
//! backend to standard error the same way. Unlike `io::write` and `io::putc`,
//! `io::log` needs no console state, so the native routes keep it; like every
//! `K-IO` operation it records the `ConsoleIO` requirement, which the browser
//! route refuses.

use k::builtin::{KSequence, io};

k::sorts! {
    Stmt: k::KItem;
}

/// A statement that logs.
#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Trace))]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("trace")]
    Trace(),
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

    /// `trace` logs one line with `#log`.
    trace: {
        k: [Trace(), ..]
    } => {
        k: [io::log("traced"), ..]
    };
}
