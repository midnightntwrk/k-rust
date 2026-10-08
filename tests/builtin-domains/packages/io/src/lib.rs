//! Console I/O and the exit cell (KF-035).
//!
//! I/O in K is configuration state. `input` is the `stream = "stdin"` cell:
//! K fills it from standard input, and a rule reads by consuming the Int at its
//! front. `output` is the `stream = "stdout"` cell: a rule prints by appending
//! an item, and K's stream rules write it out. `status` is the exit cell: its
//! final Int value is the process exit status, like `std::process::exit`.
//!
//! The program `read; read; print(sum); halt(sum)` adds two numbers from
//! standard input, prints the sum, and exits with it. The input has one token
//! per line, where k-rust's buffered input and an interactive stream agree.

use k::builtin::{Int, KSequence, List, int, list};

k::sorts! {
    Stmt: k::KItem;
}

/// A statement of the accumulator machine; `;` sequences two statements.
#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence(
    stmt (Read, PrintSum, HaltSum)
    > right seq (Seq)
)]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("read")]
    Read(),
    #[k::syntax("print(sum)")]
    PrintSum(),
    #[k::syntax("halt(sum)")]
    HaltSum(),
    #[k::syntax("{first} ; {rest}")]
    Seq { first: Stmt, rest: Stmt },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(stream = "stdin")]
    pub input: List,
    #[k::cell(stream = "stdout")]
    pub output: List,
    #[k::cell]
    pub sum: Int,
    #[k::cell(exit)]
    pub status: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            input: list::empty(),
            output: list::empty(),
            sum: 0,
            status: 1,
        }
    }
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    /// Sequencing: run the first statement, then the rest.
    seq: {
        k: [Seq { first, rest }, ..]
    } => {
        k: [first, rest, ..]
    };

    /// Reading consumes the Int at the front of the input stream.
    read: {
        k: [Read(), ..],
        input: list::concat(list::item(i), more),
        sum: s,
    } => {
        k: [..],
        input: more,
        sum: int::add(s, i),
    }
    where i: Int;

    /// Printing appends to the output stream.
    print: {
        k: [PrintSum(), ..],
        output: out,
        sum: s,
    } => {
        k: [..],
        output: list::concat(out, list::item(s)),
        sum: s,
    };

    /// Halting sets the exit status.
    halt: {
        k: [HaltSum(), ..],
        sum: s,
        status: previous,
    } => {
        k: [..],
        sum: s,
        status: s,
    };
}
