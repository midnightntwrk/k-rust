//! Optional cells (KF-023): K's lesson 1.17-A exercise.
//!
//! A `multiplicity = "?"` cell is declared `Option<T>`: a rule matches it
//! with `Some(..)` when it is present and with `None` when it is absent.
//! `<counter>` starts absent (it has no `initial`); its init value
//! `Some(0)` is K's template, not a starting state.
//!
//! - `enable` creates the counter: `{ counter: None } => { counter: Some(0) }`
//!   emits `(.Bag => <counter> 0 </counter>)`. K tests that a `?` cell is
//!   absent only by creating it, so a second `enable` is stuck;
//! - `inc` and `dec` update it in place, `<counter> N => N +Int 1 </counter>`;
//!   `dec` is written in the reference spelling `krs expand` prints;
//! - `read` reads it without restating it in the result, and writes its
//!   value to the computation cell;
//! - `disable` deletes it: `(<counter> _ </counter> => .Bag)`.
//!
//! The nested `<mark>` cell is an optional group: `mark: Some(m)` binds the
//! whole cell, of K's sort `MarkCell`, and `stamp` creates it from the
//! counter with `k::fragment!`. `peek` matches it with the readable record
//! `Some(Mark { seen: s })`, the same group term.

use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(
    cmd (Enable, Inc, Dec, Read, Disable, Stamp, Peek)
    > right seq (Seq)
)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("enable")] Enable(),
    #[k::syntax("inc")] Inc(),
    #[k::syntax("dec")] Dec(),
    #[k::syntax("read")] Read(),
    #[k::syntax("disable")] Disable(),
    #[k::syntax("stamp")] Stamp(),
    #[k::syntax("peek")] Peek(),
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

/// An optional group: a whole cell that is present or absent.
#[k::cell]
pub struct Mark {
    #[k::cell]
    pub seen: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(multiplicity = "?")]
    pub counter: Option<Int>,
    #[k::cell(multiplicity = "?", nested)]
    pub mark: Option<Mark>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            counter: Some(0),
            mark: Some(Mark { seen: 0 }),
        }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;

    seq: Seq(s1, s2) => k::k![s1, s2];
}

k::rules! {
    for Machine;
    use Cmd::*;

    /// Create the counter; a second `enable` is stuck.
    enable: {
        k: [Enable(), ..],
        counter: None
    } => {
        k: [..],
        counter: Some(0)
    };

    /// Increment the counter in place.
    inc: {
        k: [Inc(), ..],
        counter: Some(n)
    } => {
        k: [..],
        counter: Some(int::add(n, 1))
    };

    /// Write the counter to the computation cell; the counter is only read.
    read: {
        k: [Read(), ..],
        counter: Some(n)
    } => {
        k: [n, ..]
    };

    /// Delete the counter.
    disable: {
        k: [Disable(), ..],
        counter: Some(_)
    } => {
        k: [..],
        counter: None
    };

    /// Create the mark from the counter.
    stamp: {
        k: [Stamp(), ..],
        counter: Some(n),
        mark: None,
    } => {
        k: [..],
        mark: Some(k::fragment![Mark { seen: n }]),
    };

    /// Move the mark's value to the computation cell and delete the mark.
    peek: {
        k: [Peek(), ..],
        mark: Some(Mark { seen: s }),
    } => {
        k: [s, ..],
        mark: None,
    };
}

/// `dec` in the reference spelling.
#[k::rule(label = "dec")]
pub fn dec(
    n: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Dec(), tail @ ..),
        counter: Some(k::configuration::Cell(n)),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        counter: Some(k::configuration::Cell(int::sub(n, 1))),
        ..state
    }
}
