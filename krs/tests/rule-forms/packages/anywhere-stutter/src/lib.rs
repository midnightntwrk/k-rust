//! Anywhere rules that rewrite what they wrote.
//!
//! An anywhere rule replaces the application its subject matches wherever it
//! occurs. `stutter` (single-body) and `stutter_long` (its result written
//! apart) write `go` where their subject has any first argument, so their
//! result is a term their subject matches again: the rewriting has no end, and
//! no state of a run is final. `swap_ab` and `swap_ba` rewrite into each
//! other, a two-cycle, which has no end either. The gate pins what k-rust's
//! run reports for each, a known wrong output (NT-41-1): it ends the one-rule
//! rewrites after one application and reports the state stuck, at a term the
//! rule still matches, and it runs the two-cycle without end, `--depth`
//! notwithstanding.

use k::Term;
use k::builtin::KSequence;

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = k::KResult)]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("a")] A(),
    #[k::syntax("b")] B(),
    #[k::syntax("go")] Go(),
    #[k::syntax("wrap({inner})")] Wrap { inner: Stmt },
    #[k::syntax("p({first}, {second})")] P { first: Stmt, second: Stmt },
    #[k::syntax("r({first}, {second})")] R { first: Stmt, second: Stmt },
    #[k::syntax("q({first}, {second})")] Q { first: Stmt, second: Stmt },
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

#[k::rule(anywhere, label = "stutter")]
fn stutter(k::term![StmtSyntax::P(k::rewrite!(_ => StmtSyntax::Go()), _)]: Term<Stmt>) {}

#[k::rule(anywhere, label = "stutter-long")]
fn stutter_long(k::term![StmtSyntax::R(_, y)]: Term<Stmt>) -> Term<Stmt> {
    k::term![StmtSyntax::R(StmtSyntax::Go(), y)]
}

#[k::rule(anywhere, label = "swap-ab")]
fn swap_ab(
    k::term![StmtSyntax::Q(
        k::rewrite!(StmtSyntax::A() => StmtSyntax::B()),
        _
    )]: Term<Stmt>,
) {
}

#[k::rule(anywhere, label = "swap-ba")]
fn swap_ba(
    k::term![StmtSyntax::Q(
        k::rewrite!(StmtSyntax::B() => StmtSyntax::A()),
        _
    )]: Term<Stmt>,
) {
}
