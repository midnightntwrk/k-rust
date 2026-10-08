//! Readable machine rules that leave the computation cell out (KF-015).
//!
//! A K rule names only the cells it needs, and that includes `<k>`: `burn`
//! names `fuel` and `acc`, so it frames `k` like every other omitted cell and
//! fires whenever its guard holds, interleaved with the program. Starting
//! from fuel 3 and acc 0 (`-cFUEL=3 -cACC=0`) it runs three times, leaving
//! fuel 0 and acc 3 + 2 + 1 = 6.
//!
//! - `done` is erased by a `for Stmt` rule; `burn` still runs to fuel 0, and
//!   the computation cell ends empty on both routes;
//! - `report` waits for the fuel to run out and then writes `acc` to the
//!   computation cell, so both routes end with `6` there.
//!
//! The overlap check does not report `done` against `burn`: they share no
//! cell, so they commute. `report` and `burn` share `fuel` and `acc`, and
//! their guards `f > 0` and `f <= 0` are literal complements.

use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Done, Report))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("done")] Done(),
    #[k::syntax("report")] Report(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub fuel: Int,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "FUEL")] fuel: Int,
        #[k::config_var(name = "ACC")] acc: Int,
    ) -> Self {
        Self {
            k: k::k![pgm],
            fuel,
            acc,
        }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;

    done: Done() => ();
}

k::rules! {
    for Machine;
    use Cmd::*;

    /// Burn one unit of fuel into the accumulator; `k` is not touched.
    #[k::requires(int::gt(f, 0))]
    burn: {
        fuel: f,
        acc: a
    } => {
        fuel: int::sub(f, 1),
        acc: int::add(a, f)
    };

    /// Once the fuel is spent, write the accumulator to the computation cell.
    #[k::requires(int::le(f, 0))]
    report: {
        k: [Report(), ..],
        fuel: f,
        acc: a,
    } => {
        k: [a, ..],
        fuel: f,
        acc: a,
    };
}
