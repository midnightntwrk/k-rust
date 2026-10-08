//! Rule and equation priority.
//!
//! K rules are unordered; every rule has a priority (50 by default) and is
//! tried only after every rule with a lower number failed. `owise` is
//! priority 200.
//!
//! - `toss` has two transitions; `prefer_heads` at priority 40 always wins, so
//!   execution and search both end in `heads` alone.
//! - `flip` has a transition at priority 250 beside an `owise` one: owise
//!   (200) is tried first on both routes.
//! - `grade(N)` orders guarded equations by priority 50 to 54; `gradeOwise(N)`
//!   writes the same function with an `owise` fallback.

use k::Term;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Pgm: k::KItem;
    Letter: Pgm;
}

#[k::constructors(sort = Pgm, result = k::KResult)]
#[k::precedence((Toss, Heads, Tails, Flip, Low, High))]
#[rustfmt::skip]
pub enum Coin {
    #[k::syntax("toss")] Toss(),
    #[k::syntax("heads")] Heads(),
    #[k::syntax("tails")] Tails(),
    #[k::syntax("flip")] Flip(),
    #[k::syntax("low")] Low(),
    #[k::syntax("high")] High(),
}

#[k::constructors(sort = Letter, result = k::KResult)]
#[k::precedence((A, B, C, D, F))]
#[rustfmt::skip]
pub enum Grades {
    #[k::syntax("letterA")] A(),
    #[k::syntax("letterB")] B(),
    #[k::syntax("letterC")] C(),
    #[k::syntax("letterD")] D(),
    #[k::syntax("letterF")] F(),
}

#[k::function(total, sort = Letter, syntax = "grade({percentile})")]
pub struct Grade {
    pub percentile: Term<Int>,
}

#[k::function(total, sort = Letter, syntax = "gradeOwise({percentile})")]
pub struct GradeOwise {
    pub percentile: Term<Int>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Pgm) -> Self {
        Self { k: k::k![pgm] }
    }
}

#[k::rule(priority = 40)]
fn prefer_heads(k::term![Coin::Toss()]: Term<Pgm>) -> Term<Pgm> {
    k::term![Coin::Heads()]
}

#[k::rule]
fn tails(k::term![Coin::Toss()]: Term<Pgm>) -> Term<Pgm> {
    k::term![Coin::Tails()]
}

k::rules! {
    for Pgm;
    use Coin::*;

    #[k::rule(priority = 250)]
    flip_low : Flip() => Low();
    #[k::rule(owise)]
    flip_high: Flip() => High();
}

#[k::requires(int::ge(percentile, 90))]
#[k::equation(priority = 50)]
fn grade_a(k::term![Grade(percentile)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::A()]
}

#[k::requires(int::ge(percentile, 80))]
#[k::equation(priority = 51)]
fn grade_b(k::term![Grade(percentile)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::B()]
}

#[k::requires(int::ge(percentile, 70))]
#[k::equation(priority = 52)]
fn grade_c(k::term![Grade(percentile)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::C()]
}

#[k::requires(int::ge(percentile, 60))]
#[k::equation(priority = 53)]
fn grade_d(k::term![Grade(percentile)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::D()]
}

#[k::equation(priority = 54)]
fn grade_f(k::term![Grade(_)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::F()]
}

#[k::requires(int::ge(percentile, 90))]
#[k::equation(priority = 50)]
fn grade_owise_a(k::term![GradeOwise(percentile)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::A()]
}

#[k::requires(int::ge(percentile, 80))]
#[k::equation(priority = 51)]
fn grade_owise_b(k::term![GradeOwise(percentile)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::B()]
}

#[k::requires(int::ge(percentile, 70))]
#[k::equation(priority = 52)]
fn grade_owise_c(k::term![GradeOwise(percentile)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::C()]
}

#[k::requires(int::ge(percentile, 60))]
#[k::equation(priority = 53)]
fn grade_owise_d(k::term![GradeOwise(percentile)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::D()]
}

#[k::equation(owise)]
fn grade_owise_f(k::term![GradeOwise(_)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::F()]
}
