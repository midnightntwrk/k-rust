//! An equation at priority 200 beside an `owise` equation of its function:
//! `owise` gives the value only where no other equation applies, but the
//! emitted `owise` attribute fixes no rank against priorities 200 to 254, so
//! a route that tries equations in order may try the `owise` one first.

use k::Term;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Letter: k::KItem;
}

#[k::constructors(sort = Letter, result = k::KResult)]
#[k::precedence((A, F))]
#[rustfmt::skip]
pub enum Grades {
    #[k::syntax("letterA")] A(),
    #[k::syntax("letterF")] F(),
}

#[k::function(total, sort = Letter, syntax = "grade({percentile})")]
pub struct Grade {
    pub percentile: Term<Int>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Letter) -> Self {
        Self { k: k::k![pgm] }
    }
}

#[k::requires(int::ge(percentile, 90))]
#[k::equation(priority = 200)]
fn grade_a(k::term![Grade(percentile)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::A()]
}

#[k::equation(owise)]
fn grade_f(k::term![Grade(_)]: Term<Letter>) -> Term<Letter> {
    k::term![Grades::F()]
}
