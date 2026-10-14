//! A sort with two `fresh_generator` functions.

use k::Term;
use k::builtin::{Int, KSequence};

k::sorts! {
    Pgm: k::KItem;
    Loc;
}

#[k::constructors(sort = Loc, result = k::KResult)]
#[k::precedence((Loc))]
#[rustfmt::skip]
pub enum LocSyntax {
    #[k::syntax("loc({n})")] Loc { n: Int },
}

#[k::constructors(sort = Pgm, result = k::KResult)]
#[k::precedence((New, Holds))]
#[rustfmt::skip]
pub enum Stmt {
    #[k::syntax("new")] New(),
    #[k::syntax("holds({loc})")] Holds { loc: Loc },
}

#[k::function(total, fresh_generator, sort = Loc, syntax = "freshLoc({seed})")]
pub struct FreshLoc {
    pub seed: Term<Int>,
}

#[k::function(total, fresh_generator, sort = Loc, syntax = "otherLoc({seed})")]
pub struct OtherLoc {
    pub seed: Term<Int>,
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

#[k::fresh(l: Loc)]
#[k::rule]
fn allocate(k::term![Stmt::New()]: Term<Pgm>) -> Term<Pgm> {
    Stmt::Holds(l)
}
