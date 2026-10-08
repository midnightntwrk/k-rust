//! Syntactic lists (KF-020), after K tutorial lesson 1.12.
//!
//! `#[k::syntax_list]` declares K's `List{Int, ","}`: programs write
//! `sum(1, 2, 3)`, and the empty program text is the empty list. Rules match
//! the enum's variants, which K prints as `I , Is` and `.Ints`; `.Ints` is
//! rule syntax only, so a program cannot write it. `non_empty` makes `Alts`
//! K's `NeList`, which programs cannot write empty. The two lists derive
//! their symbols from the enum names: `intsCons`/`intsNil` and
//! `altsCons`/`altsNil`.

use k::builtin::{Int, KSequence, int};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

/// A comma-separated list of integers: `1, 2, 3`.
#[k::syntax_list(separator = ",")]
pub enum Ints {
    Cons { head: Int, tail: Ints },
    Nil(),
}

/// A nonempty `|`-separated list of integers.
#[k::syntax_list(separator = "|", non_empty)]
pub enum Alts {
    Cons { head: Int, tail: Alts },
    Nil(),
}

#[k::function(partial, sort = Int, syntax = "sum({items})")]
pub struct Sum {
    pub items: Term<Ints>,
}

#[k::equation]
fn sum_one(k::term![Sum(Ints::Cons(i, Ints::Nil()))]: Term<Int>) -> Term<Int> {
    i
}

#[k::equation]
fn sum_more(k::term![Sum(Ints::Cons(i1, Ints::Cons(i2, is)))]: Term<Int>) -> Term<Int> {
    Sum(Ints::Cons(int::add(i1, i2), is))
}

#[k::function(partial, sort = Int, syntax = "count({alts})")]
pub struct Count {
    pub alts: Term<Alts>,
}

#[k::equation]
fn count_one(k::term![Count(Alts::Cons(_, Alts::Nil()))]: Term<Int>) -> Term<Int> {
    1
}

#[k::equation]
fn count_more(k::term![Count(Alts::Cons(_, Alts::Cons(next, rest)))]: Term<Int>) -> Term<Int> {
    int::add(1, Count(Alts::Cons(next, rest)))
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}
