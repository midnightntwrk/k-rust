//! A syntactic list is a closed sort: a constructor family cannot target it.

use k::builtin::{Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::syntax_list(separator = ",")]
pub enum Ints {
    Cons { head: Int, tail: Ints },
    Nil(),
}

#[k::function(partial, sort = Int, syntax = "first({items})")]
pub struct First {
    pub items: Term<Ints>,
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

#[k::constructors(sort = Ints, result = KResult)]
#[k::precedence((Empty))]
pub enum IntsSyntax {
    #[k::syntax("empty")]
    Empty(),
}
