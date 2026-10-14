//! A syntactic list derives its symbols from the enum name (R11):
//! `intsCons` and `intsNil`, so a production named `IntsCons` collides.

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

#[k::function(total, sort = Int, syntax = "intsCons({value})")]
pub struct IntsCons {
    pub value: Term<Int>,
}
