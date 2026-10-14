//! A claim cannot name a private production: claims are emitted into the
//! generated `<MAIN>-SPEC` module, and K's private syntax is invisible to
//! every importing module, proof modules included.

use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Inc))]
pub enum ExpSyntax {
    #[k::syntax("inc {value}")]
    Inc { value: Exp },
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Wrap))]
enum Helper {
    #[k::syntax("helper({value})")]
    Wrap { value: Exp },
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

k::rules! {
    for Exp;
    use ExpSyntax::*;

    inc: Inc { value } => Helper::Wrap { value };
}

k::rules! {
    for Exp;
    use Helper::*;

    wrap_int: Wrap { value } => int::add(value, 1) where value: Int;
}

mod claims {
    use super::{Helper, Machine};

    #[k::claim(all_paths, label = "helper-one")]
    fn helper_one(
        k::cells! {
            k: k::configuration::KCell(Helper::Wrap(1), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        k::cells! {
            k: k::configuration::KCell(2, ..tail),
            ..state
        }
    }
}
