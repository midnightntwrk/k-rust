//! A raw K rule that K cannot parse (KF-037): the native route fails closed,
//! naming the `raw_k!` invocation.

use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

/// Doubling, whose raw rule below does not parse.
#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Double))]
#[rustfmt::skip]
pub enum Doubling {
    #[k::syntax("double({value})")] #[k::strict]
    Double { value: Exp },
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

k::raw_k!(r#"rule <k> double(I:Int) => I +Int ... </k>"#);
