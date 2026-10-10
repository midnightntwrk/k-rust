//! A dependency whose `for Exp` rule needs the configuration of the package
//! that imports it, so that configuration gets a module of its own.

use k::KResult;
use k::builtin::{Int, int};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Double))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("double {value}")]
    Double { value: Int },
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    double: Double { value: v } => int::add(v, v);
}
