//! A dependency package with rules but no configuration.
//!
//! `double` is a `for Exp` rule, so it rewrites the head of the computation
//! cell of a configuration this package does not declare. The configured
//! package `krs-grammar-dependency-rules` imports this package, so KRS emits
//! its configuration in `KRS-DEPENDENCY-RULES-CONFIGURATION`, which
//! `KRS-DEPENDENCY-RULES-BASE` imports instead of `KRS-DEPENDENCY-RULES`.

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
