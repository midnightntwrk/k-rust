//! Rust privacy is K privacy.
//!
//! `ExpSyntax` is `pub`: program syntax, visible to dependents. `Helper` is
//! not `pub`, so its production is K `private`: only this package's rules can
//! use it. A program cannot contain `helper(1)`, a dependent cannot name
//! `Helper::Wrap` (E0603), and a module importing this one cannot use it in a
//! rule, on either route.

use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Inc))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("inc {value}")]
    Inc { value: Exp },
}

/// Rule machinery private to this package. Only K rules construct it, so
/// rustc sees no Rust use of the variant.
#[allow(dead_code)]
#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Wrap))]
#[rustfmt::skip]
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
