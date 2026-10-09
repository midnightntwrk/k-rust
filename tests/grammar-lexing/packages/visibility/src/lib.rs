//! Rust privacy is K privacy.
//!
//! `ExpSyntax` is `pub`: program syntax, visible to dependents. `Helper` is
//! not `pub`, so its production is K `private`: only this package's rules can
//! use it. A program cannot contain `helper(1)`, a dependent cannot name
//! `Helper::Wrap` (E0603), and a module importing this one cannot use it in a
//! rule, on either route.
//!
//! Token productions follow the same rule. `Label` is `pub`, so its regex is
//! program syntax and `goto done` parses; the alias `Hidden` is not, so its
//! `#`-prefixed token is K `private`: the rules below use `#done`, but a
//! program `goto #done` does not parse on either route.

use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
    impl k::KItem for Label;
}

/// Jump targets.
#[k::token(regex = r"[a-z]+")]
pub struct Label(pub String);

/// Targets only this package's rules may use.
#[allow(dead_code)]
#[k::token(regex = r"#[a-z]+")]
type Hidden = Label;

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Inc, Goto))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("inc {value}")]
    Inc { value: Exp },
    #[k::syntax("goto {target}")]
    Goto { target: Label },
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

    inc        : Inc { value }                    => Helper::Wrap { value };
    goto_done  : Goto(k::lexeme!(Label, "done"))  => Goto(k::lexeme!(Label, "#done"));
    goto_hidden: Goto(k::lexeme!(Label, "#done")) => 7;
}

k::rules! {
    for Exp;
    use Helper::*;

    wrap_int: Wrap { value } => int::add(value, 1) where value: Int;
}
