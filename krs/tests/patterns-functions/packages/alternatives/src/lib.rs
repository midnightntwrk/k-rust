//! `A | B`: K's `#Or` (KF-030).
//!
//! In a left-hand side, `Red() | Green() | Blue()` matches what any of its
//! alternatives matches. K writes `( red() #Or green() #Or blue() )`, always
//! parenthesised. Every alternative binds the same names, as rustc requires,
//! and KRS rejects alternatives that could match one term with different
//! bindings, where Rust's first-match reading and K's "any of these" reading
//! would disagree.
//!
//! - `color(green())` is `1` by a readable clause with nested alternatives,
//!   and `color(3)` is stuck;
//! - `red()` is `1` by a readable clause whose whole subject is an
//!   or-pattern;
//! - `code(blue())` is `1` by an equation;
//! - `pick(pair(5, green()))` is `5`: both alternatives bind `x`.

use k::KResult;
use k::Term;
use k::builtin::{Bool, Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Color, Pick, Pair, Red, Green, Blue))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("color({c})")]
    Color { c: Exp },
    #[k::syntax("pick({p})")]
    Pick { p: Exp },
    #[k::syntax("pair({fst}, {snd})")]
    Pair { fst: Exp, snd: Exp },
    #[k::syntax("red()")]
    Red(),
    #[k::syntax("green()")]
    Green(),
    #[k::syntax("blue()")]
    Blue(),
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

/// The code of a primary colour.
#[k::function(partial, sort = Int, syntax = "code({c})")]
pub struct ColorCode {
    pub c: Term<Exp>,
}

/// `code(( red() #Or green() #Or blue() ))` is `1`.
#[k::equation]
fn code_rgb(
    k::term![ColorCode(
        ExpSyntax::Red() | ExpSyntax::Green() | ExpSyntax::Blue()
    )]: Term<Int>,
) -> Term<Int> {
    1
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    /// `color(( red() #Or green() #Or blue() ))` is `1`.
    rgb    : Color(Red() | Green() | Blue())         => 1;
    /// A whole subject: `( red() #Or green() #Or blue() )` is `1`.
    primary: Red() | Green() | Blue()                => 1;
    /// Both alternatives bind `x`, and no term matches both.
    pick   : Pick(Pair(x, Red()) | Pair(x, Green())) => x;
}
