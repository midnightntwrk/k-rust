//! A term-shaped single-body rule (KF-011).
//!
//! `unmark_left` returns `()`: its `k::term!` subject is the whole rule, and
//! `k::rewrite!` marks the one argument that changes. The emitted K is K's
//! local form, `rule pair ( (marked ( Value:Exp ) => Value:Exp) , _ )`, and
//! the term rule is completed at the head of the computation cell like any
//! other. The right argument is the frame; it occurs once, so it is `_` (a
//! named variable that K sees once is unused).

use k::Term;
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    impl Exp for Int;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Pair, Marked))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("pair({left}, {right})")]
    Pair { left: Exp, right: Exp },
    #[k::syntax("marked({value})")]
    Marked { value: Exp },
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

/// Remove one mark from the left of a pair; the right is the frame.
#[k::rule(label = "unmark-left")]
pub fn unmark_left(
    k::term![ExpSyntax::Pair(
        k::rewrite!(ExpSyntax::Marked(value) => value),
        _
    )]: Term<Exp>,
) {
}
