//! Typed binders on rule fns (KF-009).
//!
//! A typed parameter `x: S` before the subject declares the binder `x` at the
//! sort `S`, which K writes `X:S`. In a K pattern `X:S` is a runtime test: the
//! rule matches only when the term bound to `X` has sort `S`. A rule fn
//! declares no binders, and every sort is inferred, or all of them, in the
//! order they first occur in the subject. KRS has no strict cast `::S`: rule
//! bodies are resolved Rust paths, never parsed by K, so there is nothing to
//! disambiguate.
//!
//! - `isExpression(e)` is `true` when `e` is an `Exp` (`_e: Exp` narrows the
//!   `Phrase` field) and `false` otherwise, by an `owise` equation without a
//!   binder list: `isExpression(1)` and `isExpression(1 + 2)` are `true`,
//!   `isExpression({})` and `isExpression(true)` are `false`;
//! - `bar(i)` with `i: Int` steps while `i < 3` through the projection
//!   `{foo(I +Int 1)}:>Int`, so `bar(0)` ends in `bar(3)`; `bar(1 + 2)` is an
//!   `Exp` but not an `Int`, so it does not match;
//! - `baz(i)` is `{foo(I)}:>Int`: `baz(4)` is `4`, while `foo(12)` is the block
//!   `{}`, not an `Int`, so `baz(12)` is undefined.

use k::Term;
use k::builtin::{Bool, Int, KSequence, int};

k::sorts! {
    Phrase;
    Exp: Phrase;
    impl Exp for Int;
    impl Phrase for Bool;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Bar, Baz, Add))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("bar({value})")]
    Bar { value: Exp },
    #[k::syntax("baz({value})")]
    Baz { value: Exp },
    #[k::syntax("{lhs} + {rhs}")]
    Add { lhs: Exp, rhs: Exp },
}

#[k::constructors(sort = Phrase, result = k::KResult)]
#[k::precedence((Block))]
#[rustfmt::skip]
pub enum PhraseSyntax {
    #[k::syntax("{{}}")]
    Block(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Phrase) -> Self {
        Self { k: k::k![pgm] }
    }
}

/// Whether a phrase is an expression.
#[k::function(total, sort = Bool, syntax = "isExpression({phrase})")]
pub struct IsExpression {
    pub phrase: Term<Phrase>,
}

/// The exhaustive binder list declares `_e` at `Exp`: `isExpression(_E:Exp)`.
#[k::equation]
fn is_expression_exp(_e: Exp, k::term![IsExpression(_e)]: Term<Bool>) -> Term<Bool> {
    true
}

/// No binder list: the wildcard's sort is inferred.
#[k::equation(owise)]
fn is_expression_other(k::term![IsExpression(_)]: Term<Bool>) -> Term<Bool> {
    false
}

/// `foo(i)` is `i` below 10 and the block `{}` otherwise.
#[k::function(total, sort = Phrase, syntax = "foo({value})")]
pub struct Foo {
    pub value: Term<Int>,
}

#[k::equation]
#[k::requires(int::lt(i, 10))]
fn foo_small(i: Term<Int>, k::term![Foo(i)]: Term<Phrase>) -> Term<Phrase> {
    i
}

#[k::equation(owise)]
fn foo_large(k::term![Foo(_)]: Term<Phrase>) -> Term<Phrase> {
    PhraseSyntax::Block()
}

/// `bar(I:Int) => bar({foo(I:Int +Int 1)}:>Int)`: `i: Int` narrows the `Exp` field.
#[k::rule]
#[k::requires(int::lt(i, 3))]
fn bar_step(i: Term<Int>, k::term![ExpSyntax::Bar { value: i }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Bar {
        value: k::project!(Int, Foo(int::add(i, 1))),
    }
}

/// `baz(I:Int) => {foo(I:Int)}:>Int`, undefined when `foo` returns the block.
#[k::rule]
fn baz_step(i: Term<Int>, k::term![ExpSyntax::Baz { value: i }]: Term<Exp>) -> Term<Exp> {
    k::project!(Int, Foo(i))
}
