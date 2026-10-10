//! K tutorial lesson 1.21: unification and symbolic execution.
//!
//! A rule normally computes its result from what it matched.
//! `#[k::exists(x: Int)]` says the result contains an unknown integer: the
//! engine introduces a symbolic `?X` and records the `#[k::ensures]`
//! condition as a constraint on every later path. From the program `0`,
//! `zero_to_unknown` introduces `?X` with `?X =/=Int 0`, and `big_to_five`
//! applies only on the branch where `?X >=Int 10`, so symbolic execution
//! ends in two states. Concrete (LLVM) execution cannot run such a rule.
//!
//! The two rules never apply to one configuration (`0 >=Int 10` is false),
//! but KRS's overlap check compares guards only with each other, not with
//! the literal the other rule matched, so they share a `nondet` group. The
//! group is check-only: the emitted K is the lesson's.

use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

// Programs are integers, as in the lesson's `krun` of `0`.
k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Foo))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("foo")] Foo(),
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

#[k::rule(nondet = lesson, label = "zero-to-unknown")]
#[k::exists(x: Int)]
#[k::ensures(int::ne(x, 0))]
pub fn zero_to_unknown(
    k::cells! { k: k::configuration::KCell(0, tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(x, ..tail), ..state }
}

#[k::rule(nondet = lesson, label = "big-to-five")]
#[k::requires(int::ge(x, 10))]
pub fn big_to_five(
    x: Term<Int>,
    k::cells! { k: k::configuration::KCell(x, tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(5, ..tail), ..state }
}

/// The term fn form: `foo` becomes an unknown integer below five.
#[k::rule(label = "foo-bounded")]
#[k::exists(x: Int)]
#[k::ensures(int::lt(x, 5))]
pub fn foo_bounded(k::term![ExpSyntax::Foo()]: Term<Exp>) -> Term<Exp> {
    x
}

/// From `foo`, every path reaches some integer below five: here `y` is a
/// claim existential, a value the prover must exhibit (it finds the `?X` of
/// `foo-bounded`). The start `foo` is not an `Int`, so it cannot already be
/// the target: the prover must take the step before it checks `ensures`.
#[k::claim(all_paths, label = "foo-reaches-below-five")]
#[k::exists(y: Int)]
#[k::ensures(int::lt(y, 5))]
pub fn foo_reaches_below_five(
    k::cells! { k: k::configuration::KCell(ExpSyntax::Foo(), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(y, ..tail), ..state }
}

/// A gotcha, kept to pin that both engines agree on it: this claim is NOT
/// provable. From `0`, every path does reach a non-zero integer, but the
/// start `0` is itself an `Int`, so it already unifies with the target `?Y`.
/// K's reachability check stops at a state that matches the target and
/// fails there when `ensures` does not hold (`0 =/=Int 0` is false), so the
/// claim is stuck at depth 0 before any rule fires. A provable claim needs a
/// start that cannot match its target, as `foo-reaches-below-five` has.
#[k::spec_module(name = "KRS-LESSON-21-GOTCHA", imports = [crate])]
mod gotcha {
    use super::{Int, Machine, int};

    /// Stuck at depth 0: the start already matches the target.
    #[k::claim(all_paths, label = "zero-reaches-nonzero")]
    #[k::exists(y: Int)]
    #[k::ensures(int::ne(y, 0))]
    fn zero_reaches_nonzero(
        k::cells! { k: k::configuration::KCell(0, tail @ ..), state @ .. }: Machine,
    ) -> Machine {
        k::cells! { k: k::configuration::KCell(y, ..tail), ..state }
    }
}
