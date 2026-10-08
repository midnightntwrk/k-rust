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

/// From `0`, every path reaches some non-zero integer: here `y` is a claim
/// existential, a value the prover must exhibit (it finds `?X`).
#[k::claim(all_paths, label = "zero-reaches-nonzero")]
#[k::exists(y: Int)]
#[k::ensures(int::ne(y, 0))]
pub fn zero_reaches_nonzero(
    k::cells! { k: k::configuration::KCell(0, tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(y, ..tail), ..state }
}
