//! Sort-parametric functions (KF-027): K's `syntax {S} S ::= choose(Bool, S, S)`.
//!
//! A K sort parameter is a Rust type parameter of a production struct with
//! exactly the bound `?Sized`; `sort = S` and `k::Term<S>` fields name it.
//! A K rule never quantifies over sorts, so each equation fixes one instance
//! with a turbofish on its head, which the emitted K writes as strict casts:
//! `choose ( true , A::Int , _::Int ) => A:Int`. Terms elsewhere need no
//! turbofish: K solves the instance from the arguments.
//!
//! - `go(7, true)` sets `<n>` to `7` and `<bit>` to `false`, and `go(7, false)`
//!   sets them to `0` and `true`: `choose` at Int and at Bool;
//! - `pick(true, 1, 2)` is `1` and `pick(false, 1, 2)` is `2`: a readable
//!   clause builds `Choose::<Exp> { .. }`, `choose` at the user sort `Exp`.

use k::builtin::{Bool, Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

/// `choose(c, t, e)` is `t` when `c` holds and `e` otherwise, at any sort.
#[k::function(total, sort = S, syntax = "choose({cond}, {then_branch}, {else_branch})")]
pub struct Choose<S: ?Sized> {
    pub cond: Term<Bool>,
    pub then_branch: Term<S>,
    pub else_branch: Term<S>,
}

#[k::equation]
fn choose_true_int(
    k::term![Choose::<Int> {
        cond: true,
        then_branch: a,
        else_branch: _
    }]: Term<Int>,
) -> Term<Int> {
    a
}

#[k::equation]
fn choose_false_int(
    k::term![Choose::<Int> {
        cond: false,
        then_branch: _,
        else_branch: b
    }]: Term<Int>,
) -> Term<Int> {
    b
}

#[k::equation]
fn choose_true_bool(
    k::term![Choose::<Bool> {
        cond: true,
        then_branch: a,
        else_branch: _
    }]: Term<Bool>,
) -> Term<Bool> {
    a
}

#[k::equation]
fn choose_false_bool(
    k::term![Choose::<Bool> {
        cond: false,
        then_branch: _,
        else_branch: b
    }]: Term<Bool>,
) -> Term<Bool> {
    b
}

#[k::equation]
fn choose_true_exp(
    k::term![Choose::<dyn ExpSort> {
        cond: true,
        then_branch: a,
        else_branch: _
    }]: Term<Exp>,
) -> Term<Exp> {
    a
}

#[k::equation]
fn choose_false_exp(
    k::term![Choose::<dyn ExpSort> {
        cond: false,
        then_branch: _,
        else_branch: b
    }]: Term<Exp>,
) -> Term<Exp> {
    b
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Go, Pick))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("go({n}, {b})")]
    Go { n: Int, b: Bool },
    #[k::syntax("pick({cond}, {first}, {second})")]
    Pick { cond: Bool, first: Exp, second: Exp },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub n: Int,
    #[k::cell]
    pub bit: Bool,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            n: -1,
            bit: true,
        }
    }
}

k::rules! {
    for Machine;
    use ExpSyntax::Go;

    /// `choose` at Int and at Bool, each instance solved from the arguments.
    go: {
        k: [Go(i, b), ..],
        n: _,
        bit: _,
    } => {
        k: [..],
        n: crate::Choose { cond: b, then_branch: i, else_branch: 0 },
        bit: crate::Choose { cond: b, then_branch: false, else_branch: true },
    };
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    /// A readable clause names the instance with the sort, `Choose::<Exp>`.
    pick: Pick(c, x, y) => crate::Choose::<Exp> { cond: c, then_branch: x, else_branch: y };
}
