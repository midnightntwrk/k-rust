//! Contexts that constrain another cell (KF-021), after the K manual's
//! translation-phase example.
//!
//! The `evaluate` cell selects the evaluation strategy. Two context aliases
//! share the name `translate`, K's
//!
//! ```k
//! context alias [translate]: <k> HERE ... </k> <evaluate> false </evaluate>
//! context alias [translate]: <k> HERE ... </k> <evaluate> true </evaluate> [result(ExecResult)]
//! ```
//!
//! and `twice` is strict through them: when `evaluate` is false its operand
//! is evaluated to a `KResult`, and when it is true to an `ExecResult`, which
//! a variable already is. The `cells!` context `assign_target` evaluates the
//! target of `=` only when `evaluate` is true. HOLE and HERE lie in `k`:
//! heating moves the hole to the front of the computation.

use k::KResult;
use k::builtin::{Bool, Id, Int, KSequence, Map, int};
use k::{Term, map};

k::sorts! {
    #[k::bracket("(", ")")]
    Exp;
    impl Exp for Id;
    Value: Exp + KResult;
    impl Value for Int;
    ExecResult: Exp;
    impl ExecResult for Int, Id;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Twice) > left (Add) > (Assign))]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("twice({operand})")] #[k::strict(using = translate_value)]
    Twice { operand: Exp },
    #[k::syntax("{lhs} + {rhs}")]
    Add { lhs: Exp, rhs: Exp },
    #[k::syntax("{target} = {value}")]
    Assign { target: Exp, value: Exp },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub evaluate: Bool,
    #[k::cell]
    pub env: Map<Id, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp, evaluate: Bool, env: Map<Id, Int>) -> Self {
        Self {
            k: k::k![pgm],
            evaluate,
            env,
        }
    }
}

/// Outside translation, evaluate to a `KResult`.
#[k::context_alias(name = translate, here = site)]
fn translate_value(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        evaluate: k::configuration::Cell(false),
        state @ ..
    }: Machine,
) {
}

/// During translation, evaluate to an `ExecResult`.
#[k::context_alias(name = translate, here = site, result = ExecResult)]
fn translate_exec(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        evaluate: k::configuration::Cell(true),
        state @ ..
    }: Machine,
) {
}

/// During translation, evaluate the target of `=` to an `ExecResult`.
#[k::context(hole = h, result = ExecResult)]
fn assign_target(
    h: Exp,
    k::cells! {
        k: k::configuration::KCell(Op::Assign(h, _), ..),
        evaluate: k::configuration::Cell(true),
        state @ ..
    }: Machine,
) {
}

k::rules! {
    for Exp;
    use Op::*;

    add  : Add(lhs, rhs)  => int::add(lhs, rhs)         where lhs: Int, rhs: Int;
    twice: Twice(operand) => int::add(operand, operand) where operand: Int;
}

/// `[lookup]`: read a variable.
#[k::rule(label = "lookup")]
pub fn lookup(
    name: Term<Id>,
    value: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(k::rewrite!(name => value), ..),
        env: k::configuration::Cell(map![name -> value, ..]),
        state @ ..
    }: Machine,
) {
}

/// `[twice-name]`: during translation, `twice(x)` becomes the code `x + x`.
#[k::rule(label = "twice-name")]
pub fn twice_name(
    name: Term<Id>,
    k::cells! {
        k: k::configuration::KCell(k::rewrite!(Op::Twice(name) => Op::Add(name, name)), ..),
        evaluate: k::configuration::Cell(true),
        state @ ..
    }: Machine,
) {
}
