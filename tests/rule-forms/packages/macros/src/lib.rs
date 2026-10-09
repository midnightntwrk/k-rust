//! One-way macros and recursive aliases (KF-028), after K tutorial lesson 2.1.
//!
//! A K macro rewrites the definition's rules and the input program once,
//! before anything runs; it is not a runtime step. KRS calls it `desugar`:
//! the production carries `#[k::desugar]`, the emitted K says `[macro]`, and
//! each `#[k::desugar] fn` is one clause. `recursive` is a property of the
//! production (`[macro-rec]`, `[alias-rec]`): it lets an expansion apply
//! again to its own output.
//!
//! - `unless (c) s` desugars to `if (c) {} else s`, so
//!   `unless (false) x = 1;` behaves as the if/else form.
//! - `int x, y, z;` is `#[k::desugar(recursive)]` and expands fully to
//!   `var x; var y; var z;`; `decl x, y, z;` has the same clauses with a plain
//!   `#[k::desugar]`, so it expands one step to `var x; decl y, z;`, and the
//!   run stops at `decl y, z;`.
//! - `nest(1, 2)` is `#[k::alias(recursive)]`: it expands forward to
//!   `pair(1, pair(2, nil))`, and K prints that value backwards as
//!   `nest(1, 2)`.
//! - `twin` and `anyPair` are desugars used as patterns (KF-046): their
//!   clauses list `unbound_variables`, K's `unboundVariables`, because their
//!   results name variables (`n`, `rest`) and wildcards (`_`) that only the
//!   rule using them binds. `twin a = pair(3, pair(3, 7));` matches
//!   `pair(N, pair(N, Rest))` and sets `a`; `twin a = pair(3, pair(4, 7));`
//!   is stuck; `ispair b = pair(1, nil);` matches `pair(_, _)` and
//!   `ispair b = 5;` is stuck.

use k::builtin::{Bool, Id, Int, KSequence, Map, map};
use k::{KResult, Term};

k::sorts! {
    Expr;
    Value: Expr + KResult;
    impl Value for Int, Bool;
    Stmt;
}

/// A nonempty comma-separated list of identifiers.
#[k::syntax_list(separator = ",", non_empty)]
pub enum Ids {
    Cons { head: Id, tail: Ids },
    Nil(),
}

/// A comma-separated list of integers.
#[k::syntax_list(separator = ",")]
pub enum Ints {
    Cons { head: Int, tail: Ints },
    Nil(),
}

/// Integer lists as values; `nest(..)` is their recursive alias.
#[k::constructors(sort = Value, result = KResult)]
#[k::precedence((Pair, Nil, Nest))]
#[rustfmt::skip]
pub enum Data {
    #[k::syntax("pair({head}, {tail})")]
    Pair { head: Int, tail: Value },

    #[k::syntax("nil")]
    Nil(),

    #[k::syntax("nest({items})")] #[k::alias(recursive)]
    Nest { items: Ints },
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(
    stmt (Assign, Decl, IfThenElse, EmptyBlock)
    > right seq_stmt (Sequence)
)]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("{name} = {value};")]
    Assign { name: Id, value: Value },

    #[k::syntax("var {name};")]
    Decl { name: Id },

    #[k::syntax("if ({condition}) {then_branch} else {else_branch}")]
    IfThenElse { condition: Expr, then_branch: Stmt, else_branch: Stmt },

    #[k::syntax("{{}}")]
    EmptyBlock(),

    #[k::syntax("{first} {second}")]
    Sequence { first: Stmt, second: Stmt },
}

/// Statement sugar: every variant is expanded before anything runs.
#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Unless, DeclareMany, DeclareOnce))]
#[rustfmt::skip]
pub enum Sugar {
    #[k::syntax("unless ({c}) {s}")] #[k::desugar]
    Unless { c: Expr, s: Stmt },

    #[k::syntax("int {names};")] #[k::desugar(recursive)]
    DeclareMany { names: Ids },

    #[k::syntax("decl {names};")] #[k::desugar]
    DeclareOnce { names: Ids },
}

#[k::desugar]
fn unless(k::term![Sugar::Unless(c, s)]: Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::IfThenElse(c, StmtSyntax::EmptyBlock(), s)
}

#[k::desugar]
fn declare_last(k::term![Sugar::DeclareMany(Ids::Cons(x, Ids::Nil()))]: Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Decl(x)
}

#[k::desugar]
fn declare_many(
    k::term![Sugar::DeclareMany(Ids::Cons(x, Ids::Cons(y, rest)))]: Term<Stmt>,
) -> Term<Stmt> {
    StmtSyntax::Sequence(StmtSyntax::Decl(x), Sugar::DeclareMany(Ids::Cons(y, rest)))
}

#[k::desugar]
fn declare_once_last(
    k::term![Sugar::DeclareOnce(Ids::Cons(x, Ids::Nil()))]: Term<Stmt>,
) -> Term<Stmt> {
    StmtSyntax::Decl(x)
}

#[k::desugar]
fn declare_once(
    k::term![Sugar::DeclareOnce(Ids::Cons(x, Ids::Cons(y, rest)))]: Term<Stmt>,
) -> Term<Stmt> {
    StmtSyntax::Sequence(StmtSyntax::Decl(x), Sugar::DeclareOnce(Ids::Cons(y, rest)))
}

/// Value shapes written only in rule patterns, expanded into them.
#[k::constructors(sort = Value, result = KResult)]
#[k::precedence((Twin, AnyPair))]
#[rustfmt::skip]
pub enum Shape {
    #[k::syntax("twin")] #[k::desugar]
    Twin(),

    #[k::syntax("anyPair")] #[k::desugar]
    AnyPair(),
}

/// Statements that test a value against a shape.
#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((TestTwin, TestPair))]
#[rustfmt::skip]
pub enum Probe {
    #[k::syntax("twin {name} = {value};")]
    TestTwin { name: Id, value: Value },

    #[k::syntax("ispair {name} = {value};")]
    TestPair { name: Id, value: Value },
}

#[k::desugar(unbound_variables = [n, rest])]
fn twin(k::term![Shape::Twin()]: Term<Value>) -> Term<Value> {
    Data::Pair(n, Data::Pair(n, rest))
}

#[k::desugar(unbound_variables = [_])]
fn any_pair(k::term![Shape::AnyPair()]: Term<Value>) -> Term<Value> {
    Data::Pair(_, _)
}

#[k::alias]
fn nest_nil(k::term![Data::Nest(Ints::Nil())]: Term<Value>) -> Term<Value> {
    Data::Nil()
}

#[k::alias]
fn nest_cons(k::term![Data::Nest(Ints::Cons(i, is))]: Term<Value>) -> Term<Value> {
    Data::Pair(i, Data::Nest(is))
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Value>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: k::map![],
        }
    }
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    /// Expose the right-associated statement pair as K sequencing.
    step    : Sequence(s1, s2)         => k::k![s1, s2];
    /// Select the true branch.
    if_true : IfThenElse(true, s1, _)  => s1;
    /// Select the false branch.
    if_false: IfThenElse(false, _, s2) => s2;
    /// Remove an empty block from the computation cell.
    done    : EmptyBlock()             => ();
}

k::rules! {
    for Stmt;
    use Probe::*;

    /// A pair whose first two integers are equal sets `name` to 1.
    is_twin: TestTwin(name, Shape::Twin())    => StmtSyntax::Assign(name, 1);
    /// Any pair sets `name` to 1.
    is_pair: TestPair(name, Shape::AnyPair()) => StmtSyntax::Assign(name, 1);
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    /// Declare a variable with value 0.
    declare: {
        k: [Decl(name), ..],
        env: e,
    } => {
        k: [..],
        env: map::update(e, name, 0),
    };

    /// Consume an assignment and update the environment map.
    assign: {
        k: [Assign(name, value), ..],
        env: e,
    } => {
        k: [..],
        env: map::update(e, name, value),
    };
}
