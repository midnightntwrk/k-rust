//! Explicit Rust-authored definition of the M3C IMP control-flow slice.
//!
//! The independent semantic oracle is `../../fixtures/imp.k`, layered over
//! the inherited M3B expression and calculation theory. KRS attributes and
//! compiler-owned term/state islands carry object-language meaning while every
//! declaration remains visible to rustc and rust-analyzer through `k`.

use k::Term;
use k::builtin::{Bool, Id, Int, Map, bool, int};
// Whole-rule parsing consumes these compiler-owned islands before rustc's
// ordinary unused-import analysis can observe the invocations.
#[allow(unused_imports)]
use k::{cells, map};

#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait KResult {}

#[k::sort]
#[k::bracket("({value})")]
pub trait Expr {}

#[k::sort]
pub trait Value: Expr + KResult {}

// These ordinary impls expose familiar Rust-side marker membership. Only the
// attributed `Value` impls declare builtin object-language subsorts; `Value`'s
// supertraits supply its direct `Expr` and `KResult` grammar edges.
impl KItem for Int {}
impl KResult for Int {}
impl Expr for Int {}

#[k::subsort]
impl Value for Int {}

impl KItem for Bool {}
impl KResult for Bool {}
impl Expr for Bool {}

#[k::subsort]
impl Value for Bool {}

#[k::constructor(
    sort = Expr,
    syntax = "-{value}",
    group = "prefix",
    format = "%1%2",
)]
#[k::strict(sequence = [value], result = KResult)]
pub struct Neg {
    pub value: Term<dyn Expr>,
}

#[k::constructor(
    sort = Expr,
    syntax = "!{value}",
    group = "prefix",
    format = "%1%2",
)]
#[k::strict(sequence = [value], result = KResult)]
pub struct Not {
    pub value: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} * {rhs}", group = "multiplicative")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Mul {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} / {rhs}", group = "multiplicative")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Div {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} + {rhs}", group = "additive")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Add {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} - {rhs}", group = "additive")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Sub {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} >= {rhs}", group = "comparison")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Ge {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} > {rhs}", group = "comparison")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Gt {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} <= {rhs}", group = "comparison")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Le {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} < {rhs}", group = "comparison")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Lt {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} == {rhs}", group = "equality")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Eq {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} != {rhs}", group = "equality")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Ne {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} && {rhs}", group = "conjunction")]
#[k::strict(sequence = [lhs], result = KResult)]
pub struct And {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} || {rhs}", group = "disjunction")]
#[k::strict(sequence = [lhs], result = KResult)]
pub struct Or {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

k::precedence! {
    prefix > multiplicative > additive > comparison > equality > conjunction > disjunction
}

k::associativity! {
    left: multiplicative;
    left: additive;
    left: comparison;
    left: equality;
    left: conjunction;
    left: disjunction;
}

// This after-the-fact declaration is the exact `syntax Expr ::= Id` edge in
// calc.k; `Expr` was already declared above and `Id` is a closed builtin sort.
#[k::subsort]
impl Expr for Id {}

#[k::sort]
pub trait Stmt {}

#[k::constructor(
    sort = Stmt,
    syntax = "{name} = {value};",
    group = "stmt",
    format = "%1 %2 %3%4",
)]
#[k::strict(sequence = [value], result = KResult)]
pub struct Assign {
    pub name: Term<Id>,
    pub value: Term<dyn Expr>,
}

#[k::constructor(
    sort = Stmt,
    syntax = "{first} {second}",
    // The public grammar macro currently requires Rust-identifier-shaped
    // group identities. Production lowering still preserves the exact
    // right-associative sequence role and priority relation.
    group = "seq_stmt",
    format = "%1%n%2",
)]
pub struct Sequence {
    pub first: Term<dyn Stmt>,
    pub second: Term<dyn Stmt>,
}

k::precedence! {
    stmt > seq_stmt
}

k::associativity! {
    right: seq_stmt;
}

#[k::constructor(
    sort = Stmt,
    syntax = "if ({condition}) {then_branch} else {else_branch}",
    group = "stmt",
    avoid = true,
    // K's exact source uses `% ` between items 4 and 5. KRS currently rejects
    // that escape, so this authorable spelling is an explicit surface gap.
    format = "%1 %2%3%4 %5 %6 %7",
)]
#[k::strict(sequence = [condition], result = KResult)]
pub struct IfThenElse {
    pub condition: Term<dyn Expr>,
    pub then_branch: Term<dyn Stmt>,
    pub else_branch: Term<dyn Stmt>,
}

#[k::constructor(
    sort = Stmt,
    syntax = "if ({condition}) {body}",
    group = "stmt",
    format = "%1 %2%3%4 %5",
)]
pub struct IfThen {
    pub condition: Term<dyn Expr>,
    pub body: Term<dyn Stmt>,
}

#[k::constructor(
    sort = Stmt,
    syntax = "while ({condition}) {body}",
    group = "stmt",
    format = "%1 %2%3%4 %5",
)]
pub struct While {
    pub condition: Term<dyn Expr>,
    pub body: Term<dyn Stmt>,
}

#[k::constructor(
    sort = Stmt,
    syntax = "{{{body}}}",
    group = "stmt",
    format = "%1%i%n%2%d%n%3",
)]
pub struct Block {
    pub body: Term<dyn Stmt>,
}

#[k::constructor(
    sort = Stmt,
    syntax = "{{}}",
    group = "stmt",
    format = "%1%2",
)]
pub struct EmptyBlock;

/// The oracle's fixed two-cell calculation state.
#[k::configuration]
pub struct Machine {
    #[k::cell(color = "green")]
    pub k: k::configuration::KCell<k::builtin::KSequence>,
    #[k::cell(color = "yellow")]
    pub env: k::configuration::Cell<Map<Id, Term<dyn Value>>>,
}

#[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]
impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: Term<dyn Stmt>,
        #[k::config_var(name = "ENV")] environment: Map<Id, Term<dyn Value>>,
    ) -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![program]),
            env: k::configuration::Cell::new(environment),
        }
    }
}

#[k::rule]
pub fn eval_neg(Neg { value }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::sub(0, value)
}

#[k::rule]
pub fn eval_not(Not { value }: Term<dyn Expr>) -> Term<dyn Expr> {
    bool::not(value)
}

#[k::rule]
pub fn eval_add(Add { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::add(lhs, rhs)
}

#[k::rule]
pub fn eval_sub(Sub { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::sub(lhs, rhs)
}

#[k::rule]
pub fn eval_mul(Mul { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::mul(lhs, rhs)
}

#[k::rule]
pub fn eval_div(Div { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::div(lhs, rhs)
}

#[k::rule]
pub fn eval_ge(Ge { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::ge(lhs, rhs)
}

#[k::rule]
pub fn eval_gt(Gt { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::gt(lhs, rhs)
}

#[k::rule]
pub fn eval_le(Le { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::le(lhs, rhs)
}

#[k::rule]
pub fn eval_lt(Lt { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::lt(lhs, rhs)
}

#[k::rule]
pub fn eval_bool_eq(Eq { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    bool::eq(lhs, rhs)
}

#[k::rule]
pub fn eval_int_eq(Eq { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::eq(lhs, rhs)
}

#[k::rule]
pub fn eval_bool_ne(Ne { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    bool::ne(lhs, rhs)
}

#[k::rule]
pub fn eval_int_ne(Ne { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::ne(lhs, rhs)
}

#[k::rule]
pub fn and_true(And { lhs: true, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    rhs
}

#[k::rule]
pub fn and_false(And { lhs: false, rhs: _ }: Term<dyn Expr>) -> Term<dyn Expr> {
    false
}

#[k::rule]
pub fn or_true(Or { lhs: true, rhs: _ }: Term<dyn Expr>) -> Term<dyn Expr> {
    true
}

#[k::rule]
pub fn or_false(Or { lhs: false, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    rhs
}

/// `[step]`: expose the right-associated statement pair as K sequencing.
#[k::rule]
pub fn step(
    first: Term<dyn Stmt>,
    second: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(Sequence(first, second), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(first, second, ..tail),
        ..state
    }
}

/// `[var]`: replace an identifier at the head of `k` with its mapped value.
#[k::rule]
pub fn var(
    name: Term<Id>,
    value: Term<dyn Value>,
    cells! {
        k: k::configuration::KCell(name, tail @ ..),
        env: k::configuration::Cell(map![name -> value, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(value, ..tail),
        ..state
    }
}

/// `[assign]`: consume a value assignment and update the environment map.
#[k::rule]
pub fn assign(
    name: Term<Id>,
    value: Term<dyn Value>,
    environment: Term<Map>,
    cells! {
        k: k::configuration::KCell(Assign(name, value), tail @ ..),
        env: k::configuration::Cell(environment),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![environment [ name <- value ]]),
        ..state
    }
}

/// `[if-true]`: select the true branch of an evaluated conditional.
#[k::rule(label = "if-true")]
pub fn if_true(
    then_branch: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(IfThenElse(true, then_branch, _), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(then_branch, ..tail),
        ..state
    }
}

/// `[if-false]`: select the false branch of an evaluated conditional.
#[k::rule(label = "if-false")]
pub fn if_false(
    else_branch: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(IfThenElse(false, _, else_branch), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(else_branch, ..tail),
        ..state
    }
}

/// `[if-else]`: normalize the no-else form with an explicit empty branch.
#[k::rule(label = "if-else")]
pub fn if_else(
    condition: Term<dyn Expr>,
    body: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(IfThen(condition, body), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(IfThenElse(condition, body, EmptyBlock()), ..tail),
        ..state
    }
}

/// `[while]`: unfold one loop test without making the constructor strict.
#[k::rule(label = "while")]
pub fn while_loop(
    condition: Term<dyn Expr>,
    body: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(While(condition, body), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(
            IfThen(
                condition,
                Block(Sequence(body, While(condition, body)))
            ),
            ..tail
        ),
        ..state
    }
}

/// `[block]`: expose a nonempty block body followed by an empty block.
#[k::rule(label = "block")]
pub fn block(
    body: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(Block(body), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(body, EmptyBlock(), ..tail),
        ..state
    }
}

/// `[done]`: remove an empty block from the computation cell.
#[k::rule(label = "done")]
pub fn done(
    cells! {
        k: k::configuration::KCell(EmptyBlock(), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(..tail),
        ..state
    }
}
