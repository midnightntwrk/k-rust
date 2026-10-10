//! Explicit Rust-authored definition of the IMP state slice.
//!
//! The independent semantic oracle is `../../fixtures/expr.k` plus
//! `../../fixtures/calc.k`. KRS attributes and compiler-owned term/state
//! islands carry object-language meaning while every declaration remains
//! visible to rustc and rust-analyzer through the renamed `k` facade.

use k::builtin::{Bool, Id, Int, Map, bool, int};
use k::{KResult, KResultSort, Term};
// Whole-rule parsing consumes these compiler-owned islands before rustc's
// ordinary unused-import analysis can observe the invocations.
#[allow(unused_imports)]
use k::{cells, map};

#[k::sort(alias = Expr)]
#[k::bracket("({value})")]
pub trait ExprSort {}
pub type Expr = Term<dyn ExprSort>;

#[k::sort(alias = Value, parents = [Expr, KResult])]
pub trait ValueSort: ExprSort + KResultSort {}
pub type Value = Term<dyn ValueSort>;

// These ordinary impls expose familiar Rust-side marker membership. Only the
// attributed `Value` impls declare builtin object-language subsorts; `Value`'s
// parents supply its direct `Expr` and `KResult` grammar edges.
impl ExprSort for Int {}

#[k::subsort(sort = Value)]
impl ValueSort for Int {}

impl ExprSort for Bool {}

#[k::subsort(sort = Value)]
impl ValueSort for Bool {}

#[k::constructor(
    sort = Expr,
    syntax = "-{value}",
    group = "prefix",
    format = "%1%2",
)]
#[k::strict(sequence = [value], result = KResult)]
pub struct Neg {
    pub value: Term<dyn ExprSort>,
}

#[k::constructor(
    sort = Expr,
    syntax = "!{value}",
    group = "prefix",
    format = "%1%2",
)]
#[k::strict(sequence = [value], result = KResult)]
pub struct Not {
    pub value: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} * {rhs}", group = "multiplicative")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Mul {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} / {rhs}", group = "multiplicative")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Div {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} + {rhs}", group = "additive")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Add {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} - {rhs}", group = "additive")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Sub {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} >= {rhs}", group = "comparison")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Ge {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} > {rhs}", group = "comparison")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Gt {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} <= {rhs}", group = "comparison")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Le {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} < {rhs}", group = "comparison")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Lt {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} == {rhs}", group = "equality")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Eq {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} != {rhs}", group = "equality")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Ne {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} && {rhs}", group = "conjunction")]
#[k::strict(sequence = [lhs], result = KResult)]
pub struct And {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} || {rhs}", group = "disjunction")]
#[k::strict(sequence = [lhs], result = KResult)]
pub struct Or {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
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
#[k::subsort(sort = Expr)]
impl ExprSort for Id {}

#[k::sort(alias = Stmt)]
pub trait StmtSort {}
pub type Stmt = Term<dyn StmtSort>;

#[k::constructor(
    sort = Stmt,
    syntax = "{name} = {value};",
    group = "stmt",
    format = "%1 %2 %3%4",
)]
#[k::strict(sequence = [value], result = KResult)]
pub struct Assign {
    pub name: Term<Id>,
    pub value: Term<dyn ExprSort>,
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
    pub first: Term<dyn StmtSort>,
    pub second: Term<dyn StmtSort>,
}

k::precedence! {
    stmt > seq_stmt
}

k::associativity! {
    right: seq_stmt;
}

/// The oracle's fixed two-cell calculation state.
#[k::configuration]
pub struct Machine {
    #[k::cell(color = "green")]
    pub k: k::configuration::KCell<k::builtin::KSequence>,
    #[k::cell(color = "yellow")]
    pub env: k::configuration::Cell<Map<Id, Term<dyn ValueSort>>>,
}

#[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]
impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: Term<dyn StmtSort>,
        #[k::config_var(name = "ENV")] environment: Map<Id, Term<dyn ValueSort>>,
    ) -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![program]),
            env: k::configuration::Cell::new(environment),
        }
    }
}

#[k::rule]
pub fn eval_neg(Neg { value }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    int::sub(0, value)
}

#[k::rule]
pub fn eval_not(Not { value }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    bool::not(value)
}

#[k::rule]
pub fn eval_add(Add { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    int::add(lhs, rhs)
}

#[k::rule]
pub fn eval_sub(Sub { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    int::sub(lhs, rhs)
}

#[k::rule]
pub fn eval_mul(Mul { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    int::mul(lhs, rhs)
}

#[k::rule]
pub fn eval_div(Div { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    int::div(lhs, rhs)
}

#[k::rule]
pub fn eval_ge(Ge { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    int::ge(lhs, rhs)
}

#[k::rule]
pub fn eval_gt(Gt { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    int::gt(lhs, rhs)
}

#[k::rule]
pub fn eval_le(Le { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    int::le(lhs, rhs)
}

#[k::rule]
pub fn eval_lt(Lt { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    int::lt(lhs, rhs)
}

#[k::rule]
pub fn eval_bool_eq(Eq { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    bool::eq(lhs, rhs)
}

#[k::rule]
pub fn eval_int_eq(Eq { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    int::eq(lhs, rhs)
}

#[k::rule]
pub fn eval_bool_ne(Ne { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    bool::ne(lhs, rhs)
}

#[k::rule]
pub fn eval_int_ne(Ne { lhs, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    int::ne(lhs, rhs)
}

#[k::rule]
pub fn and_true(And { lhs: true, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    rhs
}

#[k::rule]
pub fn and_false(And { lhs: false, rhs: _ }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    false
}

#[k::rule]
pub fn or_true(Or { lhs: true, rhs: _ }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    true
}

#[k::rule]
pub fn or_false(Or { lhs: false, rhs }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    rhs
}

/// `[step]`: expose the right-associated statement pair as K sequencing.
#[k::rule]
pub fn step(
    first: Term<dyn StmtSort>,
    second: Term<dyn StmtSort>,
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
    value: Term<dyn ValueSort>,
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
    value: Term<dyn ValueSort>,
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
