//! Explicit Rust-authored definition of the IMP expression slice.
//!
//! It mirrors the upstream IMP `expr.k` module. This package is ordinary
//! rustc-valid source: KRS attributes attach object-language meaning while
//! Rust traits, records, functions, imports, and aliases remain visible to
//! rust-analyzer and other standard Rust tooling.

use k::builtin::{Bool, Int, bool, int};
use k::{KResult, KResultSort, Term};

#[k::sort(alias = Expr)]
#[k::bracket("({value})")]
pub trait ExprSort {}
pub type Expr = Term<dyn ExprSort>;

#[k::sort(alias = Value, parents = [Expr, KResult])]
pub trait ValueSort: ExprSort + KResultSort {}
pub type Value = Term<dyn ValueSort>;

// These ordinary impls expose familiar Rust-side marker membership. Only the
// attributed `Value` impls below declare builtin object-language subsorts;
// `Value`'s parents supply its direct `Expr` and `KResult` grammar edges.
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

#[k::configuration(root = "expression")]
pub struct Machine {
    pub k: k::configuration::KCell<k::builtin::KSequence>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] program: Term<dyn ExprSort>) -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![program]),
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

