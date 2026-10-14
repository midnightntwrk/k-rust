//! Builtin SET operations, and `list::contains`: one function and one equation
//! per operation.
//!
//! K has no SET-SYNTAX module, so a program cannot contain a set; each function
//! builds its sets from Int arguments and returns an Int or a Bool.
//! `set::to_list` and `set::from_list` come from K's `COLLECTIONS` module.

use k::builtin::{Bool, Int, KSequence, list, set};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
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

/// `set::difference`, `-Set`: the size of `{a, b} - {b}`.
#[k::function(total, sort = Int, syntax = "difference({a}, {b})")]
pub struct Difference {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn difference(k::term![Difference(a, b)]: Term<Int>) -> Term<Int> {
    set::size(set::difference(
        set::union(set::item(a), set::item(b)),
        set::item(b),
    ))
}

/// `set::intersect`, `intersectSet`: the size of `{a, b} & {b, c}`.
#[k::function(total, sort = Int, syntax = "intersect({a}, {b}, {c})")]
pub struct Intersect {
    pub a: Term<Int>,
    pub b: Term<Int>,
    pub c: Term<Int>,
}

#[k::equation]
fn intersect(k::term![Intersect(a, b, c)]: Term<Int>) -> Term<Int> {
    set::size(set::intersect(
        set::union(set::item(a), set::item(b)),
        set::union(set::item(b), set::item(c)),
    ))
}

/// `set::size` and `set::union`, `|Set`: the size of `{a} | {b}`.
#[k::function(total, sort = Int, syntax = "unionSize({a}, {b})")]
pub struct UnionSize {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn union_size(k::term![UnionSize(a, b)]: Term<Int>) -> Term<Int> {
    set::size(set::union(set::item(a), set::item(b)))
}

/// `set::is_subset`, `<=Set`: whether `{a} <= {b, c}`.
#[k::function(total, sort = Bool, syntax = "isSubset({a}, {b}, {c})")]
pub struct IsSubset {
    pub a: Term<Int>,
    pub b: Term<Int>,
    pub c: Term<Int>,
}

#[k::equation]
fn is_subset(k::term![IsSubset(a, b, c)]: Term<Bool>) -> Term<Bool> {
    set::is_subset(set::item(a), set::union(set::item(b), set::item(c)))
}

/// `set::contains`, `in`: whether `a` is in `{b, c}`.
#[k::function(total, sort = Bool, syntax = "setContains({a}, {b}, {c})")]
pub struct SetContains {
    pub a: Term<Int>,
    pub b: Term<Int>,
    pub c: Term<Int>,
}

#[k::equation]
fn set_contains(k::term![SetContains(a, b, c)]: Term<Bool>) -> Term<Bool> {
    set::contains(a, set::union(set::item(b), set::item(c)))
}

/// `set::to_list`, `Set2List`: the length of the list of `{a, b}`.
#[k::function(total, sort = Int, syntax = "toList({a}, {b})")]
pub struct ToList {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn to_list(k::term![ToList(a, b)]: Term<Int>) -> Term<Int> {
    list::size(set::to_list(set::union(set::item(a), set::item(b))))
}

/// `set::from_list`, `List2Set`: the size of the set of the list `[a, b]`.
#[k::function(total, sort = Int, syntax = "fromList({a}, {b})")]
pub struct FromList {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn from_list(k::term![FromList(a, b)]: Term<Int>) -> Term<Int> {
    set::size(set::from_list(list::concat(list::item(a), list::item(b))))
}

/// `list::contains`, `_inList_`: whether `a` is in the list `[b, c]`.
#[k::function(total, sort = Bool, syntax = "listContains({a}, {b}, {c})")]
pub struct ListContains {
    pub a: Term<Int>,
    pub b: Term<Int>,
    pub c: Term<Int>,
}

#[k::equation]
fn list_contains(k::term![ListContains(a, b, c)]: Term<Bool>) -> Term<Bool> {
    list::contains(a, list::concat(list::item(b), list::item(c)))
}
