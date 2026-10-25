//@ check-pass
//! Branching bodies of the function shorthand compile under a facade that is
//! not named `k`: an `if` chain, a `match` on a tuple of terms with literal
//! arms, a `match` on a parameter with guards and a catch-all, nested
//! branches, and an arm label.
use renamed_krs as facade;
use renamed_krs::builtin::{Bool, Int, Map, int, map};

renamed_krs::sorts! {
    Val;
}

#[facade::constructors(sort = Val, result = renamed_krs::KResult)]
#[facade::precedence((Integer, Flag))]
pub enum Value {
    #[facade::syntax("integer({ty}, {value})")]
    Integer { ty: Int, value: Int },
    #[facade::syntax("flag({set})")]
    Flag { set: Bool },
}

#[facade::function(total, internal)]
pub fn Sign(value: facade::Term<Int>) -> facade::Term<Int> {
    if int::lt(value, 0) { -1 } else { 1 }
}

#[facade::function(total, internal)]
pub fn StorageValue(storage: facade::Term<Map>, index: facade::Term<Int>) -> facade::Term<Int> {
    if map::in_keys(index, storage) {
        map::get(storage, index)
    } else {
        0
    }
}

#[facade::function(total, internal)]
pub fn SignedLess(left: facade::Term<Int>, right: facade::Term<Int>) -> facade::Term<Bool> {
    match (Sign(left), Sign(right)) {
        (1, 1) => int::lt(left, right),
        (1, -1) => false,
        (-1, 1) => true,
        (-1, -1) => int::lt(int::abs(right), int::abs(left)),
    }
}

#[facade::requires(int::ge(width, 0))]
#[facade::function(partial)]
fn Describe(value: facade::Term<Val>, width: facade::Term<Int>) -> facade::Term<Int> {
    match value {
        Value::Integer { ty: 32, value } if int::lt(value, 0) => 0,
        #[facade::label(describe_integer)]
        Value::Integer { value, .. } => match width {
            8 => value,
            _ => int::add(value, width),
        },
        Value::Flag { set } => if set { 1 } else { 2 },
        _ => -1,
    }
}

fn main() {}
