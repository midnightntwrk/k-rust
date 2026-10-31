//! The value a token of a builtin sort denotes, read as k-rust reads it.
//!
//! A static clause's subject is matched against a program term by k-rust's program expansion,
//! which compares two tokens by the value they denote in the emitted definition
//! ([`k_rust_domain::token_value`]): `1.5` and `1.50`, `01` and `1` are one term there. The
//! static matcher that expands a clause's subject at compile time and the overlap check of two
//! clauses compare tokens by the same value, so that the subject KRS writes is matched by the
//! clause program expansion applies. KRS's builtin sorts are those of K's prelude, so the value
//! is the one the prelude's hook gives ([`prelude_token_value`]); a token of any other sort (a
//! `#[k::token]` sort, which carries no hook) denotes its text.

use k_rust_domain::{TokenValue, prelude_token_value};
use krs_ir_levels::IrSortRef;

/// The value the token `text` of `sort` denotes, when it denotes one other than its text.
fn value<D>(sort: &IrSortRef<D>, text: &str) -> Option<TokenValue> {
    match sort {
        IrSortRef::Builtin(builtin) => prelude_token_value(builtin.k_name(), text),
        IrSortRef::Declared(_) | IrSortRef::Cell(_) | IrSortRef::Parameter(_) => None,
    }
}

/// Whether the tokens `left` and `right` of `sort` denote one value: equal texts, or equal
/// values ([`value`]).
pub(crate) fn same_token<D>(sort: &IrSortRef<D>, left: &str, right: &str) -> bool {
    left == right
        || matches!(
            (value(sort, left), value(sort, right)),
            (Some(left), Some(right)) if left == right
        )
}

/// A text naming the value the token `text` of `sort` denotes and no other, by which two
/// tokens of `sort` are equal exactly when [`same_token`] holds of them: the value's key, or the
/// text itself, each marked apart. A key to compare by, not a token.
pub(crate) fn token_key<D>(sort: &IrSortRef<D>, text: &str) -> String {
    match value(sort, text) {
        Some(value) => format!("value:{}", value.key()),
        None => format!("text:{text}"),
    }
}
