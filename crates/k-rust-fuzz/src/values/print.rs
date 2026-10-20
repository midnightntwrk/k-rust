//! Values as K text and as KORE (ARCHITECTURE 2.3, 2.6). Owner: FZ-03 (builtin sorts); FZ-G6
//! adds data-sort printing.

use k_rust::kore::ast::Pattern as KorePattern;

use super::{Value, ValueSort};

/// Why a value cannot be printed as K text that parses back.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PrintError {
    /// The value's shape does not match the sort.
    SortMismatch,
    /// The sort has no K-text printer in this milestone (data sorts before G-6).
    Unsupported(String),
}

/// `value` as K text at `sort`: the text a span hole's literal is replaced with
/// (ARCHITECTURE 2.3) and the witness's K text (2.6). For builtin sorts it is the literal the
/// definition's lexical syntax reads (`-5` for a negative `Int`, a quoted and escaped string,
/// `b"…"` for bytes, `5p64` for `MInt{64}`); whether the program's grammar reads it back as the
/// intended value at the hole's position is FZ-02's round-trip check, not this function's.
///
/// # Errors
///
/// [`PrintError`] when the value cannot be printed.
pub(crate) fn print_k_text(value: &Value, sort: &ValueSort) -> Result<String, PrintError> {
    unimplemented!("FZ-03")
}

/// `value` as a KORE pattern of `sort` (a domain value `\dv{SortInt{}}("5")`, a collection
/// built from the collection's symbols, or a constructor application), not injected: the
/// expected term at a hole's position for the round-trip check (ARCHITECTURE 2.3), the
/// substitution of a KORE-template hole, and the witness's KORE (2.6).
///
/// # Errors
///
/// [`PrintError`] when the value's shape does not match the sort.
pub(crate) fn to_kore(value: &Value, sort: &ValueSort) -> Result<KorePattern, PrintError> {
    unimplemented!("FZ-03")
}
