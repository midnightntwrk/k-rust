//! The values of K's builtin tokens: the kind of a sort's domain values, read from its
//! declaration ([`DomainKind`]); which texts are values of a kind ([`validate_text`]); the one
//! canonical text of each value ([`canonical_text`]), for the integers, the machine integers and
//! the floating-point numbers of every format ([`canonical_float_text`]); the unquoting of
//! `String` and `Bytes` literals ([`string`]); and the value a token denotes ([`token_value`]).
//!
//! The backend builds every domain value with these, k-rust's program expansion compares tokens
//! by [`token_value`], and KRS compares the tokens of its builtin sorts by
//! [`prelude_token_value`]: one definition of a token's value, read without a definition, a
//! backend or a KORE parser. A sort is read through [`DomainSort`], by its KORE name.

pub mod float;
mod kind;
pub mod string;
mod text;
mod token;

pub use float::{
    FloatTextRefusal, MAX_FLOAT_CANONICAL_BITS, canonical_float_text,
    float_canonical_bits_estimate, is_float_syntax,
};
pub use kind::{
    BOOL_SORT, BYTES_SORT, DomainKind, DomainSort, FLOAT_SORT, INT_SORT, MINT_SORT, MIntWidth,
    STRING_SORT, mint_width, mint_width_digits,
};
#[cfg(any(test, feature = "measure"))]
pub use text::mint_text_parses;
pub use text::{
    DomainValueBound, InvalidDomainValueReason, MAX_INT_RESULT_BITS, TextRejection, canonical_text,
    validate_text,
};
pub use token::{
    TokenValue, prelude_hook, prelude_token_value, same_prelude_token, token_payload, token_value,
};
