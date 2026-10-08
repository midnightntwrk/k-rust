//! Builtin BYTES operations: one function and one equation per operation.
//!
//! Programs write byte strings as K `Bytes` tokens such as `b"\x01\x02"`.
//! `Endianness` and `Signedness` are not program syntax, so the conversions
//! fix them in their equations.

use k::builtin::{Bool, Bytes, Int, KSequence, bytes};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Bytes, Int;
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

/// `bytes::empty` and `bytes::length`: the length of `.Bytes`.
#[k::function(total, sort = Int, syntax = "emptyLength()")]
pub struct EmptyLength {}

#[k::equation]
fn empty_length(k::term![EmptyLength()]: Term<Int>) -> Term<Int> {
    bytes::length(bytes::empty())
}

/// `bytes::length`.
#[k::function(total, sort = Int, syntax = "length({b})")]
pub struct Length {
    pub b: Term<Bytes>,
}

#[k::equation]
fn length(k::term![Length(b)]: Term<Int>) -> Term<Int> {
    bytes::length(b)
}

/// `bytes::get`.
#[k::function(partial, sort = Int, syntax = "get({b}, {i})")]
pub struct Get {
    pub b: Term<Bytes>,
    pub i: Term<Int>,
}

#[k::equation]
fn get(k::term![Get(b, i)]: Term<Int>) -> Term<Int> {
    bytes::get(b, i)
}

/// `bytes::update`.
#[k::function(partial, sort = Bytes, syntax = "update({b}, {i}, {v})")]
pub struct Update {
    pub b: Term<Bytes>,
    pub i: Term<Int>,
    pub v: Term<Int>,
}

#[k::equation]
fn update(k::term![Update(b, i, v)]: Term<Bytes>) -> Term<Bytes> {
    bytes::update(b, i, v)
}

/// `bytes::substr`.
#[k::function(partial, sort = Bytes, syntax = "substr({b}, {start}, {end})")]
pub struct Substr {
    pub b: Term<Bytes>,
    pub start: Term<Int>,
    pub end: Term<Int>,
}

#[k::equation]
fn substr(k::term![Substr(b, start, end)]: Term<Bytes>) -> Term<Bytes> {
    bytes::substr(b, start, end)
}

/// `bytes::pad_right`.
#[k::function(partial, sort = Bytes, syntax = "padRight({b}, {len}, {v})")]
pub struct PadRight {
    pub b: Term<Bytes>,
    pub len: Term<Int>,
    pub v: Term<Int>,
}

#[k::equation]
fn pad_right(k::term![PadRight(b, len, v)]: Term<Bytes>) -> Term<Bytes> {
    bytes::pad_right(b, len, v)
}

/// `bytes::pad_left`.
#[k::function(partial, sort = Bytes, syntax = "padLeft({b}, {len}, {v})")]
pub struct PadLeft {
    pub b: Term<Bytes>,
    pub len: Term<Int>,
    pub v: Term<Int>,
}

#[k::equation]
fn pad_left(k::term![PadLeft(b, len, v)]: Term<Bytes>) -> Term<Bytes> {
    bytes::pad_left(b, len, v)
}

/// `bytes::concat`, `+Bytes`.
#[k::function(total, sort = Bytes, syntax = "concat({a}, {b})")]
pub struct Concat {
    pub a: Term<Bytes>,
    pub b: Term<Bytes>,
}

#[k::equation]
fn concat(k::term![Concat(a, b)]: Term<Bytes>) -> Term<Bytes> {
    bytes::concat(a, b)
}

/// `bytes::reverse`.
#[k::function(total, sort = Bytes, syntax = "reverse({b})")]
pub struct Reverse {
    pub b: Term<Bytes>,
}

#[k::equation]
fn reverse(k::term![Reverse(b)]: Term<Bytes>) -> Term<Bytes> {
    bytes::reverse(b)
}

/// `bytes::replace_at`.
#[k::function(partial, sort = Bytes, syntax = "replaceAt({dest}, {i}, {src})")]
pub struct ReplaceAt {
    pub dest: Term<Bytes>,
    pub i: Term<Int>,
    pub src: Term<Bytes>,
}

#[k::equation]
fn replace_at(k::term![ReplaceAt(dest, i, src)]: Term<Bytes>) -> Term<Bytes> {
    bytes::replace_at(dest, i, src)
}

/// `bytes::from_int` with `bytes::big_endian`.
#[k::function(total, sort = Bytes, syntax = "fromIntBigEndian({len}, {i})")]
pub struct FromIntBigEndian {
    pub len: Term<Int>,
    pub i: Term<Int>,
}

#[k::equation]
fn from_int_big_endian(k::term![FromIntBigEndian(len, i)]: Term<Bytes>) -> Term<Bytes> {
    bytes::from_int(len, i, bytes::big_endian())
}

/// `bytes::from_int_no_len` with `bytes::little_endian` and `bytes::signed`.
#[k::function(total, sort = Bytes, syntax = "fromIntSigned({i})")]
pub struct FromIntSigned {
    pub i: Term<Int>,
}

#[k::equation]
fn from_int_signed(k::term![FromIntSigned(i)]: Term<Bytes>) -> Term<Bytes> {
    bytes::from_int_no_len(i, bytes::little_endian(), bytes::signed())
}

/// `bytes::to_int` with `bytes::little_endian` and `bytes::unsigned`.
#[k::function(total, sort = Int, syntax = "toIntUnsigned({b})")]
pub struct ToIntUnsigned {
    pub b: Term<Bytes>,
}

#[k::equation]
fn to_int_unsigned(k::term![ToIntUnsigned(b)]: Term<Int>) -> Term<Int> {
    bytes::to_int(b, bytes::little_endian(), bytes::unsigned())
}

/// `bytes::to_int` with `bytes::big_endian` and `bytes::signed`.
#[k::function(total, sort = Int, syntax = "toIntSigned({b})")]
pub struct ToIntSigned {
    pub b: Term<Bytes>,
}

#[k::equation]
fn to_int_signed(k::term![ToIntSigned(b)]: Term<Int>) -> Term<Int> {
    bytes::to_int(b, bytes::big_endian(), bytes::signed())
}
